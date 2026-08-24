
# -*- coding: utf-8 -*-
"""
td_from_round6_direct_New_IV.py

用法：python td_from_round6_direct_New_IV.py

功能：
(1) TD 段：使用 td_trunc_opt.py 打印前 5 轮（仅作对照）；
(2) SMT 段：不经 build_from_graph，直接从 Round-6 的四根线作为起点：
      u0^6 = R(x)
      u1^6 = 0s ⊕ x
      u2^6 = R(δ)
      u3^6 = R(x) ⊕ x ⊕ R(δ)
    然后用 smt_model_distinguish_new_IV 的 R/XOR 原子节点逐轮推出 Round-7..11；
    bot 传播规则：
      - R：bot_out = bot_in OR bot_internal
      - XOR（no-collision）：bot_out = Abot OR Bbot
    打印时：若 bot=true 则显示 "⊥"，否则按掩码法解码为 0s/R(x)/x/R(δ)/δ 的 ⊕ 组合。
"""

# ---------- (1) TD 段：前 5 轮 ----------
from td_trunc_opt import TDEngine as TD_Engine, Val as TD_Val, Sym as TD_Sym

def run_td_first5_and_print():
    eng = TD_Engine()
    u0 = TD_Val(TD_Sym.A)
    u1 = TD_Val(TD_Sym.AS)      # a⊕s
    u2 = TD_Val(TD_Sym.ZERO)    # 0
    u3 = TD_Val(TD_Sym.A)

    rounds = []
    for i in range(5):
        u0_new = eng.R(u3)            # u0^{i+1}
        u1_new = eng.xor2(u3, u0)     # u1^{i+1}
        u2_new = eng.xor2(u1, u3)     # u2^{i+1}
        u3_new = u2                   # u3^{i+1}
        rounds.append((str(u0_new), str(u1_new), str(u2_new), str(u3_new)))
        u0, u1, u2, u3 = u0_new, u1_new, u2_new, u3_new

    print("=== TD 前 5 轮（td_trunc_opt） ===")
    for i,(a,b,c,d) in enumerate(rounds, start=1):
        print(f"Round {i}:  u_0={a}, u_1={b}, u_2={c}, u_3={d}")
    return rounds[-1]

# ---------- (2) SMT 段：从 Round-6 种子直接推导 ----------
import smt_model_distinguish_new_IV as SMT
from cvc5 import Kind

def run_smt_from_round6_and_print():
    s = SMT.mk_solver()
    syms = SMT.build_symbols_4_1(s)

    ZERO    = syms["ZERO"]
    DELTA   = syms["DELTA"]
    R_DELTA = syms["R_DELTA"]
    X       = syms["X"]
    R_X     = syms["R_X"]
    ZERO_S  = syms["ZERO_S"]

    def OR(a,b): return s.mkTerm(Kind.BITVECTOR_OR, a, b)

    # Round-6 作为起点（值常量 & bot=false）
    u0 = s.mkConst(R_X.getSort(), "u0_r6"); s.assertFormula(SMT.Eq(s, u0, R_X))                         # R(x)
    u1 = s.mkConst(R_X.getSort(), "u1_r6"); s.assertFormula(SMT.Eq(s, u1, OR(ZERO_S, X)))               # 0s ⊕ x
    u2 = s.mkConst(R_X.getSort(), "u2_r6"); s.assertFormula(SMT.Eq(s, u2, R_DELTA))                     # R(δ)
    u3 = s.mkConst(R_X.getSort(), "u3_r6"); s.assertFormula(SMT.Eq(s, u3, OR(OR(R_X, X), R_DELTA)))     # R(x) ⊕ x ⊕ R(δ)

    b0 = s.mkBoolean(False)  # bot(u0^6)
    b1 = s.mkBoolean(False)  # bot(u1^6)
    b2 = s.mkBoolean(False)  # bot(u2^6)
    b3 = s.mkBoolean(False)  # bot(u3^6)

    rounds_terms = [(u0,u1,u2,u3)]
    rounds_bots  = [(b0,b1,b2,b3)]

    # 原子步骤封装
    def R_step(x_term, in_bot, name):
        out, s_i, mix_i, bot_internal = SMT.add_R_node(s, syms, x_term, name=name, monotone_guard=True)
        bot_eff = s.mkTerm(Kind.OR, in_bot, bot_internal)
        return out, bot_eff

    def XOR_step(a_term, b_term, a_bot, b_bot, name):
        out, xflag, bot_internal = SMT.add_XOR_node_no_collision(s, a_term, b_term, name=name)
        # no-collision：只吸收输入的 ⊥
        s.assertFormula(SMT.Not(s, xflag))
        bot_eff = s.mkTerm(Kind.OR, a_bot, b_bot)
        return out, bot_eff

    # Round-7..11
    u0c, u1c, u2c, u3c = u0, u1, u2, u3
    b0c, b1c, b2c, b3c = b0, b1, b2, b3
    for r in range(7, 12):
        # u0^{r} = R(u3^{r-1})
        u0n, b0n = R_step(u3c, b3c, f"R_r{r}_from_u3")
        # u1^{r} = u3^{r-1} ⊕ u0^{r-1}
        u1n, b1n = XOR_step(u3c, u0c, b3c, b0c, f"X1_r{r}_u3_xor_u0")
        # u2^{r} = u1^{r-1} ⊕ u3^{r-1}
        u2n, b2n = XOR_step(u1c, u3c, b1c, b3c, f"X2_r{r}_u1_xor_u3")
        # u3^{r} = u2^{r-1}
        u3n, b3n = u2c, b2c

        rounds_terms.append((u0n,u1n,u2n,u3n))
        rounds_bots.append((b0n,b1n,b2n,b3n))

        u0c,u1c,u2c,u3c = u0n,u1n,u2n,u3n
        b0c,b1c,b2c,b3c = b0n,b1n,b2n,b3n

    # 求解并打印 Round 6..11
    res = s.checkSat()
    print("\n[SMT checkSat] =", res)
    if str(res).lower() not in ("sat","unknown"):
        print("UNSAT：请检查 Round-6 种子是否与约束冲突。")
        return

    def bits_to_label(term):
        """掩码解码（独立于位序）"""
        bv = s.getValue(term)
        def has(mask):
            anded = s.getValue(s.mkTerm(Kind.BITVECTOR_AND, bv, mask))
            return anded == s.getValue(mask)
        parts = []
        if has(ZERO_S):  parts.append("0s")
        if has(R_X):     parts.append("R(x)")
        if has(X):       parts.append("x")
        if has(R_DELTA): parts.append("R(δ)")
        if has(DELTA):   parts.append("δ")
        return " ⊕ ".join(parts) if parts else "0"

    print("=== SMT 从 Round 6（直接种子）推到 Round 11 ===")
    for idx, (tup, btp) in enumerate(zip(rounds_terms, rounds_bots), start=6):
        raw = [str(s.getValue(t)) for t in tup]
        print(f"[DEBUG] Round {idx} raw BV:", raw)
        a,b,c,d = tup
        ba,bb,bc,bd = btp
        A = "⊥" if s.getValue(ba).getBooleanValue() else bits_to_label(a)
        B = "⊥" if s.getValue(bb).getBooleanValue() else bits_to_label(b)
        C = "⊥" if s.getValue(bc).getBooleanValue() else bits_to_label(c)
        D = "⊥" if s.getValue(bd).getBooleanValue() else bits_to_label(d)
        print(f"Round {idx}:  u_0={A}, u_1={B}, u_2={C}, u_3={D}")

def main():
    run_td_first5_and_print()
    run_smt_from_round6_and_print()

if __name__ == "__main__":
    main()

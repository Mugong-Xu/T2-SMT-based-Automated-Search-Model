
# -*- coding: utf-8 -*-
"""
td_from_round6_benchmark_New_IV_min.py

Runs the "from Round-6 seeds to Round-11" SMT derivation 100 times,
and prints ONLY:
  - The final (run 100) Round 11 symbols (one line)
  - The average execution time per run

Dependencies:
  - smt_model_distinguish_new_IV.py
  - cvc5  (pip install cvc5)
"""

import time
from cvc5 import Kind
import smt_model_distinguish_new_IV as SMT

def run_once():
    s = SMT.mk_solver()
    syms = SMT.build_symbols_4_1(s)

    ZERO    = syms["ZERO"]
    DELTA   = syms["DELTA"]
    R_DELTA = syms["R_DELTA"]
    X       = syms["X"]
    R_X     = syms["R_X"]
    ZERO_S  = syms["ZERO_S"]

    def OR(a,b): return s.mkTerm(Kind.BITVECTOR_OR, a, b)

    # Round-6 seeds
    u0 = s.mkConst(R_X.getSort(), "u0_r6"); s.assertFormula(SMT.Eq(s, u0, R_X))                         # R(x)
    u1 = s.mkConst(R_X.getSort(), "u1_r6"); s.assertFormula(SMT.Eq(s, u1, OR(ZERO_S, X)))               # 0s ⊕ x
    u2 = s.mkConst(R_X.getSort(), "u2_r6"); s.assertFormula(SMT.Eq(s, u2, R_DELTA))                     # R(δ)
    u3 = s.mkConst(R_X.getSort(), "u3_r6"); s.assertFormula(SMT.Eq(s, u3, OR(OR(R_X, X), R_DELTA)))     # R(x) ⊕ x ⊕ R(δ)

    b0 = s.mkBoolean(False)
    b1 = s.mkBoolean(False)
    b2 = s.mkBoolean(False)
    b3 = s.mkBoolean(False)

    def R_step(x_term, in_bot, name):
        out, s_i, mix_i, bot_internal = SMT.add_R_node(s, syms, x_term, name=name, monotone_guard=True)
        bot_eff = s.mkTerm(Kind.OR, in_bot, bot_internal)
        return out, bot_eff

    def XOR_step(a_term, b_term, a_bot, b_bot, name):
        out, xflag, bot_internal = SMT.add_XOR_node_no_collision(s, a_term, b_term, name=name)
        s.assertFormula(SMT.Not(s, xflag))  # no-collision
        bot_eff = s.mkTerm(Kind.OR, a_bot, b_bot)  # absorb input ⊥
        return out, bot_eff

    # Derive rounds 7..11
    u0c, u1c, u2c, u3c = u0, u1, u2, u3
    b0c, b1c, b2c, b3c = b0, b1, b2, b3
    for r in range(7, 12):
        u0n, b0n = R_step(u3c, b3c, f"R_r{r}_from_u3")
        u1n, b1n = XOR_step(u3c, u0c, b3c, b0c, f"X1_r{r}_u3_xor_u0")
        u2n, b2n = XOR_step(u1c, u3c, b1c, b3c, f"X2_r{r}_u1_xor_u3")
        u3n, b3n = u2c, b2c
        u0c, u1c, u2c, u3c = u0n, u1n, u2n, u3n
        b0c, b1c, b2c, b3c = b0n, b1n, b2n, b3n

    res = s.checkSat()
    if str(res).lower() not in ("sat", "unknown"):
        return ("UNSAT", "UNSAT", "UNSAT", "UNSAT")

    def label(term, bot_flag):
        if s.getValue(bot_flag).getBooleanValue():
            return "⊥"
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

    return (label(u0c, b0c), label(u1c, b1c), label(u2c, b2c), label(u3c, b3c))

def main():
    N = 100
    totals = 0.0
    last = None
    for _ in range(N):
        t0 = time.perf_counter()
        last = run_once()
        totals += time.perf_counter() - t0
    avg = totals / N
    # Print only the final run's Round 11 symbols and the average time
    u0,u1,u2,u3 = last
    print(f"Final (run {N}) Round 11:  u0={u0}, u1={u1}, u2={u2}, u3={u3}")
    print(f"Average time per run: {avg*1000:.3f} ms over {N} runs")

if __name__ == "__main__":
    main()

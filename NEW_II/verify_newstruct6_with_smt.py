# verify_newstruct6_with_smt.py
# 仅打印最后一轮 Round 6 的符号/⊥，其余过程不输出；保留分段耗时统计。

import time
from cvc5 import Kind
from td_trunc import TDEngine, Z, A, S, Val, Sym, copy_val
from smt_model_distinguish import build_from_graph

# 1) 截断域上模拟 6 轮（新结构）
def simulate_new_struct_trunc(rounds=6, init=(Z, Z, A, S)):
    eng = TDEngine()
    u0,u1,u2,u3 = init
    hist = [(u0,u1,u2,u3)]
    for _ in range(rounds):
        Ru0 = eng.R(u0)
        u3n = copy_val(u0)
        u0n = eng.xor2(Ru0, u1)
        u1n = eng.xor2(Ru0, u2)
        u2n = copy_val(u3)
        u0,u1,u2,u3 = u0n,u1n,u2n,u3n
        hist.append((u0,u1,u2,u3))
    return hist

# 2) 代换表
def td_to_smt_mask(v: Val) -> int | None:
    if v.sym == Sym.ZERO:    return 0b00000
    if v.sym == Sym.ZERO_S:  return 0b10000
    if v.sym == Sym.S:       return 0b00100
    if v.sym == Sym.AS:      return 0b00101
    if v.sym == Sym.A:       return (0b10001 if getattr(v, "a_flag", 0)==1 else 0b00001)
    if v.sym == Sym.STAR:    return None
    return None

# 3) 安全锚点
def is_pure_for_R(v: Val) -> bool:
    if v.sym in (Sym.ZERO, Sym.ZERO_S, Sym.S): return True
    if v.sym == Sym.A and getattr(v, "a_flag", 0)==0: return True
    return False

def find_safe_anchor_round(hist):
    for r in range(5, -1, -1):
        u0,u1,u2,u3 = hist[r]
        if all(v.sym != Sym.STAR for v in (u0,u1,u2,u3)) and is_pure_for_R(u0):
            return r
    return None

# 4) 规格：6轮“新结构”
def build_spec_6round_newstruct():
    nodes = []
    def ref(i,b): return f"u0_{b}" if i==0 else f"U{b}_{i}"
    ROUNDS=6
    for i in range(ROUNDS):
        nodes.append({"op":"R",    "name":f"R0_{i}",   "in": ref(i,0)})
        nodes.append({"op":"XOR",  "name":f"U0_{i+1}", "a": f"R0_{i}", "b": ref(i,1)})
        nodes.append({"op":"XOR",  "name":f"U1_{i+1}", "a": f"R0_{i}", "b": ref(i,2)})
        nodes.append({"op":"SPLIT","name":f"U2_{i+1}", "in": ref(i,3), "k":1})
        nodes.append({"op":"SPLIT","name":f"U3_{i+1}", "in": ref(i,0), "k":1})
    tails=[f"U0_{ROUNDS}", f"U1_{ROUNDS}", f"U2_{ROUNDS}", f"U3_{ROUNDS}"]
    return {
        "n_inputs":4,
        "allow_weak":False,
        "sum1":True,
        "monotone_guard":True,
        "collisions":True,
        "nodes":nodes,
        "tails":tails,
    }

# 5) 打印工具（只用于 Round 6；支持 ⊥）
def fmt(mask:int) -> str:
    if mask == 0b11111:  # BOT 显式码
        return "⊥"
    parts=[]
    if mask & 0b00001: parts.append("δ")
    if mask & 0b00010: parts.append("R(δ)")
    if mask & 0b00100: parts.append("x")
    if mask & 0b01000: parts.append("R(x)")
    if mask & 0b10000: parts.append("0s")
    return f"#b{mask:05b}  => {( ' ⊕ '.join(parts) or '0')}"

def dump_round6(s, env):
    print("\n== Round 6（SMT）取值/⊥ ==")
    for name in ("U0_6","U1_6","U2_6","U3_6"):
        is_bot = s.getValue(env["botmap"][name][0])
        if str(is_bot) == "true":
            print(f"  {name}: ⊥")
            continue
        t = env["outmap"][name][0]
        iv = int(str(s.getValue(t))[2:], 2)
        print(f"  {name}: {fmt(iv)}")

# 6) 主流程（含计时）
def main():
    T0 = time.perf_counter()

    # A) 截断轨迹 & 锚点
    t_sim0 = time.perf_counter()
    hist = simulate_new_struct_trunc(rounds=6, init=(Z, Z, A, S))
    t_sim1 = time.perf_counter()
    t_anchor0 = time.perf_counter()
    anchor = find_safe_anchor_round(hist)
    t_anchor1 = time.perf_counter()

    if anchor is None:
        print("check-sat: unknown")
        print("\n包含量子区分器？ 否（未找到安全锚点）")
        T1 = time.perf_counter()
        print("\n== 计时统计 ==")
        print(f"td_trunc 模拟: {t_sim1 - t_sim0:.6f} s")
        print(f"锚点选择   : {t_anchor1 - t_anchor0:.6f} s")
        print(f"构图        : {0.0:.6f} s")
        print(f"锚点断言   : {0.0:.6f} s")
        print(f"求解 (SMT) : {0.0:.6f} s")
        print(f"总耗时     : {T1 - T0:.6f} s")
        return

    # B) 构图
    t_build0 = time.perf_counter()
    s, env = build_from_graph(build_spec_6round_newstruct())
    mkbv = lambda x: s.mkBitVector(5, x)
    t_build1 = time.perf_counter()

    # C) 在锚点轮把 4 分支钉成 5-bit
    def nodename(r,w): return (f"u0_{w}" if r==0 else f"U{w}_{r}")
    t_pin0 = time.perf_counter()
    for w in range(4):
        v = hist[anchor][w]
        m = td_to_smt_mask(v)
        if m is None:  # 安全锚点下不应发生
            continue
        name = nodename(anchor,w)
        s.assertFormula(s.mkTerm(Kind.EQUAL, env["outmap"][name][0], mkbv(m)))
    t_pin1 = time.perf_counter()

    # D) 求解
    t_sat0 = time.perf_counter()
    res = s.checkSat()
    t_sat1 = time.perf_counter()

    print("check-sat:", res)
    print("\n包含量子区分器？", "是" if str(res)=="sat" else "否")

    # 只打印 Round 6
    if str(res) == "sat":
        dump_round6(s, env)

    T1 = time.perf_counter()

    # E) 计时统计
    print("\n== 计时统计 ==")
    print(f"td_trunc 模拟: {t_sim1 - t_sim0:.6f} s")
    print(f"锚点选择   : {t_anchor1 - t_anchor0:.6f} s")
    print(f"构图        : {t_build1 - t_build0:.6f} s")
    print(f"锚点断言   : {t_pin1 - t_pin0:.6f} s")
    print(f"求解 (SMT) : {t_sat1 - t_sat0:.6f} s")
    print(f"总耗时     : {T1 - T0:.6f} s")

if __name__ == "__main__":
    main()

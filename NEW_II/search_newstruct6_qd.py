# search_newstruct6_qd.py  —— 只打印最后一轮，分段统计耗时（含单独“构图时间”）

import time
from cvc5 import Kind
from smt_model_distinguish import build_from_graph  # §4 模型（R(3)-(7)、XOR P2-4 等）

# ===== 6轮“新结构”规格 =====
def build_spec_6round_newstruct():
    nodes = []
    def ref(i, b):
        return f"u0_{b}" if i == 0 else f"U{b}_{i}"
    ROUNDS = 6
    for i in range(ROUNDS):
        nodes.append({"op":"R",    "name":f"R0_{i}",   "in": ref(i,0)})           # R(u0^i)
        nodes.append({"op":"XOR",  "name":f"U0_{i+1}", "a": f"R0_{i}", "b": ref(i,1)})  # u0^{i+1}
        nodes.append({"op":"XOR",  "name":f"U1_{i+1}", "a": f"R0_{i}", "b": ref(i,2)})  # u1^{i+1}
        nodes.append({"op":"SPLIT","name":f"U2_{i+1}", "in": ref(i,3), "k":1})         # u2^{i+1}=u3^i
        nodes.append({"op":"SPLIT","name":f"U3_{i+1}", "in": ref(i,0), "k":1})         # u3^{i+1}=u0^i
    tails = [f"U0_{ROUNDS}", f"U1_{ROUNDS}", f"U2_{ROUNDS}", f"U3_{ROUNDS}"]
    return {
        "n_inputs": 4,
        "allow_weak": False,
        "sum1": True,
        "monotone_guard": True,
        "collisions": True,
        "nodes": nodes,
        "tails": tails,
    }

# ===== 打印工具（仅 Round 6；支持 ⊥） =====
def fmt_mask(mask: int) -> str:
    if mask == 0b11111:  # 若模型用 #b11111 表示 ⊥
        return "⊥"
    parts = []
    if mask & 0b00001: parts.append("δ")
    if mask & 0b00010: parts.append("R(δ)")
    if mask & 0b00100: parts.append("x")
    if mask & 0b01000: parts.append("R(x)")
    if mask & 0b10000: parts.append("0s")
    return f"#b{mask:05b}  => " + (" ⊕ ".join(parts) if parts else "0")

def dump_round6(s, env):
    print("\n== Round 6（SMT）取值/⊥ ==")
    for name in ("U0_6","U1_6","U2_6","U3_6"):
        # 先看 botmap（⊥）
        is_bot = s.getValue(env["botmap"][name][0])
        if str(is_bot) == "true":
            print(f"  {name}: ⊥")
            continue
        t = env["outmap"][name][0]
        iv = int(str(s.getValue(t))[2:], 2)
        print(f"  {name}: {fmt_mask(iv)}")

# ===== 主流程 =====
def main():
    T0 = time.perf_counter()

    # 1) 构图（单独计时）
    t_build0 = time.perf_counter()
    spec = build_spec_6round_newstruct()
    s, env = build_from_graph(spec)
    t_build1 = time.perf_counter()

    # 2) 绑定 Round0 初值：u0=0, u1=0, u2=δ, u3=x（单独计时）
    t_assert0 = time.perf_counter()
    mkbv = lambda x: s.mkBitVector(5, x)
    inputs = env["inputs"]
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[0], mkbv(0b00000)))  # u0^0 = 0
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[1], mkbv(0b00000)))  # u1^0 = 0
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[2], mkbv(0b00001)))  # u2^0 = δ
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[3], mkbv(0b00100)))  # u3^0 = x
    t_assert1 = time.perf_counter()

    # 3) 求解（单独计时）
    t_solve0 = time.perf_counter()
    res = s.checkSat()
    t_solve1 = time.perf_counter()

    print("check-sat:", res)
    print("\n包含量子区分器？", "是" if str(res) == "sat" else "否")

    # 4) 只打印 Round 6（单独计时）
    t_dump0 = time.perf_counter()
    if str(res) == "sat":
        dump_round6(s, env)
    t_dump1 = time.perf_counter()

    T1 = time.perf_counter()

    # 5) 计时统计
    print("\n== 计时统计 ==")
    print(f"构图        : {t_build1 - t_build0:.6f} s")
    print(f"初值断言   : {t_assert1 - t_assert0:.6f} s")
    print(f"求解 (SMT) : {t_solve1 - t_solve0:.6f} s")
    print(f"取值+打印  : {t_dump1 - t_dump0:.6f} s")
    print(f"总耗时     : {T1 - T0:.6f} s")

if __name__ == "__main__":
    main()

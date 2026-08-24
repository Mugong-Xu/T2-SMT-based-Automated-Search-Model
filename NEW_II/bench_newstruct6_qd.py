# bench_newstruct6_qd.py
# 运行 100 次：构图/初值断言/求解 分段计时并输出平均值（只打印统计，不打印符号）

import time
import gc
from statistics import mean
from cvc5 import Kind
from smt_model_distinguish import build_from_graph  # 你的 §4 模型

REPEAT = 100  # 次数

def build_spec_6round_newstruct():
    nodes = []
    def ref(i, b):  # b: 0..3 分别代表 u0,u1,u2,u3
        return f"u0_{b}" if i == 0 else f"U{b}_{i}"
    ROUNDS = 6
    for i in range(ROUNDS):
        nodes.append({"op":"R",    "name":f"R0_{i}",   "in": ref(i,0)})
        nodes.append({"op":"XOR",  "name":f"U0_{i+1}", "a": f"R0_{i}", "b": ref(i,1)})
        nodes.append({"op":"XOR",  "name":f"U1_{i+1}", "a": f"R0_{i}", "b": ref(i,2)})
        nodes.append({"op":"SPLIT","name":f"U2_{i+1}", "in": ref(i,3), "k":1})
        nodes.append({"op":"SPLIT","name":f"U3_{i+1}", "in": ref(i,0), "k":1})
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

def run_once():
    t0 = time.perf_counter()
    spec = build_spec_6round_newstruct()
    s, env = build_from_graph(spec)
    t1 = time.perf_counter()

    # Round0 初值：u0=0, u1=0, u2=δ, u3=x
    mkbv = lambda x: s.mkBitVector(5, x)
    inputs = env["inputs"]
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[0], mkbv(0b00000)))
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[1], mkbv(0b00000)))
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[2], mkbv(0b00001)))
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[3], mkbv(0b00100)))
    t2 = time.perf_counter()

    res = s.checkSat()
    t3 = time.perf_counter()

    return {
        "build": t1 - t0,
        "assert": t2 - t1,
        "solve": t3 - t2,
        "total": t3 - t0,
        "sat": (str(res) == "sat"),
    }

def main():
    builds, asserts, solves, totals = [], [], [], []
    sat_count = 0

    # 可选：预热 3 次（不计入统计），减少一次性初始化抖动
    for _ in range(3):
        _ = run_once()
        gc.collect()

    for _ in range(REPEAT):
        r = run_once()
        builds.append(r["build"])
        asserts.append(r["assert"])
        solves.append(r["solve"])
        totals.append(r["total"])
        sat_count += int(r["sat"])
        gc.collect()

    print(f"重复次数: {REPEAT}")
    print(f"SAT 次数: {sat_count}/{REPEAT}")
    print("\n== 平均耗时（秒）==")
    print(f"构图        : {mean(builds):.6f}")
    print(f"初值断言   : {mean(asserts):.6f}")
    print(f"求解 (SMT) : {mean(solves):.6f}")
    print(f"总耗时     : {mean(totals):.6f}")

if __name__ == "__main__":
    main()

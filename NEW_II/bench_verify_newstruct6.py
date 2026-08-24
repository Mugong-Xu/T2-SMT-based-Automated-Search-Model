# bench_verify_newstruct6.py
# 执行 100 次：截断→选锚点→构图→锚点断言→求解，统计平均耗时与统计计数

import time
import gc
from statistics import mean
from cvc5 import Kind
from td_trunc import TDEngine, Z, A, S, Val, Sym, copy_val
from smt_model_distinguish import build_from_graph

REPEAT = 100  # 运行次数（可改）

# ===== 与 verify_newstruct6_with_smt.py 一致的流程函数 =====

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

def td_to_smt_mask(v: Val) -> int | None:
    if v.sym == Sym.ZERO:    return 0b00000
    if v.sym == Sym.ZERO_S:  return 0b10000
    if v.sym == Sym.S:       return 0b00100
    if v.sym == Sym.AS:      return 0b00101
    if v.sym == Sym.A:       return (0b10001 if getattr(v, "a_flag", 0)==1 else 0b00001)
    if v.sym == Sym.STAR:    return None
    return None

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

def build_spec_6round_newstruct():
    nodes = []
    def ref(i,b): return f"u0_{b}" if i==0 else f"U{b}_{i}"
    ROUNDS = 6
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

def run_once():
    # A) 截断 & 锚点
    t_sim0 = time.perf_counter()
    hist = simulate_new_struct_trunc(rounds=6, init=(Z, Z, A, S))
    t_sim1 = time.perf_counter()
    t_anchor0 = time.perf_counter()
    anchor = find_safe_anchor_round(hist)
    t_anchor1 = time.perf_counter()

    if anchor is None:
        # 没有锚点：后续时间记 0
        return {
            "sim": t_sim1 - t_sim0,
            "anchor": t_anchor1 - t_anchor0,
            "build": 0.0, "pin": 0.0, "solve": 0.0, "total": (t_anchor1 - t_sim0),
            "anchor_ok": False, "sat": False
        }

    # B) 构图
    t_build0 = time.perf_counter()
    s, env = build_from_graph(build_spec_6round_newstruct())
    mkbv = lambda x: s.mkBitVector(5, x)
    t_build1 = time.perf_counter()

    # C) 在锚点轮把 4 分支钉 5-bit
    def nodename(r,w): return (f"u0_{w}" if r==0 else f"U{w}_{r}")
    t_pin0 = time.perf_counter()
    for w in range(4):
        v = hist[anchor][w]
        m = td_to_smt_mask(v)
        if m is None:  # 按“安全锚点”不应发生
            continue
        name = nodename(anchor,w)
        s.assertFormula(s.mkTerm(Kind.EQUAL, env["outmap"][name][0], mkbv(m)))
    t_pin1 = time.perf_counter()

    # D) 求解
    t_solve0 = time.perf_counter()
    res = s.checkSat()
    t_solve1 = time.perf_counter()

    return {
        "sim": t_sim1 - t_sim0,
        "anchor": t_anchor1 - t_anchor0,
        "build": t_build1 - t_build0,
        "pin": t_pin1 - t_pin0,
        "solve": t_solve1 - t_solve0,
        "total": (t_solve1 - t_sim0),
        "anchor_ok": True,
        "sat": (str(res) == "sat"),
    }

def main():
    sims, anchors, builds, pins, solves, totals = [], [], [], [], [], []
    anchor_ok_cnt = 0
    sat_cnt = 0

    # 预热（不计入统计）
    for _ in range(3):
        _ = run_once()
        gc.collect()

    # 正式测量
    for _ in range(REPEAT):
        r = run_once()
        sims.append(r["sim"]); anchors.append(r["anchor"])
        builds.append(r["build"]); pins.append(r["pin"])
        solves.append(r["solve"]); totals.append(r["total"])
        anchor_ok_cnt += int(r["anchor_ok"]); sat_cnt += int(r["sat"])
        gc.collect()

    print(f"重复次数: {REPEAT}")
    print(f"找到安全锚点: {anchor_ok_cnt}/{REPEAT}")
    print(f"SAT 次数   : {sat_cnt}/{REPEAT}")
    print("\n== 平均耗时（秒）==")
    print(f"td_trunc 模拟: {mean(sims):.6f}")
    print(f"锚点选择   : {mean(anchors):.6f}")
    print(f"构图        : {mean(builds):.6f}")
    print(f"锚点断言   : {mean(pins):.6f}")
    print(f"求解 (SMT) : {mean(solves):.6f}")
    print(f"总耗时     : {mean(totals):.6f}")

if __name__ == "__main__":
    main()

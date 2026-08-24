#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
td_then_smt_Type1GFS_full_15r.py

流程：
  1) TD 域：从 (s, a, 0, 0) 开始，按 Type‑1 GFS（u0'=u3, u1'=R(u3)⊕u0, u2'=u1, u3'=u2）
     计算 Round 0..5，并打印一次 TD 结果（仅作参考）。
  2) SMT 域：忽略 TD→SMT 具体映射，直接把 Round‑5 的 SMT 种子固定为：
        u0^5 = 0 (#b00000)
        u1^5 = x (#b00100)
        u2^5 = δ ⊕ R(x) (#b01001)
        u3^5 = R(δ) (#b00010)
     然后用放宽模型（smt_model_distinguish_relaxed.py）继续 10 轮（到 Round‑15）。
  3) 性能：循环执行 100 次，只打印 [check-sat(last)]、Round‑15 符号（最后一次）、平均耗时。

说明：之所以强制 Round‑5 种子，是为了“避开 initial constraints 干扰”且与你指定的起点一致。
"""

import os, importlib.util, time
from typing import List, Tuple
from cvc5 import Kind

def _load(name, filename):
    spec = importlib.util.spec_from_file_location(name, filename)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)  # type: ignore
    return mod

BASE = os.path.dirname(__file__)
TD_PATH   = os.path.join(BASE, "td_trunc.py")
RELAX_PATH= os.path.join(BASE, "smt_model_distinguish_relaxed.py")

td  = _load("td_trunc", TD_PATH)
SMT = _load("smt_model_distinguish_relaxed", RELAX_PATH)

# ---------- TD: 0..5 轮 ----------
def td_to_str(v: "td.Val") -> str:
    for f in ("to_str", "toString"):
        if hasattr(v, f):
            try:
                s = getattr(v, f)()
                if isinstance(s, str):
                    return s
            except Exception:
                pass
    return str(v)

def td_run_5_rounds(u0, u1, u2, u3) -> List[Tuple["td.Val","td.Val","td.Val","td.Val"]]:
    eng = td.TDEngine()
    hist = [(u0, u1, u2, u3)]
    for _ in range(5):
        cur = hist[-1]
        Ru3 = eng.R(cur[3])
        nxt0 = td.copy_val(cur[3])            # u0' = u3
        nxt1 = eng.xor2(Ru3, cur[0])          # u1' = R(u3) ⊕ u0
        nxt2 = td.copy_val(cur[1])            # u2' = u1
        nxt3 = td.copy_val(cur[2])            # u3' = u2
        hist.append((nxt0, nxt1, nxt2, nxt3))
    return hist  # Round 0..5

# ---------- SMT: 从 Round‑5 固定种子继续 10 轮 ----------
def bits_to_label_5(bv: str) -> str:
    s = str(bv).strip()
    if not s.startswith("#b"): return s
    bits = s[2:].zfill(5)[-5:]
    v = int(bits, 2)
    parts = []
    if v & 0b00001: parts.append("δ")
    if v & 0b00010: parts.append("R(δ)")
    if v & 0b00100: parts.append("x")
    if v & 0b01000: parts.append("R(x)")
    if v & 0b10000: parts.append("0s")
    return " ⊕ ".join(parts) if parts else "0"

def build_type1gfs_10r_from_r5_relaxed():
    nodes = []
    rounds = [{f"u{k}": f"u0_{k}" for k in range(4)}]  # Round‑5 作为输入 u0_0..u0_3
    for i in range(10):
        cur = rounds[-1]
        R3 = f"R3_{i}"
        nodes.append({"op":"R", "name":R3, "in":cur["u3"]})
        X1 = f"X1_{i}"
        nodes.append({"op":"XOR", "name":X1, "a":R3, "b":cur["u0"]})
        rounds.append({
            "u0": cur["u3"],
            "u1": X1,
            "u2": cur["u1"],
            "u3": cur["u2"],
        })
    tails = [rounds[10][f"u{k}"] for k in range(4)]
    spec = dict(n_inputs=4, nodes=nodes, tails=tails)  # relaxed 引擎无需额外标志
    return spec, rounds

def run_smt_once_and_get_round15():
    spec, rounds = build_type1gfs_10r_from_r5_relaxed()
    s, env = SMT.build_from_graph(spec)

    # 固定 Round‑5 的 SMT 种子：0, x, δ⊕R(x), R(δ)
    mkbv = lambda x: s.mkBitVector(5, x)
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][0], mkbv(0)))
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][1], mkbv(4)))
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][2], mkbv(9)))
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][3], mkbv(2)))

    res = s.checkSat()
    if str(res).lower() != "sat":
        return "UNSAT/UNKNOWN", None

    # Round‑15 输出
    names = [rounds[10][f"u{k}"] for k in range(4)]
    labels = []
    for k, nm in enumerate(names):
        val = s.getValue(env["outmap"][nm][0])
        labels.append(bits_to_label_5(str(val)))
    return "SAT", labels

def main():
    # 先跑一次 TD 0..5 轮（只打印一次，作为参考）
    td_hist = td_run_5_rounds(td.S, td.A, td.Z, td.Z)
    print("== TD 0..5 轮 ==")
    for r in range(6):
        u0,u1,u2,u3 = td_hist[r]
        print(f"Round {r} : u0={td_to_str(u0)}, u1={td_to_str(u1)}, u2={td_to_str(u2)}, u3={td_to_str(u3)}")

    # SMT 基准：100 次
    for _ in range(3):  # 预热
        run_smt_once_and_get_round15()

    N = 100
    total = 0.0
    last_status, last_labels = None, None
    for _ in range(N):
        t0 = time.perf_counter()
        status, labels = run_smt_once_and_get_round15()
        total += time.perf_counter() - t0
        last_status, last_labels = status, labels

    avg_ms = (total / N) * 1000.0
    print(f"\n[check-sat(last)] = {last_status}")
    if last_labels:
        print("Round 15:", ", ".join(f"u{k}={last_labels[k]}" for k in range(4)))
    print(f"Average time per run over {N} runs: {avg_ms:.3f} ms")

if __name__ == "__main__":
    main()

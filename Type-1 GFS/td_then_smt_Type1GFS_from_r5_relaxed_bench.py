#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
td_then_smt_Type1GFS_from_r5_relaxed_bench.py

从第 5 轮的 SMT 符号作为输入（避开 initial constraints），
继续 Type‑1 GFS（4线）后续 10 轮（到 Round 15），
执行 100 次统计平均耗时，只打印：
  - [check-sat(last)]
  - Round 15: u0=..., u1=..., u2=..., u3=...
  - Average time per run over 100 runs: XX.XXX ms

固定第 5 轮的 SMT 符号：
  u0^5 = 0              (#b00000 = 0)
  u1^5 = x              (#b00100 = 4)
  u2^5 = δ ⊕ R(x)       (#b01001 = 9)
  u3^5 = R(δ)           (#b00010 = 2)
"""

import os, importlib.util, time
from typing import List, Dict
from cvc5 import Kind

def _load(name, filename):
    spec = importlib.util.spec_from_file_location(name, filename)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)  # type: ignore
    return mod

BASE = os.path.dirname(__file__)
RELAX_PATH = os.path.join(BASE, "smt_model_distinguish_relaxed.py")
SMT = _load("smt_model_distinguish_relaxed", RELAX_PATH)

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

def build_type1gfs_10r_from_r5():
    """Round‑5 作为输入（u0_0..u0_3），构建后续 10 轮到 Round‑15。"""
    nodes: List[Dict] = []
    rounds = [{f"u{k}": f"u0_{k}" for k in range(4)}]  # Round‑5 as inputs

    for i in range(10):
        cur = rounds[-1]
        R3 = f"R3_{i}"
        nodes.append({"op": "R", "name": R3, "in": cur["u3"]})
        X1 = f"X1_{i}"
        nodes.append({"op": "XOR", "name": X1, "a": R3, "b": cur["u0"]})
        rounds.append({
            "u0": cur["u3"],   # u0' = u3
            "u1": X1,          # u1' = R(u3) ⊕ u0
            "u2": cur["u1"],   # u2' = u1
            "u3": cur["u2"],   # u3' = u2
        })

    tails = [rounds[10][f"u{k}"] for k in range(4)]  # Round‑15
    spec = dict(n_inputs=4, nodes=nodes, tails=tails)  # relaxed engine无初值约束
    return spec, rounds

def run_once_get_round15_labels():
    spec, rounds = build_type1gfs_10r_from_r5()
    s, env = SMT.build_from_graph(spec)

    # 固定 Round‑5 种子
    mkbv = lambda x: s.mkBitVector(5, x)
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][0], mkbv(0)))   # u0^5 = 0
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][1], mkbv(4)))   # u1^5 = x
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][2], mkbv(9)))   # u2^5 = δ ⊕ R(x)
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][3], mkbv(2)))   # u3^5 = R(δ)

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
    # 预热
    for _ in range(3):
        run_once_get_round15_labels()

    N = 100
    total = 0.0
    last_status, last_labels = None, None
    for _ in range(N):
        t0 = time.perf_counter()
        status, labels = run_once_get_round15_labels()
        total += time.perf_counter() - t0
        last_status, last_labels = status, labels

    avg_ms = (total / N) * 1000.0
    print(f"[check-sat(last)] = {last_status}")
    if last_labels:
        print("Round 15:", ", ".join(f"u{k}={last_labels[k]}" for k in range(4)))
    print(f"Average time per run over {N} runs: {avg_ms:.3f} ms")

if __name__ == "__main__":
    main()

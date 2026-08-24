#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
td2smt_GFS4F_r0to10_assert_r4_bench.py

Bench 100 runs; print only the LAST run's Round-10 SMT symbols
and the average execution time per run (ms).

Substitution rules (TD→SMT at Round-4):
  a   -> δ            (0b00001)
  0s  -> R(δ) ⊕ x     (0b00110)
  0   -> 00000
  s   -> 00100
  a⊕s -> 00101
  *   -> None (no hard assertion)
"""

import os, importlib.util, time
from typing import List, Tuple
from cvc5 import Kind

REPEAT = 100

def _load(name, filename):
    spec = importlib.util.spec_from_file_location(name, filename)
    if spec is None:
        raise RuntimeError(f"Cannot load {filename}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)  # type: ignore
    return mod

TD_PATH   = os.path.join(os.path.dirname(__file__), "td_trunc.py")
SMT_PATH  = os.path.join(os.path.dirname(__file__), "smt_model_distinguish.py")

td  = _load("td_trunc", TD_PATH)
SMT = _load("smt_model_distinguish", SMT_PATH)

def td_to_smt_mask(v: "td.Val") -> int | None:
    Sym = td.Sym
    if v.sym == Sym.ZERO:    return 0b00000
    if v.sym == Sym.ZERO_S:  return 0b00110          # R(δ) ⊕ x
    if v.sym == Sym.S:       return 0b00100          # x
    if v.sym == Sym.AS:      return 0b00101          # x ⊕ δ
    if v.sym == Sym.A:       return 0b00001          # δ
    if v.sym == Sym.STAR:    return None
    return None

def td_simulate_gfs4f_to_r4(init: Tuple["td.Val", ...]):
    eng = td.TDEngine()
    u = list(init)
    for _ in range(4):
        Ru7 = eng.R(u[7]); Ru6 = eng.R(u[6]); Ru5 = eng.R(u[5]); Ru4 = eng.R(u[4])
        u = [
            td.copy_val(u[7]),             # u0' = u7
            eng.xor2(Ru7, u[0]),           # u1' = R(u7) ⊕ u0
            eng.xor2(Ru6, u[1]),           # u2' = R(u6) ⊕ u1
            eng.xor2(Ru5, u[2]),           # u3' = R(u5) ⊕ u2
            eng.xor2(Ru4, u[3]),           # u4' = R(u4) ⊕ u3
            td.copy_val(u[4]),             # u5' = u4
            td.copy_val(u[5]),             # u6' = u5
            td.copy_val(u[6]),             # u7' = u6
        ]
    return tuple(u)  # Round-4 tuple

def build_full_10r_and_refs():
    nodes = []
    rounds = [ { f"u{k}": f"u0_{k}" for k in range(8) } ]  # Round-0 inputs
    for i in range(10):
        cur = rounds[-1]
        R7 = f"R7_{i}"; R6 = f"R6_{i}"; R5 = f"R5_{i}"; R4 = f"R4_{i}"
        X1 = f"X1_{i}"; X2 = f"X2_{i}"; X3 = f"X3_{i}"; X4 = f"X4_{i}"
        nodes += [
            {"op":"R",   "name": R7, "in": cur["u7"]},
            {"op":"R",   "name": R6, "in": cur["u6"]},
            {"op":"R",   "name": R5, "in": cur["u5"]},
            {"op":"R",   "name": R4, "in": cur["u4"]},
            {"op":"XOR", "name": X1, "a": R7, "b": cur["u0"]},
            {"op":"XOR", "name": X2, "a": R6, "b": cur["u1"]},
            {"op":"XOR", "name": X3, "a": R5, "b": cur["u2"]},
            {"op":"XOR", "name": X4, "a": R4, "b": cur["u3"]},
        ]
        rounds.append({
            "u0": cur["u7"],
            "u1": X1,
            "u2": X2,
            "u3": X3,
            "u4": X4,
            "u5": cur["u4"],
            "u6": cur["u5"],
            "u7": cur["u6"],
        })
    r4_refs = [rounds[4][f"u{k}"] for k in range(8)]
    tails   = [rounds[10][f"u{k}"] for k in range(8)]
    spec = dict(
        n_inputs=8,
        nodes=nodes,
        tails=tails,
        allow_weak=True,
        sum1=True,
        monotone_guard=True,
        collisions=True,
    )
    return spec, rounds, r4_refs

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

def run_once_and_get_round10():
    # TD Round-4
    r0 = (td.S, td.A, td.Z, td.Z, td.Z, td.Z, td.Z, td.Z)
    r4 = td_simulate_gfs4f_to_r4(r0)
    masks = [td_to_smt_mask(r4[k]) for k in range(8)]

    # SMT full 10r, assert round-4 == masks (skip None)
    spec, rounds, r4_refs = build_full_10r_and_refs()
    s, env = SMT.build_from_graph(spec)
    mkbv = lambda x: s.mkBitVector(5, x)
    for k, ref in enumerate(r4_refs):
        mk = masks[k]
        if mk is not None:
            s.assertFormula(s.mkTerm(Kind.EQUAL, env["outmap"][ref][0], mkbv(mk)))

    res = s.checkSat()
    if str(res).lower() != "sat":
        return "UNSAT/UNKNOWN", None

    # fetch Round-10 labels
    names = [rounds[10][f"u{k}"] for k in range(8)]
    labels = []
    for k, nm in enumerate(names):
        is_bot = s.getValue(env["botmap"][nm][0])
        if str(is_bot).lower() == "true":
            labels.append("⊥")
        else:
            val = s.getValue(env["outmap"][nm][0])
            labels.append(bits_to_label_5(str(val)))
    return "SAT", labels

def main():
    # warmup
    for _ in range(3):
        run_once_and_get_round10()

    total = 0.0
    last_labels = None
    for _ in range(REPEAT):
        t0 = time.perf_counter()
        status, labels = run_once_and_get_round10()
        total += time.perf_counter() - t0
        last_labels = labels
        last_status = status

    avg_ms = (total / REPEAT) * 1000.0
    # Print only last run's Round-10 symbols and average time
    print(f"[check-sat] = {last_status}")
    if last_status == "SAT":
        print("Round 10:", ", ".join(f"u{k}={last_labels[k]}" for k in range(8)))
    print(f"Average time per run: {avg_ms:.3f} ms over {REPEAT} runs")

if __name__ == "__main__":
    import time
    main()

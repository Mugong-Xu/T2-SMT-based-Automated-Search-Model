#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
td2smt_GFS4F_r0to10_assert_r4_subst_v2.py

更改的 TD→SMT 代换规则：
  A(a)    → δ              (bit 0b00001)
  ZERO_S  → R(δ) ⊕ x       (bits 0b00010 | 0b00100 = 0b00110)
其余保持：
  ZERO    → 00000
  S       → 00100
  AS      → 00101
  STAR    → None（不做强断言）
然后构建完整 10 轮 GFS-4F 图，从 Round-0 合法输入出发，
将 Round-4 的 8 根线等式约束为以上映射结果，继续打印 Round 5..10 的 SMT 符号。
"""

import os, importlib.util
from typing import List, Tuple
from cvc5 import Kind

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

# === 新的 TD→SMT 代换规则 ===
def td_to_smt_mask(v: "td.Val") -> int | None:
    Sym = td.Sym
    if v.sym == Sym.ZERO:    return 0b00000                       # 0
    if v.sym == Sym.ZERO_S:  return 0b00010 | 0b00100             # R(δ) ⊕ x = 0b00110
    if v.sym == Sym.S:       return 0b00100                       # x
    if v.sym == Sym.AS:      return 0b00101                       # x ⊕ δ
    if v.sym == Sym.A:       return 0b00001                       # δ   (忽略 a_flag)
    if v.sym == Sym.STAR:    return None                          # 不作强断言
    return None

def td_val_to_str(v) -> str:
    for attr in ("to_str", "toString"):
        if hasattr(v, attr):
            try:
                s = getattr(v, attr)()
                if isinstance(s, str):
                    return s
            except Exception:
                pass
    try:
        return str(v)
    except Exception:
        return "<Val?>"

# TD：前 4 轮
def td_simulate_gfs4f_to_r4(init: Tuple["td.Val", ...]):
    eng = td.TDEngine()
    u = list(init)
    hist = [tuple(u)]
    for _ in range(4):
        Ru7 = eng.R(u[7]); Ru6 = eng.R(u[6]); Ru5 = eng.R(u[5]); Ru4 = eng.R(u[4])
        nxt = [None]*8
        nxt[0] = td.copy_val(u[7])
        nxt[1] = eng.xor2(Ru7, u[0])
        nxt[2] = eng.xor2(Ru6, u[1])
        nxt[3] = eng.xor2(Ru5, u[2])
        nxt[4] = eng.xor2(Ru4, u[3])
        nxt[5] = td.copy_val(u[4])
        nxt[6] = td.copy_val(u[5])
        nxt[7] = td.copy_val(u[6])
        u = nxt
        hist.append(tuple(u))
    return hist  # Round 0..4

# SMT：完整 10 轮，并记录 Round-4 与 Round-10 的引用
def build_full_10r_and_refs():
    nodes = []
    rounds = [ { f"u{k}": f"u0_{k}" for k in range(8) } ]  # Round-0: inputs

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

def main():
    # TD 前 4 轮
    init = (td.S, td.A, td.Z, td.Z, td.Z, td.Z, td.Z, td.Z)
    td_hist = td_simulate_gfs4f_to_r4(init)
    print("== TD (Round 0..4) ==")
    for r in range(5):
        print("Round", r, ":", ", ".join(f"u{k}^{r}={td_val_to_str(td_hist[r][k])}" for k in range(8)))

    # Round-4 → 新代换的掩码
    masks = [td_to_smt_mask(td_hist[4][k]) for k in range(8)]
    print("\nTD→SMT Round-4 masks (new rules):", masks)

    # SMT 构图并将 Round-4 线固定为掩码
    spec, rounds, r4_refs = build_full_10r_and_refs()
    s, env = SMT.build_from_graph(spec)
    mkbv = lambda x: s.mkBitVector(5, x)

    for k, ref in enumerate(r4_refs):
        mk = masks[k]
        if mk is not None:
            s.assertFormula(s.mkTerm(Kind.EQUAL, env["outmap"][ref][0], mkbv(mk)))

    res = s.checkSat()
    print("\ncheck-sat:", res)
    if str(res).lower() != "sat":
        print("UNSAT/UNKNOWN，无法打印后续轮。")
        return

    print("\n== SMT (Round 5..10) ==")
    for idx in range(5, 11):
        names = [rounds[idx][f"u{k}"] for k in range(8)]
        labs = []
        for k, nm in enumerate(names):
            is_bot = s.getValue(env["botmap"][nm][0])
            if str(is_bot).lower() == "true":
                labs.append(f"u{k}^{idx}=⊥")
            else:
                val = s.getValue(env["outmap"][nm][0])
                labs.append(f"u{k}^{idx}={bits_to_label_5(str(val))}")
        print("Round", idx, ":", ", ".join(labs))

if __name__ == "__main__":
    main()

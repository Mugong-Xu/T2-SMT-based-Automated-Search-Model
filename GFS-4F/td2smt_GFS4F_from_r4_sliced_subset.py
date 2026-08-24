#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
td2smt_GFS4F_from_r4_sliced_subset.py

目的：解决从 TD Round-4 切到 SMT 时出现的 UNSAT。
策略：
  - 不指定 tails（去掉末端结构性约束）；
  - 关闭 sum1 / monotone_guard / collisions；
  - 用“子集”方式播种：对每根线 w 断言  (w & mask) == mask  （mask≠0 时）；
    这意味着允许 w 包含 mask 指定的所有位，且可包含额外位，避免过强相等约束。
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

def td_to_smt_mask(v: "td.Val") -> int:
    Sym = td.Sym
    if v.sym == Sym.ZERO:    return 0b00000
    if v.sym == Sym.ZERO_S:  return 0b10000
    if v.sym == Sym.S:       return 0b00100
    if v.sym == Sym.AS:      return 0b00101
    if v.sym == Sym.A:
        a_flag = getattr(v, "a_flag", 0) or getattr(v, "aFlag", 0)
        return (0b10001 if a_flag==1 else 0b00001)
    # 其它（含 *）统一返回 0，不做约束
    return 0

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
def td_simulate_gfs4f_to_r4(init: Tuple["td.Val", ...]) -> List[Tuple["td.Val", ...]]:
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
    return hist

# SMT 后缀（无 tails，约束放宽）
def build_smt_suffix_relaxed_no_tails():
    nodes = []
    rounds = [ { f"u{k}": f"u0_{k}" for k in range(8) } ]  # 标准输入
    for i in range(6):
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
    spec = dict(
        n_inputs=8,
        nodes=nodes,
        # An explicit empty list implements the intended "no tails" model while
        # remaining compatible with build_from_graph's required spec schema.
        tails=[],
        allow_weak=True,
        sum1=False,
        monotone_guard=False,
        collisions=False,
    )
    return spec, rounds

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
    # TD 到 Round-4
    init = (td.S, td.A, td.Z, td.Z, td.Z, td.Z, td.Z, td.Z)
    td_hist = td_simulate_gfs4f_to_r4(init)

    print("== TD (Round 0..4) ==")
    for r in range(5):
        print("Round", r, ":", ", ".join(f"u{k}^{r}={td_val_to_str(td_hist[r][k])}" for k in range(8)))

    masks = [td_to_smt_mask(td_hist[4][k]) for k in range(8)]

    # SMT 后缀（放宽且无 tails）
    spec, rounds = build_smt_suffix_relaxed_no_tails()
    s, env = SMT.build_from_graph(spec)

    mkbv = lambda x: s.mkBitVector(5, x)
    bvand = lambda a, b: s.mkTerm(Kind.BITVECTOR_AND, a, b)

    # 子集约束： (inputs[k] & mask) == mask  (mask!=0)
    for k in range(8):
        m = masks[k]
        if m != 0:
            inp = env["inputs"][k]
            mask_term = mkbv(m)
            s.assertFormula(s.mkTerm(Kind.EQUAL, bvand(inp, mask_term), mask_term))

    res = s.checkSat()
    print("\ncheck-sat:", res)
    if str(res).lower() != "sat":
        print("UNSAT/UNKNOWN，无法打印后续轮。")
        return

    print("\n== SMT (Round 5..10) ==")
    for idx in range(1, 7):
        rname = 4 + idx
        nm = [rounds[idx][f"u{k}"] for k in range(8)]
        labs = []
        for k, name in enumerate(nm):
            is_bot = s.getValue(env["botmap"][name][0])
            if str(is_bot).lower() == "true":
                labs.append(f"u{k}^{rname}=⊥")
            else:
                v = s.getValue(env["outmap"][name][0])
                labs.append(f"u{k}^{rname}={bits_to_label_5(str(v))}")
        print("Round", rname, ":", ", ".join(labs))

if __name__ == "__main__":
    main()

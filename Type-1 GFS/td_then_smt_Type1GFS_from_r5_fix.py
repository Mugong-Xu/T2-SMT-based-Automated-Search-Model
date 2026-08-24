#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os, importlib.util
from typing import List, Dict
from cvc5 import Kind

def _load(name, filename):
    spec = importlib.util.spec_from_file_location(name, filename)
    if spec is None:
        raise RuntimeError(f"Cannot load {filename}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)  # type: ignore
    return mod

BASE = os.path.dirname(__file__)
TD_PATH  = os.path.join(BASE, "td_trunc.py")
SMT_PATH = os.path.join(BASE, "smt_model_distinguish.py")

td  = _load("td_trunc", TD_PATH)
SMT = _load("smt_model_distinguish", SMT_PATH)

def td_bits_to_str(v: "td.Val") -> str:
    for f in ("to_str", "toString"):
        if hasattr(v, f):
            try:
                s = getattr(v, f)()
                if isinstance(s, str):
                    return s
            except Exception:
                pass
    try:
        return str(v)
    except Exception:
        return "<Val?>"

def td_run_5_rounds(u0, u1, u2, u3):
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
    """
    用 u0_0..u0_3 作为“Round-5 输入名”，以兼容 build_from_graph 的输入命名约定。
    """
    nodes: List[Dict] = []
    rounds = [ { f"u{k}": f"u0_{k}" for k in range(4) } ]  # treat Round-5 as inputs u0_0..u0_3

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

    tails = [ rounds[10][f"u{k}"] for k in range(4) ]  # Round-15
    spec = dict(
        n_inputs=4,
        nodes=nodes,
        tails=tails,
        allow_weak=True,
        sum1=True,
        monotone_guard=True,
        collisions=True,
    )
    return spec, rounds

def run_smt_from_round5_and_print():
    spec, rounds = build_type1gfs_10r_from_r5()
    s, env = SMT.build_from_graph(spec)

    # 固定“Round-5 输入”
    mkbv = lambda x: s.mkBitVector(5, x)
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][0], mkbv(0 )))  # u0^5 = 0
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][1], mkbv(4 )))  # u1^5 = x
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][2], mkbv(9 )))  # u2^5 = δ ⊕ R(x)
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][3], mkbv(2 )))  # u3^5 = R(δ)

    res = s.checkSat()
    print("\n[SMT checkSat] =", res)
    if str(res).lower() != "sat":
        print("UNSAT/UNKNOWN，无法打印后续轮。")
        return

    print("=== SMT 继续推导 Round 6..15 ===")
    for idx in range(1, 11):
        rnum = 5 + idx
        names = [rounds[idx][f"u{k}"] for k in range(4)]
        labs = []
        for k, nm in enumerate(names):
            bot = s.getValue(env["botmap"][nm][0])
            if str(bot).lower() == "true":
                labs.append(f"u{k}^{rnum}=⊥")
            else:
                val = s.getValue(env["outmap"][nm][0])
                labs.append(f"u{k}^{rnum}={bits_to_label_5(str(val))}")
        print("Round", rnum, ":", ", ".join(labs))

def main():
    # TD 0..5 轮
    td_hist = td_run_5_rounds(td.S, td.A, td.Z, td.Z)
    print("== TD 0..5 轮输出 ==")
    for r in range(6):
        u0,u1,u2,u3 = td_hist[r]
        print(f"Round {r} : u0={td_bits_to_str(u0)}, u1={td_bits_to_str(u1)}, u2={td_bits_to_str(u2)}, u3={td_bits_to_str(u3)}")

    # SMT 5→15 轮
    run_smt_from_round5_and_print()

if __name__ == "__main__":
    main()

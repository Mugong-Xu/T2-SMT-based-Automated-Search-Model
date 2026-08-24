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

BASE_DIR = os.path.dirname(__file__)
SMT_PATH = os.path.join(BASE_DIR, "smt_model_distinguish.py")
SMT = _load("smt_model_distinguish", SMT_PATH)

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

def build_type1gfs_15r():
    nodes: List[Dict] = []
    rounds = [ { f"u{k}": f"u0_{k}" for k in range(4) } ]  # Round 0 inputs
    for i in range(15):
        cur = rounds[-1]
        R3 = f"R3_{i}"
        nodes.append({"op": "R", "name": R3, "in": cur["u3"]})
        X1 = f"X1_{i}"
        nodes.append({"op": "XOR", "name": X1, "a": R3, "b": cur["u0"]})
        rounds.append({
            "u0": cur["u3"],
            "u1": X1,
            "u2": cur["u1"],
            "u3": cur["u2"],
        })
    tails = [ rounds[15][f"u{k}"] for k in range(4) ]
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

def main():
    spec, rounds = build_type1gfs_15r()
    s, env = SMT.build_from_graph(spec)
    X, D, Z = env["syms"]["X"], env["syms"]["DELTA"], env["syms"]["ZERO"]
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][0], X))
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][1], D))
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][2], Z))
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][3], Z))
    res = s.checkSat()
    print("[check-sat] =", res)
    if str(res).lower() != "sat":
        return
    for ri in range(0, 16):
        names = [rounds[ri][f"u{k}"] for k in range(4)]
        labs = []
        for k, nm in enumerate(names):
            bot = s.getValue(env["botmap"][nm][0])
            if str(bot).lower() == "true":
                labs.append(f"u{k}^{ri}=⊥")
            else:
                val = s.getValue(env["outmap"][nm][0])
                labs.append(f"u{k}^{ri}={bits_to_label_5(str(val))}")
        print(f"Round {ri}:  " + ", ".join(labs))

if __name__ == "__main__":
    main()

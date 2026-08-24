#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os, importlib.util, itertools
from typing import List, Dict, Tuple
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

def build_type1gfs_15r(sum1: bool, guard: bool, collisions: bool):
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
        sum1=sum1,
        monotone_guard=guard,
        collisions=collisions,
    )
    return spec, rounds

def run_check(sum1: bool, guard: bool, collisions: bool) -> Tuple[bool, str, list]:
    spec, rounds = build_type1gfs_15r(sum1, guard, collisions)
    s, env = SMT.build_from_graph(spec)

    # Inputs: u0=x, u1=δ, u2=0, u3=0
    X, D, Z = env["syms"]["X"], env["syms"]["DELTA"], env["syms"]["ZERO"]
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][0], X))
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][1], D))
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][2], Z))
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][3], Z))

    res = s.checkSat()
    if str(res).lower() != "sat":
        return False, "UNSAT/UNKNOWN", []

    ri = 12
    names = [rounds[ri][f"u{k}"] for k in range(4)]
    raws = []
    for nm in names:
        try:
            val = s.getValue(env["outmap"][nm][0])
            raws.append(str(val))
        except Exception:
            raws.append("⊥")

    # 0s 位是 bit4（0b10000）；检查 u1^12 的原始 BV 是否带该位
    has_0s = False
    if raws[1].startswith("#b"):
        bits = raws[1][2:].zfill(5)[-5:]
        has_0s = (bits[0] == "1")  # MSB

    return has_0s, "HIT" if has_0s else "MISS", raws

def main():
    tried = []
    hit = None
    for sum1, guard, coll in itertools.product([True, False], [True, False], [True, False]):
        ok, status, raws = run_check(sum1, guard, coll)
        tried.append(((sum1, guard, coll), status, raws))
        if ok and hit is None:
            hit = ((sum1, guard, coll), raws)

    if hit:
        (sum1, guard, coll), raws = hit
        print(f"[FOUND] Config sum1={sum1}, guard={guard}, collisions={coll}")
        print("Round 12 raw BV:", raws, "(u1 has 0s-bit)")
    else:
        print("[NO CONFIG FOUND] No config where u1^12 contains 0s-bit.")
        print("Tried configs summary:")
        for (sum1, guard, coll), status, raws in tried:
            print(f"  sum1={sum1}, guard={guard}, collisions={coll} -> {status}; raw={raws}")

if __name__ == "__main__":
    main()

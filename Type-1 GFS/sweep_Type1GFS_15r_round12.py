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

TARGET_BITS = "#b11001"  # 0s ⊕ δ ⊕ R(x)

def run_config(sum1: bool, guard: bool, collisions: bool) -> Tuple[bool, str, list, list]:
    spec, rounds = build_type1gfs_15r(sum1, guard, collisions)
    s, env = SMT.build_from_graph(spec)

    # Inputs: u0=x, u1=δ, u2=0, u3=0
    X, D, Z = env["syms"]["X"], env["syms"]["DELTA"], env["syms"]["ZERO"]
    from cvc5 import Kind
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][0], X))
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][1], D))
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][2], Z))
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][3], Z))

    res = s.checkSat()
    if str(res).lower() != "sat":
        return False, "UNSAT/UNKNOWN", [], []

    # Round 12
    ri = 12
    names = [rounds[ri][f"u{k}"] for k in range(4)]
    labs, raws = [], []
    for k, nm in enumerate(names):
        bot = s.getValue(env["botmap"][nm][0])
        if str(bot).lower() == "true":
            labs.append("⊥")
            raws.append("⊥")
        else:
            val = s.getValue(env["outmap"][nm][0])
            labs.append(bits_to_label_5(str(val)))
            raws.append(str(val))

    # Also fetch raw BV even when ⊥, if possible (best-effort)
    for k, nm in enumerate(names):
        try:
            val = s.getValue(env["outmap"][nm][0])
            raws[k] = str(val)
        except Exception:
            pass

    ok = (raws[1] == TARGET_BITS)  # u1^12 equals target?
    status = "HIT" if ok else "MISS"
    return ok, status, labs, raws

def main():
    tried = []
    hit = None
    for sum1, guard, coll in itertools.product([True, False], [True, False], [True, False]):
        ok, status, labs, raws = run_config(sum1, guard, coll)
        tried.append(((sum1, guard, coll), status, labs, raws))
        if ok and hit is None:
            hit = ((sum1, guard, coll), labs, raws)

    if hit:
        (sum1, guard, coll), labs, raws = hit
        print(f"[FOUND] Config sum1={sum1}, guard={guard}, collisions={coll}")
        print("Round 12 (labels):", ", ".join(f"u{k}={labs[k]}" for k in range(4)))
        print("Round 12 (raw BV):", raws)
    else:
        print("[NO CONFIG FOUND] None of the 8 configs yielded u1^12 = 0s ⊕ δ ⊕ R(x) (#b11001).")
        print("Tried configs summary:")
        for (sum1, guard, coll), status, labs, raws in tried:
            print(f"  sum1={sum1}, guard={guard}, collisions={coll} -> {status}; raw={raws}")

if __name__ == "__main__":
    main()

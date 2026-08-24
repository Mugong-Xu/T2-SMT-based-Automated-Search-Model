#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os, importlib.util, itertools
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
    r_nodes = []
    for i in range(15):
        cur = rounds[-1]
        R3 = f"R3_{i}"
        nodes.append({"op": "R", "name": R3, "in": cur["u3"]})
        r_nodes.append((R3, cur["u3"]))
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
    return spec, rounds, r_nodes

def add_R_singleton_with_exception(s, env, r_nodes):
    """
    Enforce:
      1) If input has >=2 hot bits among {δ, Rδ, x, Rx, 0s}, R becomes ⊥,
         EXCEPT when input is exactly (x ⊕ Rδ), in which case R=0s (bot=False).
    """
    mkbv = lambda x: s.mkBitVector(5, x)
    zero = mkbv(0)
    # basis masks
    M_DELTA = 1
    M_RDEL  = 2
    M_X     = 4
    M_RX    = 8
    M_0S    = 16

    # pair list for the ">=2 bits" implication, skipping the special (x,Rδ)
    pairs = [(a,b) for a,b in itertools.combinations([M_DELTA, M_RDEL, M_X, M_RX, M_0S], 2)
             if not ((a==M_X and b==M_RDEL) or (a==M_RDEL and b==M_X))]

    for r_name, in_ref in r_nodes:
        in_bv = env["outmap"][in_ref][0]
        r_bot = env["botmap"][r_name][0]
        r_out = env["outmap"][r_name][0]

        # Special EXACT case: (x & in) && (Rδ & in) && !(δ|Rx|0s in)
        x_hit   = s.mkTerm(Kind.DISTINCT, s.mkTerm(Kind.BITVECTOR_AND, in_bv, mkbv(M_X)),   zero)
        rdel_hit= s.mkTerm(Kind.DISTINCT, s.mkTerm(Kind.BITVECTOR_AND, in_bv, mkbv(M_RDEL)),zero)
        d_hit   = s.mkTerm(Kind.DISTINCT, s.mkTerm(Kind.BITVECTOR_AND, in_bv, mkbv(M_DELTA)),zero)
        rx_hit  = s.mkTerm(Kind.DISTINCT, s.mkTerm(Kind.BITVECTOR_AND, in_bv, mkbv(M_RX)),  zero)
        z_hit   = s.mkTerm(Kind.DISTINCT, s.mkTerm(Kind.BITVECTOR_AND, in_bv, mkbv(M_0S)),  zero)

        not_others = s.mkTerm(Kind.AND,
                              s.mkTerm(Kind.NOT, d_hit),
                              s.mkTerm(Kind.NOT, rx_hit),
                              s.mkTerm(Kind.NOT, z_hit))

        exact_x_plus_rdel = s.mkTerm(Kind.AND, x_hit, rdel_hit, not_others)

        # If exact (x⊕Rδ), force R output to 0s and NOT bot
        s.assertFormula(s.mkTerm(Kind.IMPLIES, exact_x_plus_rdel,
                                 s.mkTerm(Kind.AND,
                                          s.mkTerm(Kind.EQUAL, r_out, mkbv(M_0S)),
                                          s.mkTerm(Kind.NOT, r_bot))))

        # For all other pairs (>=2 bits) imply bot=True
        for a,b in pairs:
            a_hit = s.mkTerm(Kind.DISTINCT, s.mkTerm(Kind.BITVECTOR_AND, in_bv, mkbv(a)), zero)
            b_hit = s.mkTerm(Kind.DISTINCT, s.mkTerm(Kind.BITVECTOR_AND, in_bv, mkbv(b)), zero)
            cond = s.mkTerm(Kind.AND, a_hit, b_hit)
            s.assertFormula(s.mkTerm(Kind.IMPLIES, cond, r_bot))

def main():
    spec, rounds, r_nodes = build_type1gfs_15r()
    s, env = SMT.build_from_graph(spec)

    # Enforce R semantics with the special x⊕R(δ) → 0s rule
    add_R_singleton_with_exception(s, env, r_nodes)

    # Inputs: u0=x, u1=δ, u2=0, u3=0
    X, D, Z = env["syms"]["X"], env["syms"]["DELTA"], env["syms"]["ZERO"]
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][0], X))
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][1], D))
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][2], Z))
    s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][3], Z))

    res = s.checkSat()
    print("[check-sat] =", res)
    if str(res).lower() != "sat":
        return

    # Quick check Rounds 6 and 7
    for ri in [6,7]:
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

    print("\n== All Rounds 0..15 ==")
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

#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import argparse, os, importlib.util
from cvc5 import Kind

# Bit helpers
def bv_to_bits5(bv_str: str) -> str:
    s = str(bv_str).strip()
    if s.startswith("#b"):
        bits = s[2:].zfill(5)[-5:]
        return bits
    if s.startswith("(_ bv"):
        parts = s.replace("(", "").replace(")", "").split()
        n = int(parts[1][2:]) if parts[1].startswith("bv") else int(parts[1])
        return bin(n)[2:].zfill(5)[-5:]
    n = int(s)
    return bin(n)[2:].zfill(5)[-5:]

def bits5_to_symbol(bits_str: str) -> str:
    # bits_str: '01011' with order [0s, R(x), x, R(δ), δ]
    if bits_str is None:
        return "<?>"
    if bits_str == "00000":
        return "0"
    parts = []
    if bits_str[4] == "1": parts.append("δ")
    if bits_str[3] == "1": parts.append("R(δ)")
    if bits_str[2] == "1": parts.append("x")
    if bits_str[1] == "1": parts.append("R(x)")
    if bits_str[0] == "1": parts.append("0s")
    return " ⊕ ".join(parts) if parts else "0"

def load_user_model(path: str):
    spec = importlib.util.spec_from_file_location("smt_model_distinguish", path)
    if spec is None:
        raise RuntimeError(f"Cannot locate model at: " + path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)  # type: ignore
    return module

def build_newstructIV_9r_spec(allow_weak: bool, sum1: bool, monotone_guard: bool, collisions: bool):
    # Round wires container (start at round 0 inputs)
    rounds = [{"u0": "u0_0", "u1": "u0_1", "u2": "u0_2", "u3": "u0_3"}]
    nodes = []
    # Build 9 rounds: 0->1, 1->2, ..., 8->9
    for i in range(9):
        cur = rounds[-1]
        r_name = f"R_{i}"
        x10 = f"X10_{i}"
        x23 = f"X23_{i}"
        # new structure IV:
        # u0' = R(u3)
        nodes.append({"op": "R", "name": r_name, "in": cur["u3"]})
        # u1' = u3 ⊕ u0
        nodes.append({"op": "XOR", "name": x10, "a": cur["u3"], "b": cur["u0"]})
        # u2' = u1 ⊕ u3
        nodes.append({"op": "XOR", "name": x23, "a": cur["u1"], "b": cur["u3"]})
        # u3' = u2
        rounds.append({
            "u0": r_name,
            "u1": x10,
            "u2": x23,
            "u3": cur["u2"],
        })
    # Tails are the last round's wires (round 9)
    tails = [rounds[-1]["u0"], rounds[-1]["u1"], rounds[-1]["u2"], rounds[-1]["u3"]]
    spec = dict(
        n_inputs=4,
        nodes=nodes,
        tails=tails,
        allow_weak=allow_weak,
        sum1=sum1,
        monotone_guard=monotone_guard,
        collisions=collisions,
    )
    return spec, rounds

def main():
    here = os.path.dirname(__file__)
    default_model = os.path.join(here, "smt_model_distinguish_new_IV.py")  # use the new wrapper by default

    ap = argparse.ArgumentParser()
    ap.add_argument("--model", default=default_model)
    ap.add_argument("--collisions", type=int, default=0, help="1 to enable Property 3/4 in XOR; 0 to disable")
    ap.add_argument("--sum1", type=int, default=0)
    ap.add_argument("--monotone-guard", type=int, default=0)
    ap.add_argument("--allow-weak", type=int, default=1)
    args = ap.parse_args()

    mod = load_user_model(args.model)

    spec, rounds = build_newstructIV_9r_spec(
        allow_weak=bool(args.allow_weak),
        sum1=bool(args.sum1),
        monotone_guard=bool(args.monotone_guard),
        collisions=bool(args.collisions),
    )

    s, env = mod.build_from_graph(spec)
    syms = env["syms"]
    inputs = env["inputs"]  # u0_0,u0_1,u0_2,u0_3  (round-0 inputs)

    # Round-0 constraints:
    # u0^0 = δ, u1^0 = x ⊕ δ, u2^0 = 0, u3^0 = δ
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[0], syms["DELTA"]))                            # δ
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[1], s.mkBitVector(5, int('00101',2))))        # x⊕δ
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[2], syms["ZERO"]))                             # 0
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[3], syms["DELTA"]))                            # δ

    res = s.checkSat()
    print("check-sat:", res)
    if str(res) != "sat":
        return

    print("Model file:", args.model)
    print("Bit order: [0s, R(x), x, R(δ), δ]  (msb..lsb)")
    # Print Round 1..9
    for i in range(1, 10):
        row = []
        for nm in ["u0","u1","u2","u3"]:
            ref = rounds[i][nm]
            is_bot = s.getValue(env["botmap"][ref][0])
            if str(is_bot).lower() == "true":
                row.append("⊥")
            else:
                v = s.getValue(env["outmap"][ref][0])
                bits = bv_to_bits5(str(v))
                row.append("#b" + bits + "  => " + bits5_to_symbol(bits))
        print(f"Round {i:2d}:  u0={row[0]:>20s}  u1={row[1]:>20s}  u2={row[2]:>20s}  u3={row[3]:>20s}")

if __name__ == "__main__":
    main()

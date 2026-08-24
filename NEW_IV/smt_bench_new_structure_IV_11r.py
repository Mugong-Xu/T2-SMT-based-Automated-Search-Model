#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import argparse, os, importlib.util, time
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

def build_newstructIV_spec(depth: int, allow_weak: bool, sum1: bool, monotone_guard: bool, collisions: bool):
    # Round wires container (start at round 0 inputs)
    rounds = [{"u0": "u0_0", "u1": "u0_1", "u2": "u0_2", "u3": "u0_3"}]
    nodes = []
    # Build 'depth' rounds: 0->1, 1->2, ..., (depth-1)->depth
    for i in range(depth):
        cur = rounds[-1]
        r_name = f"R_{i}"
        x10 = f"X10_{i}"
        x23 = f"X23_{i}"
        # new structure IV:
        # u0' = R(u3); u1' = u3 ⊕ u0; u2' = u1 ⊕ u3; u3' = u2
        nodes.append({"op": "R", "name": r_name, "in": cur["u3"]})
        nodes.append({"op": "XOR", "name": x10, "a": cur["u3"], "b": cur["u0"]})
        nodes.append({"op": "XOR", "name": x23, "a": cur["u1"], "b": cur["u3"]})
        rounds.append({"u0": r_name, "u1": x10, "u2": x23, "u3": cur["u2"]})
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

def one_run(mod, depth: int, allow_weak: bool, sum1: bool, monotone_guard: bool, collisions: bool):
    spec, rounds = build_newstructIV_spec(depth, allow_weak, sum1, monotone_guard, collisions)
    s, env = mod.build_from_graph(spec)
    syms = env["syms"]
    inputs = env["inputs"]  # u0_0,u0_1,u0_2,u0_3

    # Round-0 constraints:
    # u0^0 = δ, u1^0 = x ⊕ δ, u2^0 = 0, u3^0 = δ
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[0], syms["DELTA"]))                            # δ
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[1], s.mkBitVector(5, int('00101',2))))        # x⊕δ
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[2], syms["ZERO"]))                             # 0
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[3], syms["DELTA"]))                            # δ

    res = s.checkSat()
    if str(res) != "sat":
        return False, None, None, None, None

    # Only the final round's outputs
    last = rounds[depth]
    outs = []
    for nm in ["u0","u1","u2","u3"]:
        ref = last[nm]
        is_bot = s.getValue(env["botmap"][ref][0])
        if str(is_bot).lower() == "true":
            outs.append("⊥")
        else:
            v = s.getValue(env["outmap"][ref][0])
            bits = bv_to_bits5(str(v))
            outs.append(bits5_to_symbol(bits))
    return True, outs[0], outs[1], outs[2], outs[3]

def main():
    here = os.path.dirname(__file__)
    default_model = os.path.join(here, "smt_model_distinguish_new_IV.py")

    ap = argparse.ArgumentParser()
    ap.add_argument("--model", default=default_model)
    ap.add_argument("--depth", type=int, default=11, help="forward rounds (prints only final round)")
    ap.add_argument("--collisions", type=int, default=0)
    ap.add_argument("--sum1", type=int, default=0)
    ap.add_argument("--monotone-guard", type=int, default=0)
    ap.add_argument("--allow-weak", type=int, default=1)
    ap.add_argument("--runs", type=int, default=100, help="number of repetitions")
    args = ap.parse_args()

    mod = load_user_model(args.model)

    total = 0.0
    sat_cnt = 0
    last_symbols = None

    for _ in range(args.runs):
        t0 = time.perf_counter()
        sat, u0,u1,u2,u3 = one_run(
            mod, args.depth,
            bool(args.allow_weak),
            bool(args.sum1),
            bool(args.monotone_guard),
            bool(args.collisions),
        )
        t1 = time.perf_counter()
        total += (t1 - t0)
        if sat:
            sat_cnt += 1
            last_symbols = (u0,u1,u2,u3)

    avg = total / float(args.runs) if args.runs > 0 else 0.0

    # Output: only the final round symbols (from the last SAT run), and average time
    if last_symbols is None:
        print("All runs UNSAT. Average time over runs: %.6f s" % avg)
    else:
        u0,u1,u2,u3 = last_symbols
        print("Final Round Symbols:  u0=%s  u1=%s  u2=%s  u3=%s" % (u0,u1,u2,u3))
        print("Runs: %d, SAT: %d, UNSAT: %d" % (args.runs, sat_cnt, args.runs - sat_cnt))
        print("Average time: %.6f s" % avg)

if __name__ == "__main__":
    main()

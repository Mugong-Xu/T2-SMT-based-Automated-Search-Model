#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
smt_run_GFS4F_10r_bench_min.py

Benchmark:
  - Build 10-round GFS-4F graph with smt_model_distinguish.py
  - Inputs: u0^0=x, u1^0=δ, u2..u7^0=0
  - Repeat 100 times; print ONLY last run's Round 10 symbols and average time/run
"""

import importlib.util, os, time
from cvc5 import Kind

MODEL_PATH = os.path.join(os.path.dirname(__file__), "smt_model_distinguish.py")
if not os.path.exists(MODEL_PATH):
    MODEL_PATH = "smt_model_distinguish.py"

REPEAT = 100
ROUNDS = 10

def load_user_model(path: str):
    spec = importlib.util.spec_from_file_location("smt_model_distinguish", path)
    if spec is None:
        raise RuntimeError(f"Cannot locate module at {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)  # type: ignore
    return module

def bv_to_bits5(s: str):
    s = str(s).strip()
    if s.startswith("#b"):
        bits = s[2:].zfill(5)[-5:]
        return [int(b) for b in bits]
    return None

def bits_to_label(bits):
    if bits is None:
        return "<??>"
    if bits == [0,0,0,0,0]:
        return "0"
    parts = []
    # Interpret as [0s,R(x),x,R(δ),δ] (MSB..LSB typical in our runners)
    if bits[4]: parts.append("δ")
    if bits[3]: parts.append("R(δ)")
    if bits[2]: parts.append("x")
    if bits[1]: parts.append("R(x)")
    if bits[0]: parts.append("0s")
    return " ⊕ ".join(parts) if parts else "0"

def get_pair(env, ref: str):
    outmap, botmap = env["outmap"], env["botmap"]
    if ":" in ref:
        name, idx = ref.split(":"); idx = int(idx)
    else:
        name, idx = ref, 0
    return outmap[name][idx], botmap[name][idx]

def fetch_label(s, env, ref: str):
    t, b = get_pair(env, ref)
    is_bot = (str(s.getValue(b)).lower() == "true")
    if is_bot:
        return "⊥"
    v = s.getValue(t)
    return bits_to_label(bv_to_bits5(str(v)))

def build_and_run(mod):
    nodes = []
    rounds = []
    rounds.append({f"u{k}": f"u0_{k}" for k in range(8)})
    for i in range(ROUNDS):
        cur = rounds[-1]
        R7 = f"R7_{i}"; R6 = f"R6_{i}"; R5 = f"R5_{i}"; R4 = f"R4_{i}"
        X1 = f"X1_{i}"; X2 = f"X2_{i}"; X3 = f"X3_{i}"; X4 = f"X4_{i}"
        nodes.append({"op": "R",   "name": R7, "in": cur["u7"]})
        nodes.append({"op": "R",   "name": R6, "in": cur["u6"]})
        nodes.append({"op": "R",   "name": R5, "in": cur["u5"]})
        nodes.append({"op": "R",   "name": R4, "in": cur["u4"]})
        nodes.append({"op": "XOR", "name": X1, "a": R7,       "b": cur["u0"]})
        nodes.append({"op": "XOR", "name": X2, "a": R6,       "b": cur["u1"]})
        nodes.append({"op": "XOR", "name": X3, "a": R5,       "b": cur["u2"]})
        nodes.append({"op": "XOR", "name": X4, "a": R4,       "b": cur["u3"]})
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
        tails=[rounds[-1][f"u{k}"] for k in range(8)],
        allow_weak=True,
        sum1=True,
        monotone_guard=True,
        collisions=True,
    )

    s, env = mod.build_from_graph(spec)
    inputs = env["inputs"]; syms = env["syms"]
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[0], syms["X"]))       # u0^0 = x
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[1], syms["DELTA"]))   # u1^0 = δ
    for k in range(2, 8):
        s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[k], syms["ZERO"]))

    res = s.checkSat()
    if str(res).lower() != "sat":
        return ["UNSAT"]*8

    # Only final round (Round 10)
    labels = [fetch_label(s, env, rounds[ROUNDS][f"u{k}"]) for k in range(8)]
    return labels

def main():
    mod = load_user_model(MODEL_PATH)

    # Warmup (not counted)
    for _ in range(3):
        _ = build_and_run(mod)

    # Timed runs
    total = 0.0
    last_labels = None
    for _ in range(REPEAT):
        t0 = time.perf_counter()
        last_labels = build_and_run(mod)
        total += time.perf_counter() - t0

    avg_ms = (total / REPEAT) * 1000.0
    # Print only the final round's symbols from the last run and average time
    print("Round 10:", ", ".join(f"u{k}={last_labels[k]}" for k in range(8)))
    print(f"Average time per run: {avg_ms:.3f} ms over {REPEAT} runs")

if __name__ == "__main__":
    main()

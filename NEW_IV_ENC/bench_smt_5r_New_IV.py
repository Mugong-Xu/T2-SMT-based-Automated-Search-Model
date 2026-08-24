# -*- coding: utf-8 -*-
"""
bench_smt_5r_New_IV.py

使用 SMT 仅计算 NEW_IV_ENC 前 5 轮是否存在量子区分器。
QD 判定 = Round-5 最后一轮四个分支中，任一分支同时包含 x-family 与 δ-family。
不执行剪枝。
"""

import os
import time
import importlib.util
from cvc5 import Kind

MODEL_DEFAULT = os.path.join(os.path.dirname(__file__), "smt_model_distinguish.py")
ROUNDS_N = 5
RUNS = 100


def load_model(path: str):
    spec = importlib.util.spec_from_file_location("smt_model_distinguish", path)
    if spec is None:
        raise RuntimeError(f"Cannot locate model: {path}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)  # type: ignore
    return mod


def bv_to_bits5(bv_str: str):
    s = str(bv_str).strip()
    if s.startswith("#b"):
        bits = s[2:].zfill(5)[-5:]
        return [int(b) for b in bits]  # [0s,Rx,x,Rδ,δ]
    if s.startswith("(_ bv"):
        parts = s.replace("(", "").replace(")", "").split()
        n = int(parts[1][2:]) if parts[1].startswith("bv") else int(parts[1])
        bs = bin(n)[2:].zfill(5)[-5:]
        return [int(b) for b in bs]
    try:
        n = int(s)
        bs = bin(n)[2:].zfill(5)[-5:]
        return [int(b) for b in bs]
    except Exception:
        return [None] * 5


def bits5_to_symbol(bits):
    if bits is None or any(b is None for b in bits):
        return "<?>"
    if bits == [0, 0, 0, 0, 0]:
        return "0"
    parts = []
    if bits[4]:
        parts.append("δ")
    if bits[3]:
        parts.append("R(δ)")
    if bits[2]:
        parts.append("x")
    if bits[1]:
        parts.append("R(x)")
    if bits[0]:
        parts.append("0s")
    return " ⊕ ".join(parts) if parts else "0"


def has_quantum_distinguisher(bits):
    if bits is None:
        return False
    xfam = (bits[2] == 1) or (bits[1] == 1)
    dfam = (bits[4] == 1) or (bits[3] == 1)
    return xfam and dfam


def get_pair(env, ref: str):
    outmap, botmap = env["outmap"], env["botmap"]
    if ":" in ref:
        name, idx = ref.split(":")
        idx = int(idx)
    else:
        name, idx = ref, 0
    return outmap[name][idx], botmap[name][idx]


def fetch_value_bits(s, env, ref: str):
    t, b = get_pair(env, ref)
    is_bot = str(s.getValue(b)).lower() == "true"
    if is_bot:
        return None, True
    v = s.getValue(t)
    return bv_to_bits5(str(v)), False


def build_forward_new_iv_enc(mod, rounds_n: int, allow_weak: bool, sum1: bool, monotone_guard: bool, collisions: bool):
    nodes = []
    rounds = []
    rounds.append({"u0": "u0_0", "u1": "u0_1", "u2": "u0_2", "u3": "u0_3"})
    for i in range(rounds_n):
        cur = rounds[-1]
        r_name = f"R_{i}"
        x0_name = f"X0_{i}"  # r_i ⊕ u1
        x1_name = f"X1_{i}"  # r_i ⊕ u2
        nodes.append({"op": "R", "name": r_name, "in": cur["u0"]})
        nodes.append({"op": "XOR", "name": x0_name, "a": r_name, "b": cur["u1"]})
        nodes.append({"op": "XOR", "name": x1_name, "a": r_name, "b": cur["u2"]})
        rounds.append({
            "u0": x0_name,
            "u1": x1_name,
            "u2": cur["u3"],
            "u3": r_name,
        })
    tails = [rounds[-1]["u0"], rounds[-1]["u1"], rounds[-1]["u2"], rounds[-1]["u3"]] if rounds_n > 0 else ["u0_0", "u0_1", "u0_2", "u0_3"]
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


def run_once(mod):
    spec, rounds = build_forward_new_iv_enc(
        mod,
        ROUNDS_N,
        allow_weak=True,
        sum1=True,
        monotone_guard=True,
        collisions=False,
    )
    s, env = mod.build_from_graph(spec)
    inputs = env["inputs"]
    syms = env["syms"]
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[0], syms["ZERO"]))   # u0^0 = 0
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[1], syms["ZERO"]))   # u1^0 = 0
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[2], syms["DELTA"]))  # u2^0 = δ
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[3], syms["X"]))      # u3^0 = x

    res = s.checkSat()
    if str(res).lower() != "sat":
        return False, [f"u{i}^{ROUNDS_N}: ⊥" for i in range(4)]

    has_qd = False
    last_round_lines = []
    for nm in ["u0", "u1", "u2", "u3"]:
        bits, bot = fetch_value_bits(s, env, rounds[ROUNDS_N][nm])
        if bot:
            line = f"{nm}^{ROUNDS_N}: ⊥"
        else:
            sym = bits5_to_symbol(bits)
            line = f"{nm}^{ROUNDS_N}: {sym}"
            if has_quantum_distinguisher(bits):
                has_qd = True
        last_round_lines.append(line)
    return has_qd, last_round_lines


def main():
    mod = load_model(MODEL_DEFAULT)
    total = 0.0
    last_qd = False
    last_round_lines = []

    for _ in range(RUNS):
        t0 = time.perf_counter()
        qd, lines = run_once(mod)
        total += time.perf_counter() - t0
        last_qd = qd
        last_round_lines = lines

    avg = (total / RUNS) * 1000.0

    print(f"Round {ROUNDS_N}:")
    for line in last_round_lines:
        print(line)
    print(f"平均执行时间: {avg:.3f} ms / run over {RUNS} runs")


if __name__ == "__main__":
    main()

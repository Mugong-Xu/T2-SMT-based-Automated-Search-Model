#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from cvc5 import Kind
import importlib.util
import os
import sys
import time

MODEL_PATH = os.path.join(os.path.dirname(__file__), "smt_model_distinguish.py")
if not os.path.exists(MODEL_PATH):
    MODEL_PATH = "smt_model_distinguish.py"

NUM_RUNS = 100
NUM_ROUNDS = 12


def load_user_model(path: str):
    spec = importlib.util.spec_from_file_location("smt_model_distinguish", path)
    if spec is None:
        raise RuntimeError(f"Cannot locate module at {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)  # type: ignore
    return module


# ---------- 打印工具（对齐参考风格） ----------
def decode_symbol_bits(bv_str: str) -> str:
    # 5位: [0]=δ, [1]=R(δ), [2]=x, [3]=R(x), [4]=0s
    if not (isinstance(bv_str, str) and bv_str.startswith("#b")):
        return str(bv_str)
    bits = bv_str[2:].zfill(5)[-5:]
    v = int(bits, 2)
    parts = []
    if v & (1 << 0):
        parts.append("δ")
    if v & (1 << 1):
        parts.append("R(δ)")
    if v & (1 << 2):
        parts.append("x")
    if v & (1 << 3):
        parts.append("R(x)")
    if v & (1 << 4):
        parts.append("0s")
    return " ⊕ ".join(parts) if parts else "0"


def get_pair(env, ref: str):
    outmap, botmap = env["outmap"], env["botmap"]
    if ":" in ref:
        name, idx = ref.split(":")
        idx = int(idx)
    else:
        name, idx = ref, 0
    return outmap[name][idx], botmap[name][idx]


def format_ref_value(s, env, ref: str, label=None) -> str:
    t, b = get_pair(env, ref)
    is_bot = str(s.getValue(b)).lower() == "true"
    if is_bot:
        return f"{label or ref}: ⊥"
    v = s.getValue(t)
    return f"{label or ref}: {v}  => {decode_symbol_bits(str(v))}"


def build_spec():
    nodes = []
    rounds = [{"u0": "u0_0", "u1": "u0_1", "u2": "u0_2", "u3": "u0_3"}]

    for i in range(NUM_ROUNDS):
        cur = rounds[-1]
        r_name = f"R_{i}"
        x_name = f"X_{i}"
        nodes.append({"op": "R", "name": r_name, "in": cur["u0"]})
        nodes.append({"op": "XOR", "name": x_name, "a": r_name, "b": cur["u1"]})
        rounds.append(
            {
                "u0": cur["u3"],
                "u1": r_name,
                "u2": x_name,
                "u3": cur["u2"],
            }
        )

    spec = dict(
        n_inputs=4,
        nodes=nodes,
        tails=[rounds[-1]["u0"], rounds[-1]["u1"], rounds[-1]["u2"], rounds[-1]["u3"]],
        allow_weak=True,
        sum1=True,
        monotone_guard=True,
        collisions=True,
    )
    return spec, rounds


def run_once(mod):
    spec, rounds = build_spec()
    s, env = mod.build_from_graph(spec)

    inputs = env["inputs"]
    syms = env["syms"]
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[0], syms["DELTA"]))
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[1], syms["X"]))
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[2], syms["ZERO"]))
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[3], syms["ZERO"]))

    res = s.checkSat()
    ok = str(res) == "sat"
    if not ok:
        return {
            "check_sat": str(res),
            "ok": False,
            "final_round_index": len(rounds) - 1,
            "final_round_lines": [],
        }

    final_idx = len(rounds) - 1
    final_round = rounds[-1]
    final_round_lines = [
        format_ref_value(s, env, final_round["u0"], label=f"u0^{final_idx}"),
        format_ref_value(s, env, final_round["u1"], label=f"u1^{final_idx}"),
        format_ref_value(s, env, final_round["u2"], label=f"u2^{final_idx}"),
        format_ref_value(s, env, final_round["u3"], label=f"u3^{final_idx}"),
    ]

    return {
        "check_sat": str(res),
        "ok": True,
        "final_round_index": final_idx,
        "final_round_lines": final_round_lines,
    }


def main():
    mod = load_user_model(MODEL_PATH)

    durations = []
    last_result = None

    for _ in range(NUM_RUNS):
        start = time.perf_counter()
        last_result = run_once(mod)
        durations.append(time.perf_counter() - start)

    if last_result is None:
        raise RuntimeError("No run was executed.")

    avg_seconds = sum(durations) / len(durations)

    print(f"执行次数: {NUM_RUNS}")
    print(f"平均耗时: {avg_seconds:.6f} 秒")
    print("check-sat:", last_result["check_sat"])
    print("包含量子区分器？", "是" if last_result["ok"] else "否")

    if last_result["ok"]:
        print(f"\n最后一轮（Round {last_result['final_round_index']}）符号:")
        for line in last_result["final_round_lines"]:
            print(line)


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        print("ERROR:", e)
        sys.exit(1)

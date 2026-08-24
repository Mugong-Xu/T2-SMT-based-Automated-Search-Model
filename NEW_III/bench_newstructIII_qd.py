#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import time, gc, statistics, os, importlib.util
from typing import Dict, Tuple
from cvc5 import Kind

REPEAT = 100
MODEL_PATH = os.path.join(os.path.dirname(__file__), "smt_model_distinguish.py")
MAX_ROUNDS = 13
MIN_ROUNDS = 4
ALLOW_WEAK = True
SUM1 = True
MONOTONE_GUARD = True
COLLISIONS = True

def load_user_model(path: str):
    spec = importlib.util.spec_from_file_location("smt_model_distinguish", path)
    if spec is None:
        raise RuntimeError(f"Cannot locate module at {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)  # type: ignore
    return module

def bv_to_bits5(val_str: str):
    s = str(val_str).strip()
    if s.startswith("#b"):
        bits = s[2:].zfill(5)[-5:]
        return [int(b) for b in bits]
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
        return [None]*5

def bits5_to_symbol(bits):
    if bits is None or any(b is None for b in bits): return "<?>"
    if bits == [0,0,0,0,0]: return "0"
    parts = []
    if bits[4]: parts.append("δ")
    if bits[3]: parts.append("R(δ)")
    if bits[2]: parts.append("x")
    if bits[1]: parts.append("R(x)")
    if bits[0]: parts.append("0s")
    return " ⊕ ".join(parts) if parts else "0"

def is_0s_or_0s_xor_star(bits):
    if bits is None: return False
    if bits == [1,0,0,0,0]: return True
    if bits[0] == 1 and sum(bits[1:]) == 1:
        return True
    return False

def get_pair(env, ref: str):
    outmap, botmap = env["outmap"], env["botmap"]
    if ":" in ref:
        name, idx = ref.split(":"); idx = int(idx)
    else:
        name, idx = ref, 0
    return outmap[name][idx], botmap[name][idx]

def fetch_bits_or_bot(s, env, ref: str):
    t, b = get_pair(env, ref)
    is_bot = (str(s.getValue(b)).lower() == "true")
    if is_bot: return None, True
    v = s.getValue(t)
    return bv_to_bits5(str(v)), False

def build_forward(mod, rounds_n: int):
    nodes = []
    rounds = []
    rounds.append({"u0": "u0_0", "u1": "u0_1", "u2": "u0_2", "u3": "u0_3"})
    for i in range(rounds_n):
        cur = rounds[-1]
        r_name = f"R_{i}"
        x_name = f"X_{i}"
        nodes.append({"op": "R",   "name": r_name, "in": cur["u0"]})
        nodes.append({"op": "XOR", "name": x_name, "a": r_name, "b": cur["u1"]})
        rounds.append({
            "u0": cur["u3"],
            "u1": r_name,
            "u2": x_name,
            "u3": cur["u2"],
        })
    spec = dict(
        n_inputs=4,
        nodes=nodes,
        tails=[rounds[-1]["u0"], rounds[-1]["u1"], rounds[-1]["u2"], rounds[-1]["u3"]] if rounds_n>0 else ["u0_0","u0_1","u0_2","u0_3"],
        allow_weak=ALLOW_WEAK,
        sum1=SUM1,
        monotone_guard=MONOTONE_GUARD,
        collisions=COLLISIONS,
    )
    return spec, rounds

def choose_sat_round_and_forward_table(mod):
    for n in range(MAX_ROUNDS, MIN_ROUNDS-1, -1):
        spec, rounds = build_forward(mod, n)
        s, env = mod.build_from_graph(spec)
        inputs = env["inputs"]; syms = env["syms"]
        s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[0], syms["DELTA"]))
        s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[1], syms["X"]))
        s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[2], syms["ZERO"]))
        s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[3], syms["ZERO"]))
        res = s.checkSat()
        if str(res) == "sat":
            table = {}
            for i in range(0, n+1):
                for nm in ["u0","u1","u2","u3"]:
                    bits, bot = fetch_bits_or_bot(s, env, rounds[i][nm])
                    table[(i,nm)] = None if bot else bits
            return n, (spec, rounds), table
    raise RuntimeError("No SAT round in given range.")

def decrypt_prune_survivor(chosen_rounds: int):
    survivors = {"u0", "u1", "u2", "u3"}
    cur_round = chosen_rounds
    while True:
        if len(survivors) == 1:
            last_nm = next(iter(survivors))
            return cur_round, last_nm
        if cur_round == 0:
            last_nm = sorted(survivors)[0] if survivors else None
            return cur_round, last_nm
        prev_round = cur_round - 1
        next_survivors = set()
        if "u1" in survivors and "u2" in survivors:
            next_survivors.add("u1")
        if "u3" in survivors:
            next_survivors.add("u2")
        if "u0" in survivors:
            next_survivors.add("u3")
        survivors = next_survivors
        cur_round = prev_round

def run_once(mod, chosen_rounds, spec_rounds, forward_table):
    t0 = time.perf_counter()
    spec, rounds = spec_rounds
    s, env = mod.build_from_graph(spec)
    t1 = time.perf_counter()

    inputs = env["inputs"]; syms = env["syms"]
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[0], syms["DELTA"]))
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[1], syms["X"]))
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[2], syms["ZERO"]))
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[3], syms["ZERO"]))
    t2 = time.perf_counter()

    res = s.checkSat()
    t3 = time.perf_counter()

    qd_exists = False
    last_nm = None
    last_symbol = None

    if str(res) == "sat":
        r, nm = decrypt_prune_survivor(chosen_rounds)
        last_nm = f"{nm}^{r}" if nm is not None else None
        bits = forward_table.get((r, nm)) if nm is not None else None
        if bits is not None:
            last_symbol = bits5_to_symbol(bits)
            qd_exists = is_0s_or_0s_xor_star(bits)
        else:
            last_symbol = None
            qd_exists = False

    return {
        "build": t1 - t0,
        "assert": t2 - t1,
        "solve": t3 - t2,
        "total": t3 - t0,
        "qd": qd_exists,
        "last": last_nm,
        "symbol": last_symbol,
        "sat": (str(res) == "sat"),
    }

def main():
    mod = load_user_model(MODEL_PATH)
    chosen_rounds, spec_rounds, forward_table = choose_sat_round_and_forward_table(mod)

    for _ in range(3):
        _ = run_once(mod, chosen_rounds, spec_rounds, forward_table)
        gc.collect()

    builds=[]; asserts=[]; solves=[]; totals=[]; qd_ct=0; sat_ct=0
    last_branch=None; last_symbol=None

    t_all0 = time.perf_counter()
    for _ in range(REPEAT):
        r = run_once(mod, chosen_rounds, spec_rounds, forward_table)
        builds.append(r["build"]); asserts.append(r["assert"]); solves.append(r["solve"]); totals.append(r["total"])
        qd_ct += int(r["qd"]); sat_ct += int(r["sat"])
        last_branch = r["last"]; last_symbol = r["symbol"]
        gc.collect()
    t_all1 = time.perf_counter()

    print(f"Forward 轮数: {chosen_rounds}")
    print(f"重复次数: {REPEAT}")
    print(f"SAT 次数: {sat_ct}/{REPEAT}")
    print(f"量子区分器存在?: {'是' if qd_ct>0 else '否'}")
    print(f"解密-剪枝最终分支: {last_branch}")
    print(f"对应符号: {last_symbol}")
    print("\n== 平均耗时（秒）==")
    import statistics
    print(f"构图        : {statistics.mean(builds):.6f}")
    print(f"初值断言   : {statistics.mean(asserts):.6f}")
    print(f"求解 (SMT) : {statistics.mean(solves):.6f}")
    print(f"总耗时     : {statistics.mean(totals):.6f}")
    print(f"\n整体耗时(含循环开销): {t_all1 - t_all0:.6f} s")

if __name__ == "__main__":
    main()

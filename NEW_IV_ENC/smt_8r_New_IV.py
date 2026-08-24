#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
smt_run_NEW_IV_ENC_auto_decrypt_print_all.py

- 模型：smt_model_distinguish.py
- 结构：NEW_IV_ENC（8 轮）
- 功能：
  1) 约束输入：u0^0=0, u1^0=0, u2^0=δ, u3^0=x
  2) 打印每一轮（0..8）的 smt symbol（含 ⊥ 处理）
  3) 判断第 8 轮是否存在量子区分器（xfam∧dfam）
  4) 执行“解密剪枝”：
     • 特殊规则（仅 8→7）：
         u0^7 = u3^8
         u1^7 = u3^8 ⊕ u0^8
         u2^7 = u3^8 ⊕ u1^8
         u3^7 = u2^8
     • 其他轮（i+1→i）仍使用旧规则：
         u0^i = R^{-1}(u3^{i+1})（结构上不保留该分支）
         u1^i = u3^{i+1} ⊕ u0^{i+1}
         u2^i = u3^{i+1} ⊕ u1^{i+1}
         u3^i = u2^{i+1}
"""

import os, sys, importlib.util
from cvc5 import Kind

MODEL_DEFAULT = os.path.join(os.path.dirname(__file__), "smt_model_distinguish.py")

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
        return [int(b) for b in bits]  # [0s,Rx,x,Rδ,δ] (MSB..LSB)
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
    if bits is None or any(b is None for b in bits):
        return "<?>"
    if bits == [0,0,0,0,0]: return "0"
    parts = []
    if bits[4]: parts.append("δ")
    if bits[3]: parts.append("R(δ)")
    if bits[2]: parts.append("x")
    if bits[1]: parts.append("R(x)")
    if bits[0]: parts.append("0s")
    return " ⊕ ".join(parts) if parts else "0"

def has_quantum_distinguisher(bits):
    if bits is None: return False
    xfam = (bits[2] == 1) or (bits[1] == 1)
    dfam = (bits[4] == 1) or (bits[3] == 1)
    return xfam and dfam

def is_0s_or_0s_xor_star(bits):
    if bits is None: return False
    if bits == [1,0,0,0,0]:  # 0s
        return True
    if bits[0] == 1 and sum(bits[1:]) == 1:  # 0s ⊕ exactly-one-other
        return True
    return False

def get_pair(env, ref: str):
    outmap, botmap = env["outmap"], env["botmap"]
    if ":" in ref:
        name, idx = ref.split(":"); idx = int(idx)
    else:
        name, idx = ref, 0
    return outmap[name][idx], botmap[name][idx]

def fetch_value_bits(s, env, ref: str):
    t, b = get_pair(env, ref)
    is_bot = (str(s.getValue(b)).lower() == "true")
    if is_bot: return None, True
    v = s.getValue(t)
    return bv_to_bits5(str(v)), False

def build_forward_NEW_IV_ENC(mod, rounds_n: int, allow_weak: bool, sum1: bool, monotone_guard: bool, collisions: bool):
    nodes = []
    rounds = []
    rounds.append({"u0": "u0_0", "u1": "u0_1", "u2": "u0_2", "u3": "u0_3"})
    for i in range(rounds_n):
        cur = rounds[-1]
        r_name  = f"R_{i}"
        x0_name = f"X0_{i}"  # r_i ⊕ u1
        x1_name = f"X1_{i}"  # r_i ⊕ u2
        nodes.append({"op":"R",   "name": r_name,  "in": cur["u0"]})
        nodes.append({"op":"XOR", "name": x0_name, "a": r_name,     "b": cur["u1"]})
        nodes.append({"op":"XOR", "name": x1_name, "a": r_name,     "b": cur["u2"]})
        rounds.append({
            "u0": x0_name,
            "u1": x1_name,
            "u2": cur["u3"],
            "u3": r_name,
        })
    tails = [rounds[-1]["u0"], rounds[-1]["u1"], rounds[-1]["u2"], rounds[-1]["u3"]] if rounds_n>0 else ["u0_0","u0_1","u0_2","u0_3"]
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
    mod = load_model(MODEL_DEFAULT)
    rounds_n = 8
    spec, rounds = build_forward_NEW_IV_ENC(
        mod, rounds_n,
        allow_weak=True,
        sum1=True,
        monotone_guard=True,
        collisions=False,
    )
    s, env = mod.build_from_graph(spec)

    inputs = env["inputs"]; syms = env["syms"]
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[0], syms["ZERO"]))   # u0^0 = 0
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[1], syms["ZERO"]))   # u1^0 = 0
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[2], syms["DELTA"]))  # u2^0 = δ
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[3], syms["X"]))      # u3^0 = x

    res = s.checkSat()
    print("check-sat:", res)
    if str(res).lower() != "sat":
        print("UNSAT/UNKNOWN under given constraints.")
        return

    # (A) 每一轮打印（0..8）
    print("\n=== 每一轮的 SMT symbol ===")
    for i in range(0, rounds_n+1):
        nm_list = ["u0","u1","u2","u3"]
        vals = []
        for nm in nm_list:
            bits, bot = fetch_value_bits(s, env, rounds[i][nm])
            sym = "⊥" if bot else bits5_to_symbol(bits)
            vals.append(sym)
        print(f"Round {i}:  u0={vals[0]}, u1={vals[1]}, u2={vals[2]}, u3={vals[3]}")

    # (B) 第 8 轮是否量子区分器
    has_qd = False
    for nm in ["u0","u1","u2","u3"]:
        bits, bot = fetch_value_bits(s, env, rounds[rounds_n][nm])
        if not bot and has_quantum_distinguisher(bits):
            has_qd = True
            break
    print(f"\n[判断] 8 轮 NEW_IV_ENC 量子区分器是否存在？ => {'是' if has_qd else '否'}")

    # (C) 解密剪枝（结构）——按你的新规则对 8→7 特判，其余沿用旧规则
    survivors = {"u0","u1","u2","u3"}
    cur = rounds_n
    print(f"\n解密剪枝（仅结构存活集合）：")
    print(f"Round {cur}: survivors -> [{', '.join(sorted(survivors))}]")

    while cur > 0:
        prev = cur - 1
        nxt = set()

        if cur == 8:
            # 特殊：8→7
            # u0^7 ← u3^8
            if "u3" in survivors: nxt.add("u0")
            # u1^7 ← u3^8 ⊕ u0^8
            if "u3" in survivors and "u0" in survivors: nxt.add("u1")
            # u2^7 ← u3^8 ⊕ u1^8
            if "u3" in survivors and "u1" in survivors: nxt.add("u2")
            # u3^7 ← u2^8
            if "u2" in survivors: nxt.add("u3")
        else:
            # 旧规则：i+1→i
            # u0^i = R^{-1}(u3^{i+1}) —— 我们不保留该逆分支
            # u1^i ← u3^{i+1} ⊕ u0^{i+1}
            if "u3" in survivors and "u0" in survivors: nxt.add("u1")
            # u2^i ← u3^{i+1} ⊕ u1^{i+1}
            if "u3" in survivors and "u1" in survivors: nxt.add("u2")
            # u3^i ← u2^{i+1}
            if "u2" in survivors: nxt.add("u3")

        survivors = nxt
        cur = prev
        print(f"Round {cur}: survivors -> [{', '.join(sorted(survivors))}]")

        if len(survivors) == 1:
            last = next(iter(survivors))
            bits, bot = fetch_value_bits(s, env, rounds[cur][last])
            if bot:
                print(f"\n终止：仅剩 {last}^{cur} = ⊥  => 非区分型")
            else:
                sym = bits5_to_symbol(bits)
                ok = is_0s_or_0s_xor_star(bits)
                print(f"\n终止：仅剩 {last}^{cur} = {sym} ，是否 0s 或 0s⊕*：{'是' if ok else '否'}")
            break

if __name__ == "__main__":
    main()

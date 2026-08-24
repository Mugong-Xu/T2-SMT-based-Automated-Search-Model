#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Auto-SAT forward builder + decrypt-prune for new_structure_III

- Tries forward rounds from --max-rounds down to --min-rounds until check-sat.
- Once SAT, saves every round's u0..u3 bit-vectors and human-readable symbols.
- Then treats that final round as "ciphertext" and runs the decrypt+prune procedure:
    u0^i = R^{-1}(u1^{i+1})  -> DROP
    u1^i = u1^{i+1} ⊕ u2^{i+1} -> KEEP (if both survive and non-⊥)
    u2^i = u3^{i+1}            -> KEEP (permutation)
    u3^i = u0^{i+1}            -> KEEP (permutation)
  Continue until only one non-⊥ branch remains and it is 0s or 0s ⊕ *.
- Does NOT modify smt_model_distinguish.py.
"""

import argparse, os, sys
import importlib.util
from cvc5 import Kind

MODEL_PATH_DEFAULT = os.path.join(os.path.dirname(__file__), "smt_model_distinguish.py")

def load_user_model(path: str):
    spec = importlib.util.spec_from_file_location("smt_model_distinguish", path)
    if spec is None:
        raise RuntimeError(f"Cannot locate module at {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)  # type: ignore
    return module

# ---------- utilities ----------
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

def xor_no_collision(a_bits, b_bits):
    if a_bits is None or b_bits is None:
        return None
    out = [0]*5  # [0s,Rx,x,Rδ,δ]
    out[0] = 1 if (a_bits[0] or b_bits[0]) else 0  # 0s OR
    out[1] = 1 if (a_bits[1] or b_bits[1]) else 0  # Rx OR
    out[2] = (a_bits[2] ^ b_bits[2])               # x XOR
    out[3] = 1 if (a_bits[3] or b_bits[3]) else 0  # Rδ OR
    out[4] = 1 if (a_bits[4] or b_bits[4]) else 0  # δ  OR
    return out


def has_quantum_distinguisher(bits):
    # Define "量子区分器" as a MIX: contains at least one x-family bit and one δ-family bit
    # x-family: x (idx 2) or R(x) (idx 1)
    # δ-family: δ (idx 4) or R(δ) (idx 3)
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

# ---------- forward graph builder ----------
def build_forward(mod, rounds_n: int, allow_weak: bool, sum1: bool, monotone_guard: bool, collisions: bool):
    nodes = []
    rounds = []  # round i -> {"u0","u1","u2","u3"} refs
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
        tails=[rounds[-1]["u0"], rounds[-1]["u1"], rounds[-1]["u2"], rounds[-1]["u3"]] if rounds_n>0 else ["u0_0","u0_1","u0_2","u0_3"],  # bind to final round
        allow_weak=allow_weak,
        sum1=sum1,
        monotone_guard=monotone_guard,
        collisions=collisions,
    )
    # Fix a typo if any (safe guard)
    if "tails" in spec and isinstance(spec["tails"], list):
        pass
    return spec, rounds

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", default=MODEL_PATH_DEFAULT, help="Path to smt_model_distinguish.py")
    ap.add_argument("--max-rounds", type=int, default=13)
    ap.add_argument("--min-rounds", type=int, default=4)
    ap.add_argument("--allow-weak", type=int, default=1)   # 1/0
    ap.add_argument("--sum1", type=int, default=1)
    ap.add_argument("--monotone-guard", type=int, default=1)
    ap.add_argument("--collisions", type=int, default=1)
    args = ap.parse_args()

    mod = load_user_model(args.model)

    chosen_rounds = None
    env = None
    s = None
    rounds_refs = None

    for rounds_n in range(args.max_rounds, args.min_rounds-1, -1):
        print(f"尝试正向轮数: {rounds_n}")
        spec, rounds = build_forward(mod, rounds_n,
                                     bool(args.allow_weak),
                                     bool(args.sum1),
                                     bool(args.monotone_guard),
                                     bool(args.collisions))
        s, env = mod.build_from_graph(spec)

        inputs = env["inputs"]; syms = env["syms"]
        s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[0], syms["DELTA"]))  # u0^0 = δ
        s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[1], syms["X"]))      # u1^0 = x
        s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[2], syms["ZERO"]))   # u2^0 = 0
        s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[3], syms["ZERO"]))   # u3^0 = 0

        res = s.checkSat()
        print("  check-sat:", res)
        if str(res) == "sat":
            chosen_rounds = rounds_n
            rounds_refs = rounds
            print(f"  选定轮数 = {chosen_rounds}")
            break

    if chosen_rounds is None:
        print("在给定范围内未找到 SAT 的轮数。")
        sys.exit(2)

    # ---------- save all rounds (0..chosen_rounds) symbols ----------
    print("\n保存每一轮的符号：")
    out_lines = []
    forward_syms = {}  # key: (i,'u0'..'u3') -> bits list
    for i in range(0, chosen_rounds+1):
        refs = rounds_refs[i]
        bits_u = []; sym_u = []
        print(f"\nRound {i}:")
        for nm in ["u0","u1","u2","u3"]:
            bits, bot = fetch_value_bits(s, env, refs[nm])
            if bot:
                print(f"  {nm}^{i}: ⊥")
                out_lines.append(f"{i},{nm},BOT,⊥")
            else:
                sym = bits5_to_symbol(bits)
                print(f"  {nm}^{i}: {bits}  => {sym}")
                out_lines.append(f"{i},{nm},{''.join(map(str,bits))},{sym}")
                forward_syms[(i,nm)] = bits

    out_txt = os.path.join(os.path.dirname(__file__), f"forward_rounds_symbols_{chosen_rounds}.csv")
    with open(out_txt, "w", encoding="utf-8") as f:
        f.write("round,wire,bits(0sRxxRδδ),symbol\n")
        f.write("\n".join(out_lines))
    print(f"\n已保存：{out_txt}")


    # ---------- decrypt + prune from the chosen ciphertext round (STRUCTURAL) ----------
    print(f"\n从 Round {chosen_rounds} 作为密文开始解密并剪枝（只打印每轮存活分支）：")

    # Start with all four ciphertext branches structurally present
    survivors = {"u0", "u1", "u2", "u3"}
    cur_round = chosen_rounds
    print(f"Round {cur_round}: survivors -> [{', '.join(sorted(survivors))}]")

    while True:
        if cur_round == 0:
            break
        prev_round = cur_round - 1
        next_survivors = set()
        # 规则：
        # 1) u0^i = R^{-1}(u1^{i+1}) -> 丢弃（不加入）
        # 2) u1^i = u1^{i+1} ⊕ u2^{i+1} -> 若 u1 与 u2 都在当前存活集合中，则保留 u1
        if "u1" in survivors and "u2" in survivors:
            next_survivors.add("u1")
        # 3) u2^i = u3^{i+1} -> 若 u3 存活，则保留 u2
        if "u3" in survivors:
            next_survivors.add("u2")
        # 4) u3^i = u0^{i+1} -> 若 u0 存活，则保留 u3
        if "u0" in survivors:
            next_survivors.add("u3")

        survivors = next_survivors
        cur_round = prev_round
        print(f"Round {cur_round}: survivors -> [{', '.join(sorted(survivors))}]")

        if len(survivors) == 1:
            last_nm = next(iter(survivors))
            # 查同一轮同一分支的前向符号，并判断是否 0s 或 0s xor *
            fbits = forward_syms.get((cur_round, last_nm))
            if fbits is not None:
                sym = bits5_to_symbol(fbits)
                ok = is_0s_or_0s_xor_star(fbits)
                print(f"\n终止：仅剩 {last_nm}^{cur_round}；正向符号 = {sym}；是否 0s 或 0s ⊕ *：{'是' if ok else '否'}")
            else:
                print(f"\n终止：仅剩 {last_nm}^{cur_round}；但在前向符号表中未找到其符号。")
            break

if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        print("ERROR:", e)
        sys.exit(1)

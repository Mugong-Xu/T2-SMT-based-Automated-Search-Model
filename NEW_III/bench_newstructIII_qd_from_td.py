#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import time, gc, statistics, os, importlib.util
from typing import Dict, Tuple, List, Optional
from cvc5 import Kind

# ===== Settings =====
REPEAT = 100
MODEL_PATH = os.path.join(os.path.dirname(__file__), "smt_model_distinguish.py")
MAX_ROUNDS = 13
ALLOW_WEAK = True
SUM1 = True
MONOTONE_GUARD = True
COLLISIONS = True

# ===== Load modules =====
def load_user_model(path: str):
    spec = importlib.util.spec_from_file_location("smt_model_distinguish", path)
    if spec is None:
        raise RuntimeError(f"Cannot locate module at {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)  # type: ignore
    return module

def load_td_trunc():
    td_path = os.path.join(os.path.dirname(__file__), "td_trunc.py")
    spec = importlib.util.spec_from_file_location("td_trunc", td_path)
    if spec is None:
        raise RuntimeError("Cannot locate td_trunc.py")
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)  # type: ignore
    return m

# ===== Bit-mask helpers =====
def bv_to_bits5(bv_str: str) -> List[int]:
    s = str(bv_str).strip()
    if s.startswith("#b"):
        bits = s[2:].zfill(5)[-5:]
        return [int(b) for b in bits]  # [0s,Rx,x,Rδ,δ]
    if s.startswith("(_ bv"):
        parts = s.replace("(", "").replace(")", "").split()
        n = int(parts[1][2:]) if parts[1].startswith("bv") else int(parts[1])
        bs = bin(n)[2:].zfill(5)[-5:]
        return [int(b) for b in bs]
    n = int(s)
    bs = bin(n)[2:].zfill(5)[-5:]
    return [int(b) for b in bs]

def bits5_to_symbol(bits: Optional[List[int]]) -> str:
    if bits is None: return "<?>"
    if bits == [0,0,0,0,0]: return "0"
    parts = []
    if bits[4]: parts.append("δ")
    if bits[3]: parts.append("R(δ)")
    if bits[2]: parts.append("x")
    if bits[1]: parts.append("R(x)")
    if bits[0]: parts.append("0s")
    return " ⊕ ".join(parts) if parts else "0"

def is_0s_or_0s_xor_star(bits: Optional[List[int]]) -> bool:
    # 0s alone OR 0s with exactly one other bit
    if bits is None: return False
    if bits == [1,0,0,0,0]: return True
    if bits[0] == 1 and sum(bits[1:]) == 1: return True
    return False

# ===== Forward new structure III (SMT) =====
def build_spec_newstructIII_13r():
    nodes = []
    rounds = []  # round i -> refs for u0..u3
    rounds.append({"u0": "u0_0", "u1": "u0_1", "u2": "u0_2", "u3": "u0_3"})
    for i in range(MAX_ROUNDS):
        cur = rounds[-1]
        r_name = f"R_{i}"
        x_name = f"X_{i}"
        # u1^{i+1} = R(u0^i)
        nodes.append({"op": "R", "name": r_name, "in": cur["u0"]})
        # u2^{i+1} = R(u0^i) ⊕ u1^i
        nodes.append({"op": "XOR", "name": x_name, "a": r_name, "b": cur["u1"]})
        # next wires
        rounds.append({
            "u0": cur["u3"],   # permutation
            "u1": r_name,      # R(u0)
            "u2": x_name,      # XOR(R(u0), u1)
            "u3": cur["u2"],   # permutation
        })
    spec = dict(
        n_inputs=4,
        nodes=nodes,
        tails=[rounds[-1]["u0"], rounds[-1]["u1"], rounds[-1]["u2"], rounds[-1]["u3"]],
        allow_weak=ALLOW_WEAK,
        sum1=SUM1,
        monotone_guard=MONOTONE_GUARD,
        collisions=COLLISIONS,
    )
    return spec, rounds

# ===== TD simulate 13r of new structure III and find anchor (no STAR round) =====
def simulate_td_and_find_anchor(td, init=(None,None,None,None)):
    # init on TD domain: u0^0=δ→A, u1^0=x→S, u2^0=0→Z, u3^0=0→Z
    Z, A, S = td.Z, td.A, td.S
    if init == (None,None,None,None):
        u0,u1,u2,u3 = A, S, Z, Z
    else:
        u0,u1,u2,u3 = init
    eng = td.TDEngine()
    hist = [(u0,u1,u2,u3)]
    for _ in range(MAX_ROUNDS):
        # new structure III forward
        u0n = td.copy_val(u3)       # u0' = u3
        Ru0 = eng.R(u0)            # R(u0)
        u1n = Ru0                  # u1' = R(u0)
        u2n = eng.xor2(Ru0, u1)    # u2' = R(u0) ⊕ u1
        u3n = td.copy_val(u2)      # u3' = u2
        u0,u1,u2,u3 = u0n,u1n,u2n,u3n
        hist.append((u0,u1,u2,u3))
    # find a latest anchor round with no STAR
    def no_star(vs): return all(v.sym != td.Sym.STAR for v in vs)
    for r in range(MAX_ROUNDS, -1, -1):
        if no_star(hist[r]):
            return r, hist
    return None, hist

# mapping TD Val -> SMT mask (5 bits)
def td_to_smt_mask(td, v) -> Optional[int]:
    Sym = td.Sym
    # You can refine mapping based on your td_trunc design
    if v.sym == Sym.ZERO:    return 0b00000
    if v.sym == Sym.ZERO_S:  return 0b10000       # 0s
    if v.sym == Sym.S:       return 0b00100       # x
    if v.sym == Sym.AS:      return 0b00101       # x ⊕ δ
    if v.sym == Sym.A:
        # A may annotate 0s or not; use a_flag if available
        a_flag = getattr(v, "a_flag", 0)
        return (0b10001 if a_flag==1 else 0b00001)  # δ or 0s⊕δ
    if v.sym == Sym.STAR:    return None
    return None

# structural decrypt-prune: start at round 13 and go up until 1 survivor
def decrypt_prune_survivor():
    survivors = {"u0","u1","u2","u3"}
    cur_round = MAX_ROUNDS
    while True:
        if len(survivors) == 1:
            nm = next(iter(survivors))
            return cur_round, nm
        if cur_round == 0:
            nm = sorted(survivors)[0] if survivors else None
            return cur_round, nm
        prev = cur_round - 1
        next_surv = set()
        # 1) u0^i = R^{-1}(u1^{i+1}) -> drop
        # 2) u1^i = u1^{i+1} ⊕ u2^{i+1} -> keep u1 if both present
        if "u1" in survivors and "u2" in survivors:
            next_surv.add("u1")
        # 3) u2^i = u3^{i+1} -> keep u2 if u3 present
        if "u3" in survivors:
            next_surv.add("u2")
        # 4) u3^i = u0^{i+1} -> keep u3 if u0 present
        if "u0" in survivors:
            next_surv.add("u3")
        survivors = next_surv
        cur_round = prev

def main():
    # Prepare
    td = load_td_trunc()
    mod = load_user_model(MODEL_PATH)

    # TD simulate 13r and choose anchor without STAR
    r_anchor, hist = simulate_td_and_find_anchor(td)
    if r_anchor is None:
        print("未找到无 * 的锚点轮（TD 域）。退出。")
        return

    # Precompute masks to pin at anchor
    anchor_masks = []
    for w in range(4):
        m = td_to_smt_mask(td, hist[r_anchor][w])
        if m is None:
            print("锚点轮存在 *，不应发生。退出。")
            return
        anchor_masks.append(m)

    # Build once the 13r spec (reused across runs)
    spec, rounds = build_spec_newstructIII_13r()

    # Warmup
    for _ in range(3):
        s, env = mod.build_from_graph(spec)
        mkbv = lambda x: s.mkBitVector(5, x)
        # pin anchor
        for w, nm in enumerate(["u0","u1","u2","u3"]):
            ref = (f"u0_{w}" if r_anchor==0 else rounds[r_anchor][nm])
            s.assertFormula(s.mkTerm(Kind.EQUAL, env["outmap"][ref][0], mkbv(anchor_masks[w])))
        _ = s.checkSat()
        gc.collect()

    builds=[]; asserts=[]; solves=[]; totals=[]
    qd_exists=False; last_branch=None; last_symbol=None

    T0 = time.perf_counter()
    for _ in range(REPEAT):
        t0 = time.perf_counter()
        s, env = mod.build_from_graph(spec)
        t1 = time.perf_counter()

        mkbv = lambda x: s.mkBitVector(5, x)
        # pin anchor round masks
        for w, nm in enumerate(["u0","u1","u2","u3"]):
            ref = (f"u0_{w}" if r_anchor==0 else rounds[r_anchor][nm])
            s.assertFormula(s.mkTerm(Kind.EQUAL, env["outmap"][ref][0], mkbv(anchor_masks[w])))
        t2 = time.perf_counter()

        res = s.checkSat()
        t3 = time.perf_counter()

        # Read forward mask for the decrypt-prune survivor
        survivor_round, survivor_nm = decrypt_prune_survivor()
        if survivor_nm is not None:
            ref = rounds[survivor_round][survivor_nm]
            is_bot = s.getValue(env["botmap"][ref][0])
            if str(is_bot).lower() == "true":
                bits = None
            else:
                v = s.getValue(env["outmap"][ref][0])
                bits = bv_to_bits5(str(v))
            if bits is not None:
                last_symbol = bits5_to_symbol(bits)
                qd_exists = is_0s_or_0s_xor_star(bits)
                last_branch = f"{survivor_nm}^{survivor_round}"
            else:
                last_symbol = None
                last_branch = f"{survivor_nm}^{survivor_round}"
                qd_exists = False
        else:
            last_branch = None
            last_symbol = None
            qd_exists = False

        builds.append(t1-t0); asserts.append(t2-t1); solves.append(t3-t2); totals.append(t3-t0)
        gc.collect()
    T1 = time.perf_counter()

    # Output summary
    print(f"TD 锚点轮: Round {r_anchor}")
    print(f"重复次数: {REPEAT}")
    print(f"量子区分器存在?: {'是' if qd_exists else '否'}")
    print(f"解密-剪枝最终分支: {last_branch}")
    print(f"对应符号: {last_symbol}")
    print("\n== 平均耗时（秒）==")
    print(f"构图        : {statistics.mean(builds):.6f}")
    print(f"锚点断言   : {statistics.mean(asserts):.6f}")
    print(f"求解 (SMT) : {statistics.mean(solves):.6f}")
    print(f"总耗时     : {statistics.mean(totals):.6f}")
    print(f"\n整体耗时(含循环开销): {T1 - T0:.6f} s")

if __name__ == "__main__":
    main()

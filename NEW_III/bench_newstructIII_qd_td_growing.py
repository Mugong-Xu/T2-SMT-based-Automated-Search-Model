#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import time, gc, statistics, os, importlib.util
from typing import List, Optional, Tuple
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

# ===== Bit helpers =====
def bv_to_bits5(bv_str: str) -> List[int]:
    s = str(bv_str).strip()
    if s.startswith("#b"):
        bits = s[2:].zfill(5)[-5:]
        return [int(b) for b in bits]
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
    if bits is None: return False
    if bits == [1,0,0,0,0]: return True
    if bits[0] == 1 and sum(bits[1:]) == 1: return True
    return False

# ===== TD simulate forward; find growing anchor =====
def find_growing_anchor(td) -> Optional[Tuple[int,int]]:
    """Return (anchor_round, branch_idx) where anchor_round=r-1 and branch_idx in {0,1,2,3}.
       Condition: round r is all STAR, and round r-1 has at least one ZERO_S (0_s).
       TD init: u0^0=A (δ), u1^0=S (x), u2^0=Z (0), u3^0=Z (0).
    """
    Z, A, S = td.Z, td.A, td.S
    u0,u1,u2,u3 = A, S, Z, Z
    eng = td.TDEngine()
    hist = [(u0,u1,u2,u3)]
    for i in range(1, MAX_ROUNDS+1):
        # forward new structure III
        u0n = td.copy_val(u3)       # u0' = u3
        Ru0 = eng.R(u0)
        u1n = Ru0                   # u1' = R(u0)
        u2n = eng.xor2(Ru0, u1)     # u2' = R(u0) ⊕ u1
        u3n = td.copy_val(u2)       # u3' = u2
        u0,u1,u2,u3 = u0n,u1n,u2n,u3n
        hist.append((u0,u1,u2,u3))
        # check stop condition at round i
        all_star = all(v.sym == td.Sym.STAR for v in hist[i])
        zero_s_idx = [idx for idx,v in enumerate(hist[i-1]) if v.sym == td.Sym.ZERO_S] if i-1 >= 0 else []
        if all_star and zero_s_idx:
            return (i-1, zero_s_idx[0])
    return None

# ===== Build suffix SMT from anchor round to 13 =====
def build_spec_suffix_from_anchor(anchor_round: int):
    steps = MAX_ROUNDS - anchor_round
    nodes = []
    rounds = []
    rounds.append({"u0": "u0_0", "u1": "u0_1", "u2": "u0_2", "u3": "u0_3"})  # anchor wires
    for k in range(steps):
        cur = rounds[-1]
        r_name = f"R_suf_{anchor_round+k}"
        x_name = f"X_suf_{anchor_round+k}"
        nodes.append({"op": "R",   "name": r_name, "in": cur["u0"]})
        nodes.append({"op": "XOR", "name": x_name, "a": r_name, "b": cur["u1"]})
        rounds.append({
            "u0": cur["u3"],
            "u1": r_name,
            "u2": x_name,
            "u3": cur["u2"],
        })
    tails = [rounds[-1]["u0"], rounds[-1]["u1"], rounds[-1]["u2"], rounds[-1]["u3"]]
    spec = dict(
        n_inputs=4,
        nodes=nodes,
        tails=tails,
        allow_weak=ALLOW_WEAK,
        sum1=SUM1,
        monotone_guard=MONOTONE_GUARD,
        collisions=COLLISIONS,
    )
    return spec, rounds

# ===== Structural decrypt-prune =====
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
        if "u1" in survivors and "u2" in survivors:
            next_surv.add("u1")
        if "u3" in survivors:
            next_surv.add("u2")
        if "u0" in survivors:
            next_surv.add("u3")
        survivors = next_surv
        cur_round = prev

def main():
    # 1) TD: find growing anchor
    td = load_td_trunc()
    anchor = find_growing_anchor(td)
    if anchor is None:
        print("未找到满足条件的锚点（上一轮含 0_s，且当前轮全为 *）。退出。")
        return
    anchor_round, branch_idx = anchor  # 0->u0,1->u1,2->u2,3->u3

    # 2) SMT suffix: build once
    mod = load_user_model(MODEL_PATH)
    spec, rounds = build_spec_suffix_from_anchor(anchor_round)

    mask_0s = 0b10000  # SMT 0s

    # Warmup
    for _ in range(3):
        s, env = mod.build_from_graph(spec)
        mkbv = lambda x: s.mkBitVector(5, x)
        s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][branch_idx], mkbv(mask_0s)))
        _ = s.checkSat()
        gc.collect()

    builds=[]; asserts=[]; solves=[]; totals=[]
    qd_exists=False; last_branch=None; last_symbol=None; last_status="not-run"

    T0 = time.perf_counter()
    for _ in range(REPEAT):
        t0 = time.perf_counter()
        s, env = mod.build_from_graph(spec)
        t1 = time.perf_counter()

        mkbv = lambda x: s.mkBitVector(5, x)
        s.assertFormula(s.mkTerm(Kind.EQUAL, env["inputs"][branch_idx], mkbv(mask_0s)))
        t2 = time.perf_counter()

        res = s.checkSat()
        last_status = str(res)
        t3 = time.perf_counter()

        # cvc5 model values are only available after SAT (or UNKNOWN).  This
        # growing-anchor configuration can be UNSAT, so record that outcome
        # instead of querying a non-existent model.
        if str(res).lower() != "sat":
            last_branch = None
            last_symbol = None
            qd_exists = False
            builds.append(t1-t0); asserts.append(t2-t1); solves.append(t3-t2); totals.append(t3-t0)
            gc.collect()
            continue

        survivor_round, survivor_nm = decrypt_prune_survivor()
        if survivor_nm is not None:
            ref = rounds[-1][survivor_nm]
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

    print(f"TD 锚点：Round {anchor_round}, 分支 u{branch_idx}")
    print(f"重复次数: {REPEAT}")
    print(f"SMT 结果: {last_status}")
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

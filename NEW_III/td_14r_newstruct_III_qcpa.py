#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import importlib.util, os, time
from typing import Tuple, Optional

MAX_ROUNDS = 13


def load_td_trunc():
    td_path = os.path.join(os.path.dirname(__file__), "td_trunc.py")
    spec = importlib.util.spec_from_file_location("td_trunc", td_path)
    if spec is None:
        raise RuntimeError("Cannot locate td_trunc.py")
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)  # type: ignore
    return m


def simulate_newstructIII_13(td):
    """Return history list of length 14: round 0..13, each a tuple(u0,u1,u2,u3)."""
    Z, A, S = td.Z, td.A, td.S
    u0, u1, u2, u3 = A, S, Z, Z  # δ, x, 0, 0
    eng = td.TDEngine()
    hist = [(u0, u1, u2, u3)]
    for _ in range(MAX_ROUNDS):
        u0n = td.copy_val(u3)         # u0' = u3
        Ru0 = eng.R(u0)               # R(u0)
        u1n = Ru0                     # u1' = R(u0)
        u2n = eng.xor2(Ru0, u1)       # u2' = R(u0) ⊕ u1
        u3n = td.copy_val(u2)         # u3' = u2
        u0, u1, u2, u3 = u0n, u1n, u2n, u3n
        hist.append((u0, u1, u2, u3))
    return hist


def find_anchor(td, hist) -> Optional[Tuple[int, int]]:
    """Find first r (from 1..13) such that round r all STAR, and round r-1 has at least one ZERO_S.
       Return (anchor_round=r-1, branch_idx in 0..3).
    """
    for r in range(1, MAX_ROUNDS + 1):
        all_star = all(v.sym == td.Sym.STAR for v in hist[r])
        if not all_star:
            continue
        prev = hist[r - 1]
        zero_s = [i for i, v in enumerate(prev) if v.sym == td.Sym.ZERO_S]
        if zero_s:
            return (r - 1, zero_s[0])
    return None


def decrypt_prune_survivor():
    """Pure structural decrypt-prune from round 13 down to 0; return (round_index, 'u0'|'u1'|'u2'|'u3')."""
    survivors = {"u0", "u1", "u2", "u3"}
    cur_round = MAX_ROUNDS
    while True:
        if len(survivors) == 1:
            return (cur_round, next(iter(survivors)))
        if cur_round == 0:
            return (cur_round, sorted(survivors)[0])
        prev = cur_round - 1
        next_surv = set()
        # 1) u0^i = R^{-1}(u1^{i+1}) -> DROP
        # 2) u1^i = u1^{i+1} ⊕ u2^{i+1} -> KEEP if both present
        if "u1" in survivors and "u2" in survivors:
            next_surv.add("u1")
        # 3) u2^i = u3^{i+1} -> KEEP if u3 present
        if "u3" in survivors:
            next_surv.add("u2")
        # 4) u3^i = u0^{i+1} -> KEEP if u0 present
        if "u0" in survivors:
            next_surv.add("u3")
        survivors = next_surv
        cur_round = prev


def td_val_to_str(v) -> str:
    return str(v)


def print_td_history(hist):
    print("TD 逐轮符号传播：")
    for i, (u0, u1, u2, u3) in enumerate(hist):
        print(f"Round {i}:")
        print(f"  u0^{i}: {td_val_to_str(u0)}")
        print(f"  u1^{i}: {td_val_to_str(u1)}")
        print(f"  u2^{i}: {td_val_to_str(u2)}")
        print(f"  u3^{i}: {td_val_to_str(u3)}")


def get_branch_value(hist, round_idx: int, branch_name: str):
    branch_idx = int(branch_name[1])
    return hist[round_idx][branch_idx]


def main():
    td = load_td_trunc()

    t0 = time.perf_counter()
    hist = simulate_newstructIII_13(td)
    anchor = find_anchor(td, hist)
    surv_round, surv_nm = decrypt_prune_survivor()
    surv_val = get_branch_value(hist, surv_round, surv_nm)
    t1 = time.perf_counter()

    print_td_history(hist)

    print("\n剪枝技术输出：")
    print(f"最终剩余分支: {surv_nm}^{surv_round}")
    print(f"该分支对应 TD 符号: {td_val_to_str(surv_val)}")

    if anchor is not None:
        anchor_round, branch_idx = anchor
        print(f"锚点分支: u{branch_idx}^{anchor_round}")
        print(f"锚点符号: {td_val_to_str(hist[anchor_round][branch_idx])}")
        is_same_branch = (surv_round == anchor_round) and (surv_nm == f"u{branch_idx}")
        is_zero_s = (hist[anchor_round][branch_idx].sym == td.Sym.ZERO_S)
        print(f"量子区分器存在?: {'是' if (is_same_branch and is_zero_s) else '否'}")
    else:
        print("锚点分支: 无")
        print("锚点符号: 无")
        print("量子区分器存在?: 否")

    print(f"\n单次运行耗时: {t1 - t0:.6f} s")


if __name__ == "__main__":
    main()

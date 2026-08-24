#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import importlib.util, os, time, statistics, gc
from typing import List, Tuple, Optional

MAX_ROUNDS = 13
REPEAT = 100

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
    u0,u1,u2,u3 = A, S, Z, Z  # δ, x, 0, 0
    eng = td.TDEngine()
    hist = [(u0,u1,u2,u3)]
    for _ in range(MAX_ROUNDS):
        u0n = td.copy_val(u3)         # u0' = u3
        Ru0 = eng.R(u0)               # R(u0)
        u1n = Ru0                     # u1' = R(u0)
        u2n = eng.xor2(Ru0, u1)       # u2' = R(u0) ⊕ u1
        u3n = td.copy_val(u2)         # u3' = u2
        u0,u1,u2,u3 = u0n,u1n,u2n,u3n
        hist.append((u0,u1,u2,u3))
    return hist

def find_anchor(td, hist) -> Optional[Tuple[int,int]]:
    """Find first r (from 1..13) such that round r all STAR, and round r-1 has at least one ZERO_S.
       Return (anchor_round=r-1, branch_idx in 0..3).
    """
    for r in range(1, MAX_ROUNDS+1):
        all_star = all(v.sym == td.Sym.STAR for v in hist[r])
        if not all_star:
            continue
        prev = hist[r-1]
        zero_s = [i for i,v in enumerate(prev) if v.sym == td.Sym.ZERO_S]
        if zero_s:
            return (r-1, zero_s[0])
    return None

def decrypt_prune_survivor():
    """Pure structural decrypt-prune from round 13 down to 0; return (round_index, 'u0'|'u1'|'u2'|'u3')."""
    survivors = {"u0","u1","u2","u3"}
    cur_round = MAX_ROUNDS
    while True:
        if len(survivors) == 1:
            return (cur_round, next(iter(survivors)))
        if cur_round == 0:
            # If never got to 1 survivor, pick lexicographically (shouldn't happen for this structure)
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

def main():
    td = load_td_trunc()

    # Warmup (not counted)
    for _ in range(3):
        hist = simulate_newstructIII_13(td)
        anchor = find_anchor(td, hist)
        _ = decrypt_prune_survivor()
        gc.collect()

    totals = []
    final_branch = None
    final_round = None
    qd_exists_any = False

    t_all0 = time.perf_counter()
    for _ in range(REPEAT):
        t0 = time.perf_counter()

        # TD simulate and find anchor
        hist = simulate_newstructIII_13(td)
        anchor = find_anchor(td, hist)
        if anchor is None:
            # No such anchor in this configuration; mark as no QD
            totals.append(time.perf_counter() - t0)
            gc.collect()
            continue
        anchor_round, branch_idx = anchor
        # survivor by structural decrypt-prune
        surv_round, surv_nm = decrypt_prune_survivor()

        # we "converted" ZERO_S -> SMT 0s notionally; check the survivor is exactly that branch/round
        branch_name = f"u{branch_idx}"
        is_same_branch = (surv_round == anchor_round) and (surv_nm == branch_name)

        # symbol check at anchor: in TD domain, ZERO_S corresponds to SMT '0s'
        is_zero_s = (hist[anchor_round][branch_idx].sym == td.Sym.ZERO_S)
        # TD 没有“0s ⊕ *”这种复合显式表示，因此只需 is_zero_s
        qd_ok = is_same_branch and is_zero_s

        if qd_ok:
            qd_exists_any = True
            final_branch = f"{branch_name}^{anchor_round}"
            final_round = anchor_round

        totals.append(time.perf_counter() - t0)
        gc.collect()
    t_all1 = time.perf_counter()

    avg_total = statistics.mean(totals) if totals else 0.0
    print(f"重复次数: {REPEAT}")
    print(f"量子区分器存在?: {'是' if qd_exists_any else '否'}")
    if final_branch is not None:
        print(f"解密-剪枝最终分支: {final_branch}")
        print(f"对应符号: 0s")
    else:
        print("解密-剪枝最终分支: 无")
        print("对应符号: 无")
    print("\n== 平均耗时（秒）==")
    print(f"总耗时     : {avg_total:.6f}")
    print(f"\n整体耗时(含循环开销): {t_all1 - t_all0:.6f} s")

if __name__ == "__main__":
    main()

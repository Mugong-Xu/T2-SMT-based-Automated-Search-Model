#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
bench_td_only_NEW_IV_ENC_8r.py

TD-only benchmark for NEW_IV_ENC (8 rounds), following the style of
bench_td_only_newstructIII_qd.py. Uses td_trunc.py only.

Structure NEW_IV_ENC:
  u0' = R(u0) ⊕ u1
  u1' = R(u0) ⊕ u2
  u2' = u3
  u3' = R(u0)

Initial TD symbols:
  u0^0 = 0, u1^0 = 0, u2^0 = a, u3^0 = s

Timing:
  - 3 warmups, then repeat 100 times; report average and total wall time.

QD (TD-side heuristic):
  - If any Round-8 output is a⊕s, OR
  - Decrypt-prune (special 8→7 rule) terminates at u3^4 == 0_s,
    then we say "量子区分器存在".
"""

import importlib.util, os, time, statistics, gc

REPEAT = 100
ROUNDS = 8

def load_td_trunc():
    td_path = os.path.join(os.path.dirname(__file__), "td_trunc.py")
    spec = importlib.util.spec_from_file_location("td_trunc", td_path)
    if spec is None:
        raise RuntimeError("Cannot locate td_trunc.py")
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)  # type: ignore
    return m

def simulate_NEW_IV_ENC_hist(td):
    """Return history list of length 9: round 0..8, each is (u0,u1,u2,u3) Val tuple."""
    Z, A, S = td.Z, td.A, td.S
    u0,u1,u2,u3 = Z, Z, A, S
    eng = td.TDEngine()
    hist = [(u0,u1,u2,u3)]
    for _ in range(ROUNDS):
        Ru0 = eng.R(u0)
        u0n = eng.xor2(Ru0, u1)
        u1n = eng.xor2(Ru0, u2)
        u2n = td.copy_val(u3)
        u3n = Ru0
        u0,u1,u2,u3 = u0n,u1n,u2n,u3n
        hist.append((u0,u1,u2,u3))
    return hist

def qd_exists_td(td, hist) -> bool:
    """TD-side QD heuristic as documented above."""
    # Rule A: Round-8 has any a⊕s
    u0,u1,u2,u3 = hist[8]
    if any(v.sym == td.Sym.AS for v in (u0,u1,u2,u3)):
        return True

    # Rule B: decrypt-prune to see if it ends at u3^4 == 0_s
    survivors = {"u0","u1","u2","u3"}
    cur = 8
    while cur > 0:
        prev = cur - 1
        nxt = set()
        if cur == 8:
            # Special 8→7
            # u0^7 = u3^8
            if "u3" in survivors: nxt.add("u0")
            # u1^7 = u3^8 ⊕ u0^8
            if "u3" in survivors and "u0" in survivors: nxt.add("u1")
            # u2^7 = u3^8 ⊕ u1^8
            if "u3" in survivors and "u1" in survivors: nxt.add("u2")
            # u3^7 = u2^8
            if "u2" in survivors: nxt.add("u3")
        else:
            # Generic i+1→i rule for NEW_IV_ENC
            # Drop u0 inverse branch
            # u1^i depends on (u3^{i+1}, u0^{i+1})
            if "u3" in survivors and "u0" in survivors: nxt.add("u1")
            # u2^i depends on (u3^{i+1}, u1^{i+1})
            if "u3" in survivors and "u1" in survivors: nxt.add("u2")
            # u3^i depends on (u2^{i+1})
            if "u2" in survivors: nxt.add("u3")
        survivors = nxt
        cur = prev
        if len(survivors) == 1:
            last = next(iter(survivors))
            # if the single survivor at round cur is u3 and its TD symbol is 0_s, success
            if last == "u3" and hist[cur][3].sym == td.Sym.ZERO_S:
                return True
            break
    return False

def main():
    td = load_td_trunc()

    # Warmup (not counted)
    for _ in range(3):
        hist = simulate_NEW_IV_ENC_hist(td)
        _ = qd_exists_td(td, hist)
        gc.collect()

    # Timed runs
    totals = []
    qd_any = False
    t_all0 = time.perf_counter()
    for _ in range(REPEAT):
        t0 = time.perf_counter()
        hist = simulate_NEW_IV_ENC_hist(td)
        qd_any = qd_exists_td(td, hist)
        totals.append(time.perf_counter() - t0)
        gc.collect()
    t_all1 = time.perf_counter()

    avg_sim = statistics.mean(totals) if totals else 0.0
    print("=== NEW_IV_ENC（8轮）TD-only Benchmark ===")
    print(f"重复次数: {REPEAT}")
    print(f"量子区分器存在?: {'是' if qd_any else '否'}")
    print("\n== 平均耗时（秒）==")
    print(f"8轮仿真平均: {avg_sim:.6f}")
    print(f"\n整体耗时(含循环开销): {t_all1 - t_all0:.6f} s")

if __name__ == "__main__":
    main()

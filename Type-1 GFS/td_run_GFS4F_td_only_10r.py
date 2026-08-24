#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
td_run_GFS4F_td_only_10r.py

使用 td_trunc.py 的 TD 引擎，按 10 轮 GFS-4F 结构前向仿真，并打印每一轮（Round 0..10）的 TD 符号。

结构（i -> i+1）：
  u0' = u7
  u1' = R(u7) ⊕ u0
  u2' = R(u6) ⊕ u1
  u3' = R(u5) ⊕ u2
  u4' = R(u4) ⊕ u3
  u5' = u4
  u6' = u5
  u7' = u6

初始输入（Round 0）：
  u0=s, u1=a, u2=0, u3=0, u4=0, u5=0, u6=0, u7=0
"""

import importlib.util, os

ROUNDS = 10

def load_td_trunc():
    td_path = os.path.join(os.path.dirname(__file__), "td_trunc.py")
    spec = importlib.util.spec_from_file_location("td_trunc", td_path)
    if spec is None:
        raise RuntimeError("Cannot locate td_trunc.py")
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)  # type: ignore
    return m

def td_val_to_str(v) -> str:
    try:
        return str(v)
    except Exception:
        return "<Val?>"

def simulate_and_print():
    td = load_td_trunc()
    eng = td.TDEngine()

    # Round 0
    u = [td.S, td.A, td.Z, td.Z, td.Z, td.Z, td.Z, td.Z]  # u0..u7
    hist = [tuple(u)]

    # Round 1..10
    for _ in range(ROUNDS):
        Ru7 = eng.R(u[7])
        Ru6 = eng.R(u[6])
        Ru5 = eng.R(u[5])
        Ru4 = eng.R(u[4])
        u_next = [None]*8
        u_next[0] = td.copy_val(u[7])          # u0' = u7
        u_next[1] = eng.xor2(Ru7, u[0])        # u1' = R(u7) ⊕ u0
        u_next[2] = eng.xor2(Ru6, u[1])        # u2' = R(u6) ⊕ u1
        u_next[3] = eng.xor2(Ru5, u[2])        # u3' = R(u5) ⊕ u2
        u_next[4] = eng.xor2(Ru4, u[3])        # u4' = R(u4) ⊕ u3
        u_next[5] = td.copy_val(u[4])          # u5' = u4
        u_next[6] = td.copy_val(u[5])          # u6' = u5
        u_next[7] = td.copy_val(u[6])          # u7' = u6
        u = u_next
        hist.append(tuple(u))

    # Print Round 0..10
    for r in range(0, ROUNDS+1):
        items = [f"u{k}^{r}={td_val_to_str(hist[r][k])}" for k in range(8)]
        print(f"Round {r}:  " + ", ".join(items))

if __name__ == "__main__":
    simulate_and_print()

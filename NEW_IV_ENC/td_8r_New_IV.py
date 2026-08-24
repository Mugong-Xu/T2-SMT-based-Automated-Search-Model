#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
bench_td_8r_New_IV.py

TD-only展示脚本 for NEW_IV_ENC (8 rounds).
- 不做重复计时
- 输出每一轮 TD 符号
- 输出剪枝过程与最终结果
"""

import importlib.util
import os
from typing import List, Set, Tuple

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
    u0, u1, u2, u3 = Z, Z, A, S
    eng = td.TDEngine()
    hist = [(u0, u1, u2, u3)]
    for _ in range(ROUNDS):
        Ru0 = eng.R(u0)
        u0n = eng.xor2(Ru0, u1)
        u1n = eng.xor2(Ru0, u2)
        u2n = td.copy_val(u3)
        u3n = Ru0
        u0, u1, u2, u3 = u0n, u1n, u2n, u3n
        hist.append((u0, u1, u2, u3))
    return hist


def val_to_symbol_str(v) -> str:
    sym_str = str(v.sym)
    if sym_str.startswith("Sym."):
        sym_str = sym_str.split(".", 1)[1]
    mapping = {
        "ZERO": "0",
        "ZERO_S": "0_s",
        "A": "a",
        "S": "s",
        "AS": "a⊕s",
        "STAR": "*",
        "0": "0",
        "0_s": "0_s",
        "a": "a",
        "s": "s",
        "a⊕s": "a⊕s",
        "*": "*",
    }
    base = mapping.get(sym_str, sym_str)
    tag = getattr(v, "tag", None)
    tag_str = ""
    if tag is not None:
        raw = str(tag)
        if raw.startswith("Tag."):
            raw = raw.split(".", 1)[1]
        if raw not in ("PLAIN", "plain"):
            tag_map = {
                "FROM_R_A": "fromR_a",
                "FROM_R_AS": "fromR_as",
                "fromR_a": "fromR_a",
                "fromR_as": "fromR_as",
            }
            tag_str = f"<{tag_map.get(raw, raw)}>"
    if base == "a":
        a_flag = getattr(v, "a_flag", 0)
        return f"{base}{tag_str}[a_flag={a_flag}]"
    return f"{base}{tag_str}"


def print_rounds(hist):
    print("=== NEW_IV_ENC（8轮）TD 逐轮符号 ===")
    for r, vals in enumerate(hist):
        u0, u1, u2, u3 = vals
        print(f"Round {r}:")
        print(f"  u0^{r}: {val_to_symbol_str(u0)}")
        print(f"  u1^{r}: {val_to_symbol_str(u1)}")
        print(f"  u2^{r}: {val_to_symbol_str(u2)}")
        print(f"  u3^{r}: {val_to_symbol_str(u3)}")


def prune_trace(td, hist) -> Tuple[List[str], Tuple[int, str], bool]:
    """
    Return:
      trace_lines,
      (final_round, final_branch),
      qd_success  # whether prune terminates at u3^4 == 0_s
    """
    survivors: Set[str] = {"u0", "u1", "u2", "u3"}
    cur = ROUNDS
    trace_lines: List[str] = [f"初始幸存分支（Round {cur}）: {{{', '.join(sorted(survivors))}}}"]

    while cur > 0:
        prev = cur - 1
        nxt: Set[str] = set()
        if cur == 8:
            if "u3" in survivors:
                nxt.add("u0")
            if "u3" in survivors and "u0" in survivors:
                nxt.add("u1")
            if "u3" in survivors and "u1" in survivors:
                nxt.add("u2")
            if "u2" in survivors:
                nxt.add("u3")
        else:
            if "u3" in survivors and "u0" in survivors:
                nxt.add("u1")
            if "u3" in survivors and "u1" in survivors:
                nxt.add("u2")
            if "u2" in survivors:
                nxt.add("u3")

        trace_lines.append(
            f"Round {cur} -> Round {prev}: {{{', '.join(sorted(survivors))}}} -> "
            f"{{{', '.join(sorted(nxt))}}}"
        )
        survivors = nxt
        cur = prev

        if len(survivors) == 1:
            last = next(iter(survivors))
            idx = int(last[1])
            v = hist[cur][idx]
            success = (last == "u3" and cur == 4 and v.sym == td.Sym.ZERO_S)
            return trace_lines, (cur, last), success

    if survivors:
        last = sorted(survivors)[0]
    else:
        last = "无"
    return trace_lines, (cur, last), False


def qd_exists_td(td, hist, final_round: int, final_branch: str, prune_success: bool) -> bool:
    # Rule A: Round-8 has any a⊕s
    u0, u1, u2, u3 = hist[8]
    if any(v.sym == td.Sym.AS for v in (u0, u1, u2, u3)):
        return True
    # Rule B: decrypt-prune terminates at u3^4 == 0_s
    return prune_success and final_branch == "u3" and final_round == 4


def main():
    td = load_td_trunc()
    hist = simulate_NEW_IV_ENC_hist(td)
    print_rounds(hist)

    print("\n=== 剪枝过程 ===")
    trace_lines, (final_round, final_branch), prune_success = prune_trace(td, hist)
    for line in trace_lines:
        print(line)

    print("\n=== 剪枝结果 ===")
    if final_branch != "无":
        idx = int(final_branch[1])
        final_val = hist[final_round][idx]
        print(f"最终剩余分支: {final_branch}^{final_round}")
        print(f"对应符号: {val_to_symbol_str(final_val)}")
    else:
        print("最终剩余分支: 无")
        print("对应符号: 无")

    print("\n=== 量子区分器判定 ===")
    qd = qd_exists_td(td, hist, final_round, final_branch, prune_success)
    print(f"量子区分器存在?: {'是' if qd else '否'}")
    print(f"剪枝判定条件（终止于 u3^4 == 0_s）: {'满足' if prune_success else '不满足'}")


if __name__ == "__main__":
    main()

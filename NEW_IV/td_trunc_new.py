
from typing import Tuple, List
from td_trunc import TDEngine, Z, A, S, Val, Sym, copy_val

def simulate_type2_gfs_5r(
    init: Tuple[Val, Val, Val, Val] = (Z, Z, A, S),
    rounds: int = 5
) -> List[Tuple[Val, Val, Val, Val]]:
    """
    轮函数：
      u0' = R(u0) ⊕ u1
      u1' = u2
      u2' = R(u2) ⊕ u3
      u3' = u0
    返回：[(u0^0, u1^0, u2^0, u3^0), ..., (u0^rounds, ...)]
    """
    eng = TDEngine()
    u0, u1, u2, u3 = init
    hist = [(u0, u1, u2, u3)]
    for _ in range(rounds):
        u0n = eng.xor2(eng.R(u0), u1)
        u1n = copy_val(u2)  # 复制：强制 a_flag=0
        u2n = eng.xor2(eng.R(u2), u3)
        u3n = copy_val(u0)  # 复制：强制 a_flag=0
        u0, u1, u2, u3 = u0n, u1n, u2n, u3n
        hist.append((u0, u1, u2, u3))
    return hist

def td_to_smt_mask(v: Val) -> int | None:
    if v.sym == Sym.ZERO:    return 0b00000
    if v.sym == Sym.ZERO_S:  return 0b10000
    if v.sym == Sym.S:       return 0b00100
    if v.sym == Sym.AS:      return 0b00101
    if v.sym == Sym.A:       return (0b10001 if getattr(v, "a_flag", 0)==1 else 0b00001)
    if v.sym == Sym.STAR:    return None
    return None

def is_pure_for_R(v: Val) -> bool:
    if v.sym in (Sym.ZERO, Sym.ZERO_S, Sym.S): return True
    if v.sym == Sym.A and getattr(v, "a_flag", 0)==0: return True
    return False

def find_safe_anchor_round(hist):
    for r in range(5, -1, -1):
        u0,u1,u2,u3 = hist[r]
        if all(v.sym != Sym.STAR for v in (u0,u1,u2,u3)) and is_pure_for_R(u0):
            return r
    return None

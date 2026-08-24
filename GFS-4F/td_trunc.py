# td_trunc.py
# Σ = {0, 0_s, a, s, a⊕s, *} 的直接传播模型（不依赖 SMT）
# 支持一次性触发：首次出现 R(a⊕s) 或 R(a) ⊕ s 时产生 0_s（仅一次）
# 新增 a_flag：若 a 由复制或 a⊕0 得到 → a_flag=0；若 a 由 a⊕0_s 得到 → a_flag=1

from enum import Enum
from dataclasses import dataclass
from typing import List, Tuple

# ===== 6 个符号 =====
class Sym(str, Enum):
    ZERO   = "0"
    ZERO_S = "0_s"
    A      = "a"
    S      = "s"
    AS     = "a⊕s"
    STAR   = "*"

# 标记：用于识别 “R(a)” 产出的特定 *
class Tag(str, Enum):
    PLAIN     = "plain"     # 普通产生的 *
    FROM_R_A  = "fromR_a"   # 由 R(a) 产生的 *
    FROM_R_AS = "fromR_as"  # 由 R(a⊕s) 产生的 *（一般用不到，但保留）

@dataclass
class Val:
    sym: Sym
    tag: Tag = Tag.PLAIN
    a_flag: int = 0  # ← 新增：0 / 1
    def __str__(self) -> str:
        base = f"{self.sym}"
        if self.tag != Tag.PLAIN:
            base += f"<{self.tag.value}>"
        if self.sym == Sym.A:
            base += f"[a_flag={self.a_flag}]"
        return base

# ===== 一次性触发状态 =====
class TriggerState:
    def __init__(self) -> None:
        self.triggered: bool = False
    def reset(self) -> None:
        self.triggered = False

# ===== 引擎：实现 R / XOR 与一次性触发 =====
class TDEngine:
    def __init__(self) -> None:
        self.st = TriggerState()

    # 重置“首次触发”状态
    def reset(self) -> None:
        self.st.reset()

    # XOR（二元），按你的规则 + “首次出现 R(a) ⊕ s → 0_s”
    def xor2(self, a: Val, b: Val) -> Val:
        # 首发：R(a) ⊕ s  -> 0_s
        if not self.st.triggered:
            cond_ra_s = (
                (a.sym == Sym.S and b.sym == Sym.STAR and b.tag == Tag.FROM_R_A) or
                (b.sym == Sym.S and a.sym == Sym.STAR and a.tag == Tag.FROM_R_A)
            )
            if cond_ra_s:
                self.st.triggered = True
                return Val(Sym.ZERO_S)

        # 1) * 吸收
        if a.sym == Sym.STAR or b.sym == Sym.STAR:
            return Val(Sym.STAR)

        # 2) 单位元（无冲突定义）
        # 0 ⊕ A = A ，A ∈ {0, 0_s, a, s, a⊕s, *}
        if a.sym == Sym.ZERO:
            # 若 A == a，则 a_flag = 0（a⊕0=a）
            if b.sym == Sym.A:
                return Val(Sym.A, b.tag, a_flag=0)
            return Val(b.sym, b.tag)
        if b.sym == Sym.ZERO:
            if a.sym == Sym.A:
                return Val(Sym.A, a.tag, a_flag=0)
            return Val(a.sym, a.tag)

        # 0_s ⊕ A = A ，A ∈ {0_s, a, s, a⊕s, *}（排除 A=0 以避免与上面冲突）
        if a.sym == Sym.ZERO_S and b.sym != Sym.ZERO:
            if b.sym == Sym.A:
                # a ⊕ 0_s = a → a_flag = 1
                return Val(Sym.A, b.tag, a_flag=1)
            return Val(b.sym, b.tag)
        if b.sym == Sym.ZERO_S and a.sym != Sym.ZERO:
            if a.sym == Sym.A:
                return Val(Sym.A, a.tag, a_flag=1)
            return Val(a.sym, a.tag)

        # 3) 指定合并
        # a ⊕ s = a⊕s
        if {a.sym, b.sym} == {Sym.A, Sym.S}:
            return Val(Sym.AS)
        # (a⊕s) ⊕ s = a   —— 未指定 a_flag，默认 0
        if (a.sym == Sym.AS and b.sym == Sym.S) or (a.sym == Sym.S and b.sym == Sym.AS):
            return Val(Sym.A, a_flag=0)
        # (a⊕s) ⊕ a = s
        if (a.sym == Sym.AS and b.sym == Sym.A) or (a.sym == Sym.A and b.sym == Sym.AS):
            return Val(Sym.S)

        # —— 闭包补全（不改变你给的核心规则，仅保证可计算性）——
        if a.sym == b.sym == Sym.A:
            return Val(Sym.ZERO)
        if a.sym == b.sym == Sym.S:
            return Val(Sym.ZERO)
        if a.sym == b.sym == Sym.AS:
            return Val(Sym.ZERO)

        # 其它未列出：保守为 *
        return Val(Sym.STAR)

    # XOR 多元
    def xorf(self, *vals: Val) -> Val:
        out = Val(Sym.ZERO)
        for v in vals:
            out = self.xor2(out, v)
            if out.sym == Sym.STAR:
                return out
        return out

    # R：按你的规则 + “首次出现 R(a⊕s) → 0_s（即使后面不接 ⊕）”
    def R(self, x: Val) -> Val:
        # 1) 基本
        if x.sym == Sym.ZERO:
            return Val(Sym.ZERO)
        if x.sym == Sym.ZERO_S:
            return Val(Sym.ZERO_S)

        # 3) 首次出现 R(a⊕s) → 0_s
        if (x.sym == Sym.AS) and (not self.st.triggered):
            self.st.triggered = True
            return Val(Sym.ZERO_S)

        # 2) 其它：R(s)=*，R(*)=*；并且 “否则 R(A)=*，A∈{a,s,a⊕s,*}”
        if x.sym == Sym.S:
            return Val(Sym.STAR)
        if x.sym == Sym.A:
            return Val(Sym.STAR, Tag.FROM_R_A)   # 标明：来自 R(a) 的 *
        if x.sym == Sym.AS:
            return Val(Sym.STAR, Tag.FROM_R_AS)
        if x.sym == Sym.STAR:
            return Val(Sym.STAR)

        # 理论上到不了
        return Val(Sym.STAR)

# ===== 便捷常量（都是 Val 类型）=====
Z    = Val(Sym.ZERO)
ZS   = Val(Sym.ZERO_S)
A    = Val(Sym.A)     # 默认 a_flag=0
S    = Val(Sym.S)
AS   = Val(Sym.AS)
STAR = Val(Sym.STAR)

# ===== 复制（SPLIT/直连搬移）=====
def copy_val(v: Val) -> Val:
    """复制：若是 a，则强制 a_flag=0；其他符号原样保留。"""
    if v.sym == Sym.A:
        return Val(Sym.A, v.tag, a_flag=0)
    return Val(v.sym, v.tag, getattr(v, "a_flag", 0))

# ===== 示例：5 轮 Type-2 GFS（可直接调用）=====
def simulate_type2_gfs_5r(
    init: Tuple[Val,Val,Val,Val] = (Z, Z, A, S),
    rounds: int = 5
) -> List[Tuple[Val,Val,Val,Val]]:
    """
    轮函数：
      u0' = R(u0) ⊕ u1
      u1' = u2
      u2' = R(u2) ⊕ u3
      u3' = u0
    返回：[(u0^0,u1^0,u2^0,u3^0), ..., (u0^rounds, ...)]
    """
    eng = TDEngine()
    u0,u1,u2,u3 = init
    hist = [(u0,u1,u2,u3)]
    for _ in range(rounds):
        u0n = eng.xor2(eng.R(u0), u1)
        u1n = copy_val(u2)             # 复制：强制 a_flag=0
        u2n = eng.xor2(eng.R(u2), u3)
        u3n = copy_val(u0)             # 复制：强制 a_flag=0
        u0,u1,u2,u3 = u0n,u1n,u2n,u3n
        hist.append((u0,u1,u2,u3))
    return hist

# 直接运行本文件时，打印一份演示
if __name__ == "__main__":
    hist = simulate_type2_gfs_5r(init=(Z, Z, A, S), rounds=5)
    for i,(u0,u1,u2,u3) in enumerate(hist):
        print(f"Round {i}: u0={u0}, u1={u1}, u2={u2}, u3={u3}")

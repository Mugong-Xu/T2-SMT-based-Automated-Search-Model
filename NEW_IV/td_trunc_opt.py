
from enum import Enum
from dataclasses import dataclass

class Sym(str, Enum):
    ZERO   = "0"
    ZERO_S = "0_s"
    A      = "a"
    S      = "s"
    AS     = "a⊕s"
    STAR   = "*"

class Tag(str, Enum):
    PLAIN     = "plain"
    FROM_R_A  = "fromR_a"   # 用于：R(a)来源的标记；也用于 0_s⊕s 派生的 s 打印为 R(a)

@dataclass
class Val:
    sym: Sym
    tag: Tag = Tag.PLAIN
    a_flag: int = 0
    def __str__(self) -> str:
        # 特殊打印：若这是由 0_s ⊕ s 派生并标注为 FROM_R_A 的 s，则打印成 R(a)
        if self.sym == Sym.S and self.tag == Tag.FROM_R_A:
            return "R(a)"
        base = f"{self.sym}"
        if self.tag != Tag.PLAIN:
            base += f"<{self.tag.value}>"
        if self.sym == Sym.A:
            base += f"[a_flag={self.a_flag}]"
        return base

class TriggerState:
    def __init__(self) -> None:
        self.first_fired = False   # 首次触发：*<fromR_a> ⊕ s -> 0_s
        self.last_trigger = None   # 若需要扩展回退，可使用

    def reset(self) -> None:
        self.first_fired = False
        self.last_trigger = None

class TDEngine:
    def __init__(self) -> None:
        self.st = TriggerState()

    def reset(self) -> None:
        self.st.reset()

    # 复制（SPLIT）：完整保留标签（包括 *<fromR_a>）
    def copy_val(self, v: Val) -> Val:
        return Val(v.sym, v.tag, getattr(v, "a_flag", 0))

    def xor2(self, a: Val, b: Val) -> Val:
        # ===== 首次触发： *<fromR_a> ⊕ s  =>  0_s（只触发一次） =====
        if not self.st.first_fired:
            cond_star_fromRa_s = (
                (a.sym == Sym.STAR and a.tag == Tag.FROM_R_A and b.sym == Sym.S) or
                (b.sym == Sym.STAR and b.tag == Tag.FROM_R_A and a.sym == Sym.S)
            )
            if cond_star_fromRa_s:
                self.st.first_fired = True
                self.st.last_trigger = "star_fromRa_s"
                return Val(Sym.ZERO_S)

        # ===== 基本规则 =====
        # * 吸收（保留标签，以便传播）
        if a.sym == Sym.STAR or b.sym == Sym.STAR:
            return Val(Sym.STAR, a.tag if a.sym == Sym.STAR else b.tag)

        # 单位元 0
        if a.sym == Sym.ZERO:
            if b.sym == Sym.A:
                return Val(Sym.A, b.tag, a_flag=0)
            return Val(b.sym, b.tag)
        if b.sym == Sym.ZERO:
            if a.sym == Sym.A:
                return Val(Sym.A, a.tag, a_flag=0)
            return Val(a.sym, a.tag)

        # 0_s ⊕ s = s —— 但根据你的需求打印成 R(a)：给 s 打上 FROM_R_A 标签
        if (a.sym == Sym.ZERO_S and b.sym == Sym.S) or (b.sym == Sym.ZERO_S and a.sym == Sym.S):
            return Val(Sym.S, Tag.FROM_R_A)

        # 0_s ⊕ A = A, A ∈ {0_s, a, a⊕s, *}
        if a.sym == Sym.ZERO_S and b.sym in (Sym.ZERO_S, Sym.A, Sym.AS, Sym.STAR):
            return Val(b.sym, b.tag)
        if b.sym == Sym.ZERO_S and a.sym in (Sym.ZERO_S, Sym.A, Sym.AS, Sym.STAR):
            return Val(a.sym, a.tag)

        # a ⊕ s = a⊕s
        if {a.sym, b.sym} == {Sym.A, Sym.S}:
            return Val(Sym.AS)
        # (a⊕s) ⊕ s = a
        if (a.sym == Sym.AS and b.sym == Sym.S) or (a.sym == Sym.S and b.sym == Sym.AS):
            return Val(Sym.A, a_flag=0)
        # (a⊕s) ⊕ a = s
        if (a.sym == Sym.AS and b.sym == Sym.A) or (a.sym == Sym.A and b.sym == Sym.AS):
            return Val(Sym.S)

        # 同类抵消为 0
        if a.sym == b.sym and a.sym in (Sym.A, Sym.S, Sym.AS):
            return Val(Sym.ZERO)

        # 其它未覆盖：保守为 *
        return Val(Sym.STAR)

    def xorf(self, *vals: Val) -> Val:
        out = Val(Sym.ZERO)
        for v in vals:
            out = self.xor2(out, v)
            if out.sym == Sym.STAR:
                return out
        return out

    # R 运算：R(a) -> *<fromR_a>；R(0)->0；R(0_s)->0_s；其他 -> *
    def R(self, x: Val) -> Val:
        if x.sym == Sym.ZERO:
            return Val(Sym.ZERO)
        if x.sym == Sym.ZERO_S:
            return Val(Sym.ZERO_S)
        if x.sym == Sym.A:
            return Val(Sym.STAR, Tag.FROM_R_A)   # R(a) 以 *<fromR_a> 表现
        return Val(Sym.STAR)

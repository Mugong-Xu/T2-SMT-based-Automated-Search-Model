# model_graph_flexible.py
# Strict encoding of §4: symbols, initial constraints, R(3)-(7), XOR(2-4) with ⊥ propagation.
from cvc5 import Solver, Kind
import cvc5

# -------------------- Helpers --------------------

def mk_solver():
    slv = Solver()
    slv.setOption("produce-models", "true")
    slv.setOption("strings-exp", "false")
    slv.setLogic("QF_BV")
    return slv

def build_symbols_4_1(s):
    # 5-bit: [δ, R(δ), x, R(x), 0s] = bits [0..4]
    return dict(
        ZERO    = s.mkBitVector(5, 0),
        DELTA   = s.mkBitVector(5, 1 << 0),
        R_DELTA = s.mkBitVector(5, 1 << 1),
        X       = s.mkBitVector(5, 1 << 2),
        R_X     = s.mkBitVector(5, 1 << 3),
        ZERO_S  = s.mkBitVector(5, 1 << 4),
    )

def Eq(s, a, b):  return s.mkTerm(Kind.EQUAL, a, b)
def Imp(s, a, b): return s.mkTerm(Kind.IMPLIES, a, b)
def Not(s, a):    return s.mkTerm(Kind.NOT, a)
def Or2(s, a, b): return s.mkTerm(Kind.OR, a, b)
def And2(s, a, b):return s.mkTerm(Kind.AND, a, b)

def AndN(s, *xs):
    if not xs: return s.mkTrue()
    cur = xs[0]
    for x in xs[1:]:
        cur = s.mkTerm(Kind.AND, cur, x)
    return cur

def OrN(s, *xs):
    if not xs: return s.mkFalse()
    cur = xs[0]
    for x in xs[1:]:
        cur = s.mkTerm(Kind.OR, cur, x)
    return cur

def big_or(s, arr):
    if not arr: return s.mkFalse()
    cur = arr[0]
    for t in arr[1:]:
        cur = s.mkTerm(Kind.OR, cur, t)
    return cur

def at_most_one(s, bools):
    # pairwise AMO
    for i in range(len(bools)):
        for j in range(i+1, len(bools)):
            s.assertFormula(Not(s, And2(s, bools[i], bools[j])))

def Extract(s, hi, lo, t):
    # hi >= lo，且都是 Python 的 int
    op = s.mkOp(Kind.BITVECTOR_EXTRACT, hi, lo)
    return s.mkTerm(op, t)


# -------------------- SPLIT --------------------

def split_k(s, src, k, base="split"):
    # Produce k outputs each equal to src
    outs = []
    for i in range(k):
        oi = s.mkConst(src.getSort(), f"{base}{i}")
        s.assertFormula(Eq(s, oi, src))
        outs.append(oi)
    return outs

# -------------------- Initial constraints (§4.2) --------------------

def add_initial_constraints_4_2(s, syms, inputs, tails, allow_weak=False):
    # (1) Domain: inputs ∈ {0, X, Δ, X⊕Δ}
    X, D, Z = syms["X"], syms["DELTA"], syms["ZERO"]
    XoD = s.mkTerm(Kind.BITVECTOR_XOR, X, D)
    allowed = [Z, X, D, XoD]
    for ui in inputs:
        s.assertFormula(big_or(s, [Eq(s, ui, c) for c in allowed]))

    # (2a) At least one δ (counted by bit, so X⊕Δ also valid)
    one = s.mkBitVector(1,1)
    has_delta_bits = [Eq(s, Extract(s, 0, 0, ui), one) for ui in inputs]
    s.assertFormula(big_or(s, has_delta_bits))

    # (2b) "x or x⊕δ" appears at most once
    isX  = [Eq(s, ui, X)   for ui in inputs]
    isXd = [Eq(s, ui, XoD) for ui in inputs]
    occ  = [Or2(s, a, b) for a, b in zip(isX, isXd)]
    at_most_one(s, occ)

    # (3) Tail separability (strong; optionally weak 001)
    def strong_has_0s(t):  # 0s bit == 1
        return Eq(s, Extract(s, 4, 4, t), one)
    strong_any = big_or(s, [strong_has_0s(t) for t in tails])

    if allow_weak:
        # weak 001 on projection (0s=0, R(x)=0, x=1)
        zero = s.mkBitVector(1,0)
        def weak_001(t):
            c0 = Eq(s, Extract(s, 4, 4, t), zero)  # 0s=0
            c1 = Eq(s, Extract(s, 3, 3, t), zero)  # R(x)=0
            c2 = Eq(s, Extract(s, 2, 2, t), one)   # x=1
            return AndN(s, c0, c1, c2)
        weak_any = big_or(s, [weak_001(t) for t in tails])
        s.assertFormula(Or2(s, strong_any, weak_any))
    else:
        s.assertFormula(strong_any)

# -------------------- R node: §4 (3)-(7) with ⊥ --------------------

def add_R_node(s, syms, x_in, name, monotone_guard=True):
    """
    Strict §4 (3)-(7):
      - Only pure 0s -> 0s (5)
      - only_x -> R(x) (3); only_d -> R(δ) (4); 0 -> 0 (5)
      - mixture & s_i -> 0s (6); mixture & ¬s_i -> ⊥
      - others -> ⊥ (7)
    Return: (x_out, s_i, mixture, bot)
    """
    x_out = s.mkConst(x_in.getSort(), f"R_{name}")
    one = s.mkBitVector(1,1); zero = s.mkBitVector(1,0)

    def b1(idx): return s.mkTerm(Kind.EQUAL, Extract(s, idx, idx, x_in), one)
    has0s, hasRx, hasX, hasRd, hasD = b1(4), b1(3), b1(2), b1(1), b1(0)

    # —— 先组合“家族”位 ——
    hasXfam = Or2(s, hasX, hasRx)      # x 家族
    hasDfam = Or2(s, hasD, hasRd)      # δ 家族
    mixture = And2(s, hasXfam, hasDfam)

    # —— 关键修正：only_x / only_d 需排除 has0s ——
    only_x  = AndN(s, hasXfam, Not(s, hasDfam), Not(s, has0s))
    only_d  = AndN(s, hasDfam, Not(s, hasXfam), Not(s, has0s))

    is_zero = Eq(s, x_in, syms["ZERO"])
    # 仅“纯 0s”映射到 0s：有 0s 且无任一显式位
    pure0s  = AndN(s, has0s, Not(s, hasXfam), Not(s, hasDfam))

    # 其余（others）：不属于 {only_x, only_d, is_zero, pure0s, mixture}
    others = Not(s, OrN(s, only_x, only_d, is_zero, pure0s, mixture))

    s_i = s.mkConst(s.getBooleanSort(), f"s_{name}")  # Eq.(6) trigger

    # (3)(4)(5)
    s.assertFormula(Imp(s, pure0s,  Eq(s, x_out, syms["ZERO_S"])))
    s.assertFormula(Imp(s, only_x,  Eq(s, x_out, syms["R_X"])))
    s.assertFormula(Imp(s, only_d,  Eq(s, x_out, syms["R_DELTA"])))
    s.assertFormula(Imp(s, is_zero, Eq(s, x_out, syms["ZERO"])))

    # (6) mixture
    s.assertFormula(Imp(s, And2(s, mixture, s_i), Eq(s, x_out, syms["ZERO_S"])))

    # (6) 未触发混合  或  (7) others  ——> ⊥
    bot = s.mkConst(s.getBooleanSort(), f"bot_{name}")
    s.assertFormula(Eq(s, bot, Or2(s, And2(s, mixture, Not(s, s_i)), others)))

    # ⊥：不可分离（无 0s，且不是弱 001），避免被尾部判据误当“可分离”
    not_sep = And2(s,
        Eq(s, Extract(s,4,4,x_out), zero),
        Not(s, Eq(s, Extract(s,4,2,x_out), s.mkBitVector(3,1)))
    )
    s.assertFormula(Imp(s, bot, not_sep))

    # s_i 只能在混合上为真
    s.assertFormula(Imp(s, s_i, mixture))

    # 可选：单调守卫——在 (mixture ∧ ¬s_i) 分支不引入新显式位
    if monotone_guard:
        def bit_is1(t, idx): return Eq(s, Extract(s, idx, idx, t), one)
        guard = And2(s, mixture, Not(s, s_i))
        for bit in (3,2,1,0):  # R(x), x, R(δ), δ
            s.assertFormula(Imp(s, guard, Imp(s, bit_is1(x_out, bit), bit_is1(x_in, bit))))

    return x_out, s_i, mixture, bot


# -------------------- XOR node: Property 2/3/4 + ⊥ absorb --------------------

def add_XOR_node_no_collision(s, A, B, name: str, Abot=None, Bbot=None):
    """
    XOR without collisions: Property 2 + Property 3 (always).
    Return: (W, xflag=false, botW)
    """
    ZERO    = s.mkBitVector(5, 0)
    DELTA   = s.mkBitVector(5, 1 << 0)
    R_DELTA = s.mkBitVector(5, 1 << 1)
    X       = s.mkBitVector(5, 1 << 2)
    R_X     = s.mkBitVector(5, 1 << 3)
    ZERO_S  = s.mkBitVector(5, 1 << 4)

    def m_and(T, M): return s.mkTerm(Kind.BITVECTOR_AND, T, M)

    bv5 = s.mkBitVectorSort(5)
    W = s.mkConst(bv5, name)

    u0, v0, w0 = m_and(A, ZERO_S),  m_and(B, ZERO_S),  m_and(W, ZERO_S)
    u1, v1, w1 = m_and(A, R_X),     m_and(B, R_X),     m_and(W, R_X)
    u2, v2, w2 = m_and(A, X),       m_and(B, X),       m_and(W, X)
    u3, v3, w3 = m_and(A, R_DELTA), m_and(B, R_DELTA), m_and(W, R_DELTA)
    u4, v4, w4 = m_and(A, DELTA),   m_and(B, DELTA),   m_and(W, DELTA)

    # Property 2
    s.assertFormula(Eq(s, w0, s.mkTerm(Kind.BITVECTOR_OR,  u0, v0)))
    s.assertFormula(Eq(s, w1, s.mkTerm(Kind.BITVECTOR_OR,  u1, v1)))
    s.assertFormula(Eq(s, w2, s.mkTerm(Kind.BITVECTOR_XOR, u2, v2)))
    # Property 3 (always, since no collisions)
    s.assertFormula(Eq(s, w3, s.mkTerm(Kind.BITVECTOR_OR, u3, v3)))  # R(δ)位
    s.assertFormula(Eq(s, w4, s.mkTerm(Kind.BITVECTOR_OR, u4, v4)))  # δ 位

    # xflag=false (to keep interface uniform)
    xflag = s.mkConst(s.getBooleanSort(), f"xXOR_{name}")
    s.assertFormula(Not(s, xflag))

    # ⊥ absorb
    boolSort = s.getBooleanSort()
    if Abot is None:
        Abot = s.mkConst(boolSort, f"bot_inA_{name}"); s.assertFormula(Not(s, Abot))
    if Bbot is None:
        Bbot = s.mkConst(boolSort, f"bot_inB_{name}"); s.assertFormula(Not(s, Bbot))
    botW = s.mkConst(boolSort, f"bot_{name}")
    s.assertFormula(Eq(s, botW, Or2(s, Abot, Bbot)))

    return W, xflag, botW

def add_XOR_node(s, A, B, name: str, Abot=None, Bbot=None):
    """
    XOR with Property 2/3/4 + collision flag xflag, and ⊥ absorb.
    Return: (W, xflag, botW)
    """
    ZERO    = s.mkBitVector(5, 0)
    DELTA   = s.mkBitVector(5, 1 << 0)
    R_DELTA = s.mkBitVector(5, 1 << 1)
    X       = s.mkBitVector(5, 1 << 2)
    R_X     = s.mkBitVector(5, 1 << 3)
    ZERO_S  = s.mkBitVector(5, 1 << 4)

    def m_and(T, M): return s.mkTerm(Kind.BITVECTOR_AND, T, M)

    bv5 = s.mkBitVectorSort(5)
    W = s.mkConst(bv5, name)

    u0, v0, w0 = m_and(A, ZERO_S),  m_and(B, ZERO_S),  m_and(W, ZERO_S)
    u1, v1, w1 = m_and(A, R_X),     m_and(B, R_X),     m_and(W, R_X)
    u2, v2, w2 = m_and(A, X),       m_and(B, X),       m_and(W, X)
    u3, v3, w3 = m_and(A, R_DELTA), m_and(B, R_DELTA), m_and(W, R_DELTA)
    u4, v4, w4 = m_and(A, DELTA),   m_and(B, DELTA),   m_and(W, DELTA)

    # Property 2
    s.assertFormula(Eq(s, w0, s.mkTerm(Kind.BITVECTOR_OR,  u0, v0)))      # 0s: OR
    s.assertFormula(Eq(s, w1, s.mkTerm(Kind.BITVECTOR_OR,  u1, v1)))      # R(x): OR
    s.assertFormula(Eq(s, w2, s.mkTerm(Kind.BITVECTOR_XOR, u2, v2)))      # x : XOR

    # Property 3 / 4 switching via xflag
    boolSort = s.getBooleanSort()
    xflag = s.mkConst(boolSort, f"xXOR_{name}")
    not_x = Not(s, xflag)

    # no-collision propagation
    # —— 这里改动：无碰撞时 δ 家族按 OR 传播 ——
    s.assertFormula(Imp(s, not_x,
                        And2(s,
                             Eq(s, w3, s.mkTerm(Kind.BITVECTOR_OR, u3, v3)),
                             Eq(s, w4, s.mkTerm(Kind.BITVECTOR_OR, u4, v4)),
                             )
                        ))

    # trigger patterns for Property 4
    def has_bit(T, M): return Eq(s, m_and(T, M), M)
    A_Rd, A_d = has_bit(A, R_DELTA), has_bit(A, DELTA)
    B_Rd, B_d = has_bit(B, R_DELTA), has_bit(B, DELTA)

    # allowed outputs tests
    def w3_eq0(): return Eq(s, w3, ZERO)
    def w3_eq1(): return Eq(s, w3, R_DELTA)
    def w4_eq0(): return Eq(s, w4, ZERO)
    def w4_eq1(): return Eq(s, w4, DELTA)

    # A: (Rδ, δ) or (δ, Rδ)
    cond_A = Or2(s,
        AndN(s, A_Rd, B_d, Not(s, A_d), Not(s, B_Rd)),
        AndN(s, A_d,  B_Rd, Not(s, A_Rd), Not(s, B_d)),
    )
    out_A_no_col = And2(s, w3_eq1(), w4_eq1())   # Rδ⊕δ
    out_A_col    = And2(s, w3_eq0(), w4_eq0())   # 0

    # B: (Rδ⊕δ, Rδ⊕δ) or (Rδ, Rδ)
    cond_B = Or2(s,
        AndN(s, A_Rd, A_d, B_Rd, B_d),
        AndN(s, A_Rd, Not(s, A_d), B_Rd, Not(s, B_d)),
    )
    out_B_no_col = And2(s, w3_eq1(), w4_eq0())   # Rδ
    out_B_col    = And2(s, w3_eq0(), w4_eq0())   # 0

    # C: (Rδ⊕δ, Rδ) or (Rδ, Rδ⊕δ)
    cond_C = Or2(s,
        AndN(s, A_Rd, A_d, B_Rd, Not(s, B_d)),
        AndN(s, A_Rd, Not(s, A_d), B_Rd, B_d),
    )
    out_C_no_col = And2(s, w3_eq1(), w4_eq1())   # Rδ⊕δ
    out_C_col_0  = And2(s, w3_eq0(), w4_eq0())   # 0
    out_C_col_d  = And2(s, w3_eq0(), w4_eq1())   # δ

    # Property 4 assertions
    s.assertFormula(Imp(s, cond_A, Or2(s, And2(s, not_x, out_A_no_col), And2(s, xflag, out_A_col))))
    s.assertFormula(Imp(s, cond_B, Or2(s, And2(s, not_x, out_B_no_col), And2(s, xflag, out_B_col))))
    s.assertFormula(Imp(s, cond_C, Or2(s, And2(s, not_x, out_C_no_col),
                                       And2(s, xflag, Or2(s, out_C_col_0, out_C_col_d)))))

    cond_any = OrN(s, cond_A, cond_B, cond_C)
    # necessary condition for collision flag
    s.assertFormula(Imp(s, xflag, cond_any))
    s.assertFormula(Imp(s, Not(s, cond_any), Not(s, xflag)))

    # ⊥ absorb
    if Abot is None:
        Abot = s.mkConst(boolSort, f"bot_inA_{name}"); s.assertFormula(Not(s, Abot))
    if Bbot is None:
        Bbot = s.mkConst(boolSort, f"bot_inB_{name}"); s.assertFormula(Not(s, Bbot))
    botW = s.mkConst(boolSort, f"bot_{name}")
    s.assertFormula(Eq(s, botW, Or2(s, Abot, Bbot)))

    return W, xflag, botW

# -------------------- Builder --------------------

def build_from_graph(spec):
    """
    spec:
      n_inputs: int
      nodes: topo-ordered ops:
        - SPLIT: {"op":"SPLIT","name":str,"in":ref,"k":int}
        - R    : {"op":"R","name":str,"in":ref}
        - XOR  : {"op":"XOR","name":str,"a":ref,"b":ref}
      tails: list[str]
      allow_weak: bool
      sum1: bool
      monotone_guard: bool
      collisions: bool
    """
    s = mk_solver()
    syms = build_symbols_4_1(s)

    # 1) inputs and maps
    n = int(spec["n_inputs"])
    bv5 = s.mkBitVectorSort(5)
    inputs = [s.mkConst(bv5, f"u0_{i}") for i in range(n)]
    outmap = {f"u0_{i}": [inputs[i]] for i in range(n)}
    # botmap: maintain ⊥ for each value
    botmap = {f"u0_{i}": [s.mkConst(s.getBooleanSort(), f"bot_u0_{i}")] for i in range(n)}
    for i in range(n):
        s.assertFormula(Not(s, botmap[f"u0_{i}"][0]))  # inputs are not ⊥

    # 2) UR tails placeholders and initial constraints bound to UR
    tails_specs = list(spec["tails"])
    ur = [s.mkConst(bv5, f"ur_{i}") for i in range(len(tails_specs))]
    add_initial_constraints_4_2(
        s, syms, inputs, ur,
        allow_weak=bool(spec.get("allow_weak", False))
    )

    R_flags, mix_flags, xor_flags = [], [], []

    def get_pair(ref: str):
        if ":" in ref:
            name, idx = ref.split(":"); idx = int(idx)
        else:
            name, idx = ref, 0
        if name not in outmap or idx >= len(outmap[name]):
            raise ValueError(f"Unknown ref '{ref}'")
        return outmap[name][idx], botmap[name][idx]

    # 3) build graph
    for node in spec["nodes"]:
        op = node["op"].upper(); name = node["name"]

        if op == "SPLIT":
            t, b = get_pair(node["in"])
            k = int(node.get("k", 2))
            outs = split_k(s, t, k, base=f"{name}:")
            outmap[name] = outs
            botmap[name] = [b for _ in range(k)]  # ⊥ copy

        elif op == "R":
            t, b_in = get_pair(node["in"])
            out, s_i, mix_i, b_core = add_R_node(
                s, syms, t, name=name,
                monotone_guard=bool(spec.get("monotone_guard", True))
            )
            # ⊥ 吸收：R 的 ⊥ = 上游 ⊥  OR  R 内部规则产生的 ⊥
            b_out = s.mkConst(s.getBooleanSort(), f"bot_{name}_absorb")
            s.assertFormula(Eq(s, b_out, Or2(s, b_core, b_in)))
            outmap[name] = [out]
            botmap[name] = [b_out]
            R_flags.append(s_i)
            mix_flags.append(mix_i)

        elif op == "XOR":
            a, ba = get_pair(node["a"])
            b, bb = get_pair(node["b"])
            if not spec.get("collisions", True):
                out, xflag, bw = add_XOR_node_no_collision(s, a, b, name=name, Abot=ba, Bbot=bb)
            else:
                out, xflag, bw = add_XOR_node(s, a, b, name=name, Abot=ba, Bbot=bb)
            outmap[name] = [out]
            botmap[name] = [bw]
            xor_flags.append(xflag)

        else:
            raise ValueError(f"Unsupported op: {op}")

    # 4) bind UR to real tails (so §4.2 constraints apply to final tails)
    tails_terms = []
    for i, ref in enumerate(tails_specs):
        t, _b = get_pair(ref)
        tails_terms.append(t)
        s.assertFormula(Eq(s, ur[i], t))

    # 5) global Eq.(6)(7): earliest-wins & exactly-once-once-mix (conditional)
    if spec.get("sum1", True) and R_flags:
        # at most one s_i
        at_most_one(s, R_flags)
        # if any mixture appears ⇒ at least one s_i
        any_mix = big_or(s, mix_flags)
        any_s   = big_or(s, R_flags)
        s.assertFormula(Imp(s, any_mix, any_s))
        # earliest-wins
        for j in range(len(R_flags)):
            if j > 0:
                earlier_no_mix = None
                for k in range(j):
                    nm = Not(s, mix_flags[k])
                    earlier_no_mix = nm if earlier_no_mix is None else And2(s, earlier_no_mix, nm)
                s.assertFormula(Imp(s, R_flags[j], earlier_no_mix))
            ej = mix_flags[j]
            for k in range(j):
                ej = And2(s, ej, Not(s, mix_flags[k]))
            s.assertFormula(Imp(s, ej, R_flags[j]))

    return s, dict(
        inputs=inputs, ur=ur, syms=syms,
        outmap=outmap, botmap=botmap,
        R_flags=R_flags, mix_flags=mix_flags, xor_flags=xor_flags
    )

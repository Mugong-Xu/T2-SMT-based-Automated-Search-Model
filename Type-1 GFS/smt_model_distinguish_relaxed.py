#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from cvc5 import Solver, Kind

BVW = 5  # bits: [0s, R(x), x, R(δ), δ] viewed via masks 16,8,4,2,1
MASK_DELTA = 1
MASK_RDEL  = 2
MASK_X     = 4
MASK_RX    = 8
MASK_0S    = 16

def mk_bv(s, val): return s.mkBitVector(BVW, val)

def R_transform(s, in_bv):
    """Relaxed R mapping (multi-hot allowed, no bot unless you assert it):
       δ   -> R(δ)        (1 -> 2)
       R(δ)-> R(δ)        (2 -> 2)
       x   -> R(x)        (4 -> 8)
       R(x)-> R(x)        (8 -> 8)
       0s  -> 0s          (16-> 16)
       δ,x 位被消去；其像叠加到 R(δ),R(x) 上；0s 保持。
    """
    zero = mk_bv(s, 0)
    d   = mk_bv(s, MASK_DELTA)
    rd  = mk_bv(s, MASK_RDEL)
    x   = mk_bv(s, MASK_X)
    rx  = mk_bv(s, MASK_RX)
    z   = mk_bv(s, MASK_0S)

    in_has = lambda m: s.mkTerm(Kind.DISTINCT, s.mkTerm(Kind.BITVECTOR_AND, in_bv, mk_bv(s,m)), zero)
    # compose outputs
    out = mk_bv(s, 0)
    # Rδ gets δ or Rδ
    cond_rd = s.mkTerm(Kind.OR, in_has(MASK_DELTA), in_has(MASK_RDEL))
    out = s.mkTerm(Kind.ITE, cond_rd, s.mkTerm(Kind.BITVECTOR_OR, out, mk_bv(s, MASK_RDEL)), out)
    # Rx gets x or Rx
    cond_rx = s.mkTerm(Kind.OR, in_has(MASK_X), in_has(MASK_RX))
    out = s.mkTerm(Kind.ITE, cond_rx, s.mkTerm(Kind.BITVECTOR_OR, out, mk_bv(s, MASK_RX)), out)
    # 0s preserved
    cond_z = in_has(MASK_0S)
    out = s.mkTerm(Kind.ITE, cond_z, s.mkTerm(Kind.BITVECTOR_OR, out, mk_bv(s, MASK_0S)), out)
    return out

def build_from_graph(spec: dict):
    """Minimal relaxed builder.
       spec: {n_inputs:int, nodes:[{op:'R'|'XOR', name:str, in/a/b:str}], tails:[str]}
       Returns (solver, env) where
         env['inputs'] -> list of BV nodes
         env['outmap'][name] -> (BV,)
         env['botmap'][name] -> (Bool,)  (all False by default; not auto-propagated)
    """
    s = Solver()
    s.setLogic("QF_BV")
    s.setOption("produce-models", "true")
    outmap = {}
    botmap = {}
    inputs = []

    # Create input BV vars (unconstrained)
    for i in range(spec.get("n_inputs", 0)):
        bv = s.mkConst(s.mkBitVectorSort(BVW), f"inp_{i}")
        outmap[f"u0_{i}"] = (bv,)  # name inputs as u0_0..u0_{n-1}
        botmap[f"u0_{i}"] = (s.mkFalse(),)
        inputs.append(bv)

    def get_bv(name):
        return outmap[name][0]

    # Build nodes
    for node in spec.get("nodes", []):
        op = node["op"].upper()
        name = node["name"]
        bot = s.mkFalse()
        if op == "R":
            in_name = node["in"]
            in_bv = get_bv(in_name)
            out_bv = R_transform(s, in_bv)
        elif op == "XOR":
            a = get_bv(node["a"]); b = get_bv(node["b"])
            out_bv = s.mkTerm(Kind.BITVECTOR_XOR, a, b)
        else:
            raise ValueError(f"Unknown op {op}")
        outmap[name] = (out_bv,)
        botmap[name] = (bot,)

    syms = {
        "ZERO": mk_bv(s, 0),
        "DELTA": mk_bv(s, MASK_DELTA),
        "RDELTA": mk_bv(s, MASK_RDEL),
        "X": mk_bv(s, MASK_X),
        "RX": mk_bv(s, MASK_RX),
        "ZEROS": mk_bv(s, MASK_0S),
    }

    env = dict(inputs=inputs, outmap=outmap, botmap=botmap, syms=syms, tails=spec.get("tails", []))
    return s, env

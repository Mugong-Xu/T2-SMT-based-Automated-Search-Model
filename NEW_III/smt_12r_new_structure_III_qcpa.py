#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from cvc5 import Kind
import importlib.util, os, sys

MODEL_PATH = os.path.join(os.path.dirname(__file__), "smt_model_distinguish.py")
if not os.path.exists(MODEL_PATH):
    MODEL_PATH = "smt_model_distinguish.py"

def load_user_model(path: str):
    spec = importlib.util.spec_from_file_location("smt_model_distinguish", path)
    if spec is None:
        raise RuntimeError(f"Cannot locate module at {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)  # type: ignore
    return module

# ---------- 打印工具（对齐参考风格） ----------
def decode_symbol_bits(bv_str: str) -> str:
    # 5位: [0]=δ, [1]=R(δ), [2]=x, [3]=R(x), [4]=0s
    if not (isinstance(bv_str, str) and bv_str.startswith("#b")):
        return str(bv_str)
    # 统一填充至5位
    bits = bv_str[2:].zfill(5)[-5:]
    v = int(bits, 2)
    parts = []
    if v & (1 << 0): parts.append("δ")
    if v & (1 << 1): parts.append("R(δ)")
    if v & (1 << 2): parts.append("x")
    if v & (1 << 3): parts.append("R(x)")
    if v & (1 << 4): parts.append("0s")
    return " ⊕ ".join(parts) if parts else "0"

def get_pair(env, ref: str):
    outmap, botmap = env["outmap"], env["botmap"]
    if ":" in ref:
        name, idx = ref.split(":"); idx = int(idx)
    else:
        name, idx = ref, 0
    return outmap[name][idx], botmap[name][idx]

def show_ref(s, env, ref: str, label=None):
    t, b = get_pair(env, ref)
    is_bot = (str(s.getValue(b)).lower() == "true")
    if is_bot:
        print(f"{label or ref}: ⊥")
    else:
        v = s.getValue(t)
        print(f"{label or ref}: {v}  => {decode_symbol_bits(str(v))}")

def main():
    mod = load_user_model(MODEL_PATH)

    # ---------- 构图：10 轮 new structure III ----------
    nodes = []
    rounds = []  # 保存每轮四根线的引用
    # i=0 使用初始输入名 u0_0..u0_3
    rounds.append({"u0": "u0_0", "u1": "u0_1", "u2": "u0_2", "u3": "u0_3"})
    for i in range(12):
        cur = rounds[-1]
        r_name = f"R_{i}"
        x_name = f"X_{i}"
        nodes.append({"op": "R",   "name": r_name, "in": cur["u0"]})
        nodes.append({"op": "XOR", "name": x_name, "a": r_name, "b": cur["u1"]})
        rounds.append({
            "u0": cur["u3"],   # u0^{i+1} = u3^i
            "u1": r_name,      # u1^{i+1} = R(u0^i)
            "u2": x_name,      # u2^{i+1} = R(u0^i) ⊕ u1^i
            "u3": cur["u2"],   # u3^{i+1} = u2^i
        })

    # tails 绑定到最终一轮（第10轮）四根线上，以应用尾部可分离约束
    spec = dict(
        n_inputs=4,
        nodes=nodes,
        tails=[rounds[-1]["u0"], rounds[-1]["u1"], rounds[-1]["u2"], rounds[-1]["u3"]],
        allow_weak=True,    # 可按需切换 False
        sum1=True,          # Eq.(6)(7): 最早且仅一次触发
        monotone_guard=True,
        collisions=True,
    )

    s, env = mod.build_from_graph(spec)

    # ---------- 设定第 0 轮输入 ----------
    # u0^0 = δ, u1^0 = x, u2^0 = 0, u3^0 = 0
    inputs = env["inputs"]
    syms   = env["syms"]
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[0], syms["DELTA"]))
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[1], syms["X"]))
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[2], syms["ZERO"]))
    s.assertFormula(s.mkTerm(Kind.EQUAL, inputs[3], syms["ZERO"]))

    # ---------- 求解与打印 ----------
    res = s.checkSat()
    print("check-sat:", res)
    ok = (str(res) == "sat")
    print("包含量子区分器？", "是" if ok else "否")

    # 逐轮输出（i=0..10）
    for i in range(0, 13):
        print(f"\nRound {i}:")
        show_ref(s, env, rounds[i]["u0"], label=f"u0^{i}")
        show_ref(s, env, rounds[i]["u1"], label=f"u1^{i}")
        show_ref(s, env, rounds[i]["u2"], label=f"u2^{i}")
        show_ref(s, env, rounds[i]["u3"], label=f"u3^{i}")

    # （可选）打印触发/混合/碰撞标志
    if env.get("R_flags"):
        print("\nR 触发位 s_i：")
        for j, sf in enumerate(env["R_flags"]):
            print(f"  s[{j}] =", s.getValue(sf))
    if env.get("mix_flags"):
        print("R 混合位 mix_i：")
        for j, mf in enumerate(env["mix_flags"]):
            print(f"  mix[{j}] =", s.getValue(mf))
    if env.get("xor_flags"):
        print("XOR 碰撞位 xflag_i：")
        for j, xf in enumerate(env["xor_flags"]):
            print(f"  xflag[{j}] =", s.getValue(xf))

if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        print("ERROR:", e)
        sys.exit(1)

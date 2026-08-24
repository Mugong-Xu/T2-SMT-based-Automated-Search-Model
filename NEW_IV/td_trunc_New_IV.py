# -*- coding: utf-8 -*-
"""
td_trunc_New_IV.py
使用 td_trunc_opt.py 里的模型，按“new structure IV”规则运行 11 轮并打印每一轮的 symbol。

递推关系：
u0^{i+1} = R(u3^i)
u1^{i+1} = u3^i ⊕ u0^i
u2^{i+1} = u1^i ⊕ u3^i
u3^{i+1} = u2^i

初始：u0^0 = a, u1^0 = a⊕s, u2^0 = 0, u3^0 = a
"""

from td_trunc_opt import TDEngine, Val, Sym

def run_new_structure_iv(rounds: int = 11) -> None:
    eng = TDEngine()

    # 初始符号
    u0 = Val(Sym.A)        # a
    u1 = Val(Sym.AS)       # a⊕s
    u2 = Val(Sym.ZERO)     # 0
    u3 = Val(Sym.A)        # a

    for i in range(1, rounds + 1):
        # 递推
        u0_new = eng.R(u3)           # u0^{i+1}
        u1_new = eng.xor2(u3, u0)    # u1^{i+1}
        u2_new = eng.xor2(u1, u3)    # u2^{i+1}
        u3_new = u2                  # u3^{i+1}

        print(f"Round {i}: u_0 = {u0_new}, u_1 = {u1_new}, u_2 = {u2_new}, u_3 = {u3_new}")

        # 更新到下一轮
        u0, u1, u2, u3 = u0_new, u1_new, u2_new, u3_new

if __name__ == '__main__':
    run_new_structure_iv()

"""Arb Taylor jets through degree four in the 25 gauge coordinates.

Used by audit_local.py, which proves all norm bounds by rational matrix
checks and Arb error bounds. This module supplies coefficients only.
"""
import math
from fractions import Fraction as Fr
from flint import arb, ctx
ctx.prec = 200
HS = arb('0.45536779516246300350924502372107445741075259468695') + arb(0, 1e-45)
PI = arb.pi()
ORD = 4
class Jet:
    """truncated Taylor polynomial in nv variables, total order <= ORD; coefficients arb"""
    def __init__(s, nv, c=None): s.nv = nv; s.c = c if c is not None else {}
    @staticmethod
    def const(nv, a): return Jet(nv, {(0,) * nv: arb(a)})
    @staticmethod
    def var(nv, i, a):
        e = [0] * nv; e[i] = 1; return Jet(nv, {(0,) * nv: arb(a), tuple(e): arb(1)})
    def __add__(s, o):
        if not isinstance(o, Jet): o = Jet.const(s.nv, o)
        c = dict(s.c)
        for k, v in o.c.items(): c[k] = c[k] + v if k in c else v
        return Jet(s.nv, c)
    __radd__ = __add__
    def __neg__(s): return Jet(s.nv, {k: -v for k, v in s.c.items()})
    def __sub__(s, o): return s + (-o if isinstance(o, Jet) else -arb(o))
    def __rsub__(s, o): return (-s) + o
    def __mul__(s, o):
        if not isinstance(o, Jet): return Jet(s.nv, {k: v * o for k, v in s.c.items()})
        c = {}
        for k1, v1 in s.c.items():
            d1 = sum(k1)
            for k2, v2 in o.c.items():
                if d1 + sum(k2) > ORD: continue
                k = tuple(a + b for a, b in zip(k1, k2)); p = v1 * v2
                c[k] = c[k] + p if k in c else p
        return Jet(s.nv, c)
    __rmul__ = __mul__
    def x0(s): return s.c.get((0,) * s.nv, arb(0))
    def nil(s): return Jet(s.nv, {k: v for k, v in s.c.items() if sum(k) > 0})
    def apply(s, derivs):
        """f(s) = sum_k derivs[k]/k! * nil^k, derivs[k] = f^(k)(x0)"""
        N = s.nil(); out = Jet.const(s.nv, 0) + derivs[0]; P = Jet.const(s.nv, 1)
        for k in range(1, ORD + 1):
            P = P * N; out = out + P * (derivs[k] / math.factorial(k))
        return out
    def power(s, al):
        x = s.x0(); d = []; c = arb(1)
        for k in range(ORD + 1):
            d.append(c * x ** (arb(al) - k)); c = c * (arb(al) - k)
        return s.apply(d)
    def cos(s):
        x = s.x0(); cs, sn = x.cos(), x.sin(); return s.apply([cs, -sn, -cs, sn, cs][:ORD + 1])
    def sin(s):
        x = s.x0(); cs, sn = x.cos(), x.sin(); return s.apply([sn, cs, -sn, -cs, sn][:ORD + 1])
def gauge_params(r):
    """list of 25 (value ball) and point -> param index map"""
    def b(m): return arb(m) + arb(0, r) if r > 0 else arb(m)
    p = [b(0), b(0), HS + (arb(0, r) if r > 0 else 0)]
    for i in range(3, 14):
        if i <= 7: z = HS; th = (i - 2) * PI / 3
        else: z = -HS; th = (i - 8) * PI / 3 + PI / 6
        p.append(z + (arb(0, r) if r > 0 else 0)); p.append(th + (arb(0, r) if r > 0 else 0))
    own = {0: [], 1: [0, 1], 2: [2]}
    for i in range(3, 14): own[i] = [3 + 2 * (i - 3), 4 + 2 * (i - 3)]
    return p, own
def point_jet(i, p, loc, nv):
    """jet of point i in local variables; loc maps global param index -> local var index"""
    if i == 0: return [Jet.const(nv, 0), Jet.const(nv, 0), Jet.const(nv, 1)]
    if i == 1:
        a = Jet.var(nv, loc[0], p[0]); b = Jet.var(nv, loc[1], p[1])
        w = (1 - a * a - b * b).power(0.5); return [a, b, -w]
    if i == 2:
        z = Jet.var(nv, loc[2], p[2]); rho = (1 - z * z).power(0.5); return [rho, Jet.const(nv, 0), z]
    kz = 3 + 2 * (i - 3)
    z = Jet.var(nv, loc[kz], p[kz]); th = Jet.var(nv, loc[kz + 1], p[kz + 1])
    rho = (1 - z * z).power(0.5); return [rho * th.cos(), rho * th.sin(), z]
def pair_jets(r):
    p, own = gauge_params(r); out = []
    for i in range(14):
        for j in range(i + 1, 14):
            g = own[i] + own[j]; nv = max(1, len(g)); loc = {k: n for n, k in enumerate(g)}
            xi = point_jet(i, p, loc, nv); xj = point_jet(j, p, loc, nv)
            s = xi[0] * xj[0] + xi[1] * xj[1] + xi[2] * xj[2]
            f = (2 - 2 * s).power(-0.5)
            out.append((i, j, g, f))
    return out

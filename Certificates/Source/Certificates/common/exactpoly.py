# exact rational polynomial utilities in 3 variables (dict {(a,b,c): Fraction}) and Chebyshev conversions
from fractions import Fraction as Fr
from math import comb
from collections import defaultdict
import itertools
def padd(*ps):
    r=defaultdict(Fr)
    for p in ps:
        for k,v in p.items(): r[k]+=v
    return {k:v for k,v in r.items() if v!=0}
def pscale(p,s): return {k:v*s for k,v in p.items()} if s!=0 else {}
def pmul(p,q):
    r=defaultdict(Fr)
    for k1,v1 in p.items():
        for k2,v2 in q.items(): r[(k1[0]+k2[0],k1[1]+k2[1],k1[2]+k2[2])]+=v1*v2
    return {k:v for k,v in r.items() if v!=0}
def var(i):
    e=[0,0,0]; e[i]=1; return {tuple(e):Fr(1)}
ONE={(0,0,0):Fr(1)}
def cheb_poly(n, i):
    """T_n(x_i) as exact polynomial in variable i"""
    T=[ONE, var(i)]
    for k in range(2,n+1): T.append(padd(pscale(pmul(var(i),T[-1]),2), pscale(T[-2],-1)))
    return T[:n+1]
def permute(p, perm):
    """substitute (x0,x1,x2) -> (x_perm0, x_perm1, x_perm2): monomial u^a v^b t^c with u=X[perm0]..."""
    r=defaultdict(Fr)
    for (a,b,c),v in p.items():
        e=[0,0,0]; e[perm[0]]+=a; e[perm[1]]+=b; e[perm[2]]+=c; r[tuple(e)]+=v
    return dict(r)
def subst_diag(p):
    """(u,v,t)->(w,w,1) returning univariate dict in variable 0"""
    r=defaultdict(Fr)
    for (a,b,c),v in p.items(): r[(a+b,0,0)]+=v
    return {k:v for k,v in r.items() if v!=0}
def mono_to_cheb_1d(n):
    """x^n = sum_k M[n][k] T_k(x)"""
    M={}
    for k in range(n%2, n+1, 2):
        j=(n-k)//2
        M[k]= Fr(comb(n,j), 2**(n-1)) if k>0 else Fr(comb(n,n//2), 2**n)
    return M
def to_cheb(p):
    cache={}
    r=defaultdict(Fr)
    for (a,b,c),v in p.items():
        for (x,y) in ((a,None),):
            pass
        Ma=cache.setdefault(a,mono_to_cheb_1d(a)); Mb=cache.setdefault(b,mono_to_cheb_1d(b)); Mc=cache.setdefault(c,mono_to_cheb_1d(c))
        for i,ci in Ma.items():
            for j,cj in Mb.items():
                for k,ck in Mc.items(): r[(i,j,k)]+=v*ci*cj*ck
    return {k:v for k,v in r.items() if v!=0}
def ldl_psd(F):
    """exact LDL^T; returns True iff F (list of lists of Fraction) is positive definite"""
    n=len(F); A=[row[:] for row in F]
    for k in range(n):
        if A[k][k]<=0: return False
        for i in range(k+1,n):
            f=A[i][k]/A[k][k]
            for j in range(k+1,n): A[i][j]-=f*A[k][j]
    return True
def fr_down(x):   # largest double <= Fraction x
    import math
    d=float(x)
    while Fr(d)>x: d=math.nextafter(d,-math.inf)
    return d
def fr_up(x):
    import math
    d=float(x)
    while Fr(d)<x: d=math.nextafter(d,math.inf)
    return d

"""P/R cap domains, permutation symmetries and conservative affine cuts."""
import math
from fractions import Fraction as Fr
HI=-0.99
S3=[(1,0,2),(0,2,1),(2,1,0),(1,2,0),(2,0,1)]
import os
TMAX=float(os.environ.get('TMAX','1.0'))      # a-priori separation (Case 0 lemma): all inner products <= TMAX; 1.0 = no cut
def config(typing):
    if typing=='PR':
        P={(0,0,1):('PPR',[(0,2,1)],[(0,0,0,-1.0),(1,0,0,HI),(2,1,0,0.0),(2,2,1,0.0)],((-1.0,-1.0,-1.0),(HI,1.0,1.0))),
           (0,1,1):('PRR',[(1,0,2)],[(2,1,0,0.0)],((-1.0,-1.0,-1.0),(1.0,1.0,1.0))),
           (1,1,1):('RRR',S3,[(2,1,0,0.0),(2,2,1,0.0)],((-1.0,-1.0,-1.0),(1.0,1.0,1.0)))}
        if TMAX<1.0:
            # every inner product of the configuration is <= TMAX: upper cuts (kind 1: x_i <= val) and smaller root boxes.
            # In the fundamental domains the largest coordinate is t (PPR: t >= v >= u; RRR: t >= v >= u) or v/t (PRR: v >= u).
            # Moreover <P,x> = <P+Q,x> - <Q,x> > -|P+Q| - TMAX >= -(sqrt(2+2*HI) + TMAX) for every R point x (and the same
            # with P and Q exchanged): lower cuts PRLOW for the P-R coordinates (PPR: v,t; PRR: u,v), rounded outward.
            PRLOW=-(math.sqrt(2+2*HI)+TMAX); PRLOW=(math.floor(PRLOW*1e4)-1)/1e4      # -0.9416 for TMAX=0.8 (checked exactly below)
            assert Fr(PRLOW)<=-(Fr(TMAX)+Fr(1415,10000)) and Fr(1415,10000)**2>=2+2*Fr(HI)
            prc={(0,0,1):(1,2),(0,1,1):(0,1),(1,1,1):()}
            Q={}
            for p,(name,perms,cuts,(lo3,hi3)) in P.items():
                extra=[(1,i,0,TMAX) for i in range(3) if hi3[i]>TMAX]+[(0,i,0,PRLOW) for i in prc[p]]
                Q[p]=(name,perms,cuts+extra,(lo3,tuple(min(h,TMAX) for h in hi3)))
            P=Q
    else: raise ValueError(typing)
    return P
def edge_pattern(typing):
    """pattern whose first pair is the minimal pair (u=<P,Q> in [-1,HI]); its X* nodes lie on the edge u=-1, G=0"""
    assert typing == 'PR'
    return (0,0,1)
def in_fd(cuts,s,tol=1e-12):
    """is the point s in the closed domain given by the cuts (tolerance tol)?"""
    for kind,i,j,val in cuts:
        if kind==0 and s[i]<val-tol: return False
        if kind==1 and s[i]>val+tol: return False
        if kind==2 and s[i]<s[j]-tol: return False
    return True
def cut_affine(kind,i,j,val):
    """cut as (a,b0) with a.x + b0 >= 0 (exact rationals)"""
    a=[0,0,0]
    if kind==0: a[i]=1; return a,-Fr(val)
    if kind==1: a[i]=-1; return a,Fr(val)
    a[i]=1; a[j]=-1; return a,Fr(0)

# Write branch-and-bound inputs (problem file + exact root Taylor data) for the three typed slack patterns of a slab [lo,hi].
#   PPR (P,Q,r): u=<P,Q> in [lo,hi], v=<P,r>, t=<Q,r>;  v >= u, and t >= v by the P<->Q symmetry of the slack.
#   PRR (p,r,r'): u,v,t >= lo;  v >= u by symmetry.     RRR: u,v,t >= lo;  u <= v <= t by symmetry.
# usage: run_typed_ts.py certificate.json lo hi nroot_u nroot prefix
import sys, math
from certificate_io import load_certificate
from fractions import Fraction as Fr
from exactpoly import fr_down, fr_up
from prep_roots import shift1
def gram_possible_LH(L,H):
    """RIGOROUS: False only if 1+2uvt-u^2-v^2-t^2 < 0 on the whole cell [L,H] (exact rationals)"""
    mx=max(x*y*z for x in (L[0],H[0]) for y in (L[1],H[1]) for z in (L[2],H[2]))
    def minsq(a,b): return Fr(0) if a<=0<=b else min(a*a,b*b)
    return 1+2*mx-minsq(L[0],H[0])-minsq(L[1],H[1])-minsq(L[2],H[2])>=0
def cell_ok(L,H,cuts):
    for kind,i,j,val in cuts:
        if kind==0 and H[i]<Fr(val): return False
        if kind==1 and L[i]>Fr(val): return False
        if kind==2 and H[i]<L[j]: return False
    return True
def write_roots(P, D, lo3, hi3, ns, cuts, out):
    """root cells tile the box exactly; Taylor data exact at the DOUBLE center; radius covers the cell (rounded up)"""
    w=[(Fr(hi3[i])-Fr(lo3[i]))/ns[i] for i in range(3)]; roots=[]
    for i in range(ns[0]):
        for j in range(ns[1]):
            for k in range(ns[2]):
                L=[Fr(lo3[a])+idx*w[a] for a,idx in zip(range(3),(i,j,k))]; H=[L[a]+w[a] for a in range(3)]
                if not cell_ok(L,H,cuts) or not gram_possible_LH(L,H): continue
                cf=[float((L[a]+H[a])/2) for a in range(3)]
                rad=[fr_up(max(Fr(cf[a])-L[a],H[a]-Fr(cf[a]))) for a in range(3)]
                Q=P
                for ax in range(3): Q=shift1(Q,ax,Fr(cf[ax]))
                roots.append((cf,rad,Q))
    with open(out,'w') as f:
        f.write(f'{len(roots)}\n')
        for cf,rf,Q in roots:
            f.write(' '.join(repr(x) for x in cf)+' '+' '.join(repr(x) for x in rf)+'\n')
            for a in range(D+1):
                for b in range(D+1-a):
                    for c in range(D+1-a-b):
                        v=Q.get((a,b,c),Fr(0)); f.write(f'{fr_down(v)!r} {fr_up(v)!r}\n')
    return len(roots)
def write_problem(D, phiw, cuts, minw, out):
    with open(out,'w') as f:
        f.write(f'{D}\n{len(phiw)}\n')
        for q,wt in phiw: f.write(f'{q} {fr_down(wt)!r} {fr_up(wt)!r}\n')
        f.write(f'{len(cuts)}\n')
        for kind,i,j,val in cuts: f.write(f'{kind} {i} {j} {val!r}\n')
        f.write(f'{minw!r}\n')
if __name__=='__main__':
    pk,lo,hi,nu,nr,prefix=sys.argv[1],float(sys.argv[2]),float(sys.argv[3]),int(sys.argv[4]),int(sys.argv[5]),sys.argv[6]
    res=load_certificate(pk); D=res['D']
    specs={
      'PPR':((lo,lo,lo),(hi,1.0,1.0),(nu,nr,nr),[(0,0,0,lo),(1,0,0,hi),(2,1,0,0.0),(2,2,1,0.0)]),
      'PRR':((lo,lo,lo),(1.0,1.0,1.0),(nr,nr,nr),[(0,0,0,lo),(0,1,0,lo),(0,2,0,lo),(2,1,0,0.0)]),
      'RRR':((lo,lo,lo),(1.0,1.0,1.0),(nr,nr,nr),[(0,0,0,lo),(0,1,0,lo),(0,2,0,lo),(2,1,0,0.0),(2,2,1,0.0)])}
    for pat,(lo3,hi3,ns,cuts) in specs.items():
        P,phiw=res['slacks'][{'PPR':(0,0,1),'PRR':(0,1,1),'RRR':(1,1,1)}[pat]]
        n=write_roots(P,D,lo3,hi3,ns,cuts,f'{prefix}_{pat}_roots.txt')
        write_problem(D,phiw,cuts,1e-9,f'{prefix}_{pat}_ts.txt')
        print(pat,'roots',n,flush=True)

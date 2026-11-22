# Global cap inputs: positivity outside the balls covered by the local node runs.
# Usage: make_cap_global4.py certificate.json cellwidth rho theta r_inc prefix
# The proof uses r_inc=inf, so there is no restriction to an include region.
import sys, os, math
from certificate_io import load_certificate
from fractions import Fraction as Fr
from run_typed_ts import write_roots, write_problem
import capcfg
TYPING=os.environ.get('TYPING','PR'); CFG=capcfg.config(TYPING)
cap=load_certificate(sys.argv[1]); cw=float(sys.argv[2]); rho=float(sys.argv[3]); theta=float(sys.argv[4]); rinc=float(sys.argv[5]); prefix=sys.argv[6]
D=max(sum(k) for P,_ in cap['slacks'].values() for k in P)
for p,(name,perms,cuts,(lo3,hi3)) in CFG.items():
    P,phiw=cap['slacks'][p]
    ns=[max(1,math.ceil((hi3[i]-lo3[i])/cw-1e-9)) for i in range(3)]
    nodes=[[float(Fr(x)) for x in sq] for (pp,sv,sq) in cap['nodes'] if tuple(pp)==p]
    balls=[s for s in nodes if capcfg.in_fd(cuts,s)]
    # nodes outside the fundamental domain must stay at distance > rho from it (otherwise their small balls would be needed too)
    n=write_roots(P,D,lo3,hi3,ns,cuts,f'{prefix}_{name}_roots.txt')
    write_problem(D,phiw,cuts,1e-10,f'{prefix}_{name}_ts.txt')
    with open(f'{prefix}_{name}_ts.txt','a') as f:
        f.write(f'{theta!r}\n{len(balls)}\n')
        for b in balls: f.write(f'{b[0]!r} {b[1]!r} {b[2]!r} {rho!r}\n')
        included=nodes if math.isfinite(rinc) else []
        f.write(f'{len(included)}\n')
        for b in included: f.write(f'{b[0]!r} {b[1]!r} {b[2]!r} {rinc!r}\n')
    print(name,'grid',ns,'roots',n,' excluded balls',len(balls),' include balls',len(included),flush=True)

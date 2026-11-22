# Verifier inputs for the separation lemma (Case 0), from the exact untyped slack polynomial :
#   run "pos"  : lambda >= 0    on the fundamental domain {-1 <= u <= v <= t <= 1, Gram >= 0}
#   run "close": lambda >= c_v  on the same set intersected with {t >= T0}
#   (the slack is S3-symmetric, so max(u,v,t) >= T0 becomes t >= T0 in the fundamental domain).
# Consequence (identity 4(E-e) = sum_T lambda_T + PSD): a configuration with a pair of inner product >= T0 has
#   E >= e + 3 c_v   (the 12 triples through that pair are in the close set, all other slacks are >= 0).
# usage: make_case0.py certificate.json n T0 c_v prefix          (T0 and c_v are used as the doubles given; c_v is the threshold)
import sys
from fractions import Fraction as Fr
from run_typed_ts import write_roots, write_problem
from exactpoly import permute as substitute
from certificate_io import load_certificate
P=load_certificate(sys.argv[1])['slacks'][(0,0,0)][0]; n=int(sys.argv[2]); T0=float(sys.argv[3]); cv=float(sys.argv[4]); pre=sys.argv[5]
D=max(sum(k) for k in P)
for perm in [(1,0,2),(0,2,1),(2,1,0),(1,2,0),(2,0,1)]:
    assert substitute(P,perm)==P, 'slack polynomial not exactly symmetric'
print('exact S3 symmetry of the slack polynomial: OK; degree',D,flush=True)
lo=-1.0
cuts=[(0,0,0,lo),(0,1,0,lo),(0,2,0,lo),(2,1,0,0.0),(2,2,1,0.0)]
phiw=[(0,Fr(1,3)),(1,Fr(1,3)),(2,Fr(1,3))]
nr=write_roots(P,D,(lo,lo,lo),(1.0,1.0,1.0),(n,n,n),cuts,pre+'_roots.txt')
write_problem(D,phiw,cuts,1e-9,pre+'_pos_ts.txt')
cuts2=cuts+[(0,2,0,T0)]
write_problem(D,phiw,cuts2,1e-9,pre+'_close_ts.txt')
with open(pre+'_close_ts.txt','a') as f: f.write(f'{cv!r}\n0\n')
print('roots',nr,'; close run: t >=',repr(T0),', threshold',repr(cv),flush=True)

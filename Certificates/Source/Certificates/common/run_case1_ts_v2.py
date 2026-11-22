# Case 1 verifier input, v2: root cells tile [lo,1]^3 exactly, exact Taylor data at the DOUBLE centers, covering radii,
# fundamental domain u <= v <= t (the slack is exactly S3-symmetric; checked here on the exact polynomial).
import sys
from fractions import Fraction as Fr
from run_typed_ts import write_roots, write_problem
from exactpoly import permute as substitute
from certificate_io import load_certificate
P=load_certificate(sys.argv[1])['slacks'][(0,0,0)][0]; n=int(sys.argv[2]); lo=float(sys.argv[3]) if len(sys.argv)>3 else -0.9; pre=sys.argv[4] if len(sys.argv)>4 else 'case1v2'
D=max(sum(k) for k in P)
for perm in [(1,0,2),(0,2,1),(2,1,0),(1,2,0),(2,0,1)]:
    assert substitute(P,perm)==P, 'slack polynomial not exactly symmetric'
print('exact S3 symmetry of the Case 1 slack polynomial: OK',flush=True)
cuts=[(0,0,0,lo),(0,1,0,lo),(0,2,0,lo),(2,1,0,0.0),(2,2,1,0.0)]
nr=write_roots(P,D,(lo,lo,lo),(1.0,1.0,1.0),(n,n,n),cuts,pre+'_roots.txt')
write_problem(D,[(0,Fr(1,3)),(1,Fr(1,3)),(2,Fr(1,3))],cuts,1e-9,pre+'_ts.txt')
print('roots',nr,'degree',D)

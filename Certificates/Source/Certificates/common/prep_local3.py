# Local verification data around the X* nodes (input for bnb_local), from an exact rational cap certificate.
#   lambda(s~+h) = Q(h) + phi-remainder,  Q = exact Taylor polynomial of the polynomial part at the rational node s~
#                  plus the phi part to degree D with rational coefficients; |remainder| <= eps for |h| <= R_out
#                  (arb enclosures: coefficient radii + geometric tail).
#   h = M y, with the rational matrix M supplied in certificate.json and checked exactly;
#   Ly = Q(M y), Gy = Gram(s~ + M y) composed EXACTLY;  cuts a.x+b >= 0 rewritten exactly in y and rounded
#   conservatively (constant raised by the coefficient rounding error times max|y_j| on the local region).
#   Local region E = {sum (y_i/s_i)^2 <= 1}.  Exact (LDL) checks:
#     (i)   |My| <= R_out on E                      (R_out^2 S^-2 - M^T M  PSD)      -> remainder bound valid on E
#     (ii)  E contains M^-1 B(0, rho_g)             (M^T M - rho_g^2 S^-2  PSD)      -> global run may exclude B(s~,rho_g - 1e-14)
#     (iii) ||M||_2 <= c_M                          (c_M^2 I - M^T M  PSD)           -> |h| <= c_M |y|
#   Inner node lemma (arb, rigorous), on the S-procedure Lagrangian Lq = Ly - m_G Gy (m_G >= 0, Gy >= 0 on the domain):
#     Lq = c0 + g.y + y^T Hq y/2 + R,  Hq - (9/10) I PD (exact LDL),  |R| <= Mr |y|^3 on |y| <= y_in with Mr y_in <= 0.225
#     =>  lambda >= Lq - eps >= c0 - eps - |g||y| + 0.225|y|^2  on |y| <= y_in:
#         lambda >= 0 there (needs c0 - eps - |g|^2/0.45 >= 0), and lambda >= theta for y_tin <= |y| <= y_in,
#         y_tin = |g|/0.225 + sqrt((theta+eps)/0.225)  (the printed y_tin is min(y_tin, y_in): if y_tin > y_in the
#         whole ball |y| <= y_in belongs to the tube).
# usage: prep_local3.py certificate.json theta R_out rho_g outdir [i,j,k | all]     (env TYPING=PR; patterns/cuts from capcfg.py)
import sys, os, pickle, math, itertools
from certificate_io import load_certificate
from fractions import Fraction as Fr
from flint import arb, ctx
ctx.prec=300
from prep_roots import shift1
from exactpoly import fr_down, fr_up, ldl_psd
import capcfg
TYPING=os.environ.get('TYPING','PR'); CFG=capcfg.config(TYPING); EDGEP=capcfg.edge_pattern(TYPING)
cap=load_certificate(sys.argv[1]); theta=Fr(float(sys.argv[2])); Rout=Fr(sys.argv[3]); rho_g=Fr(sys.argv[4]); outdir=sys.argv[5]
SELARG=sys.argv[6] if len(sys.argv)>6 else "all"
sel=None if SELARG=="all" or SELARG.startswith("mod") else set(int(x) for x in SELARG.split(","))
MODN,MODI=(int(SELARG[3:].split("_")[0]),int(SELARG[3:].split("_")[1])) if SELARG.startswith("mod") else (1,0)
fdcount=0
os.makedirs(outdir,exist_ok=True)
D=max(sum(k) for P,_ in cap['slacks'].values() for k in P)
def A(q): return arb(q.numerator)/arb(q.denominator)
def arb_exact_fr(a):
    m,e=a.man_exp(); m=int(m); e=int(e)
    return Fr(m)*Fr(2)**e if e>=0 else Fr(m,2**(-e))
def arb_up(a): return arb_exact_fr(a.upper())
def arb_lo(a): return arb_exact_fr(a.lower())
def padd(a,b,s=1):
    r=dict(a)
    for k,v in b.items(): r[k]=r.get(k,Fr(0))+s*v
    return {k:v for k,v in r.items() if v!=0}
def compose(P,M):
    """Exact substitution P(M y) in the rational polynomial ring."""
    from rational_compose import linear_compose
    return linear_compose(P,M)
Gpoly={(0,0,0):Fr(1),(1,1,1):Fr(2),(2,0,0):Fr(-1),(0,2,0):Fr(-1),(0,0,2):Fr(-1)}
def taylor(P,s):
    Q=P
    for ax in range(3): Q=shift1(Q,ax,s[ax])
    return Q
def matmul(X,Y): return [[sum((X[i][k]*Y[k][j] for k in range(3)),Fr(0)) for j in range(3)] for i in range(3)]
def tr(X): return [[X[j][i] for j in range(3)] for i in range(3)]
CUTS={p:[capcfg.cut_affine(*c) for c in CFG[p][2]] for p in CFG}
summary={}
for ni,(p,sv,sq) in enumerate(cap['nodes']):
    p=tuple(p); P,phiw=cap['slacks'][p]; s=[Fr(v) for v in sq]
    us,vs,ts=[float(x) for x in s]
    if not capcfg.in_fd(CFG[p][2],[us,vs,ts]): continue                 # fundamental domain (images by symmetry)
    fdcount+=1
    if (fdcount-1)%MODN!=MODI: continue
    if sel is not None and ni not in sel: continue
    Q=taylor(P,s); eps=Fr(0)
    for qi,w in phiw:
        assert w>0
        om=1-A(s[qi]); ph=1/(2*om).sqrt(); beta=arb(1); errsum=arb(0)
        for k in range(D+1):
            if k>0: beta=beta*(2*k-1)/(2*k)
            c=A(w)*ph*beta/om**k; cf=arb_exact_fr(c.mid()); e=[0,0,0]; e[qi]=k; e=tuple(e)
            Q[e]=Q.get(e,Fr(0))+cf
            errsum+=c.rad()*A(Rout)**k
        qq=A(Rout)/om; assert qq<arb('0.5')
        tail=A(w)*ph*qq**(D+1)/(1-qq)
        eps+=arb_up(tail+errsum)
    eps+=Fr(1,10**60)
    # These are rational certificate proposals, not numerical assumptions.
    # Every property used below is checked exactly or with Arb bounds.
    proposal=cap['local_coordinates'][ni]
    M=proposal['M']; cM=proposal['cM']
    sc=[float(q) for q in proposal['sc']]
    assert all(Fr(sc[i])==proposal['sc'][i] for i in range(3))
    assert cM>0
    S2inv=[Fr(1)/q**2 for q in proposal['sc']]
    mGq=proposal['mG']; nuq=proposal['nu']
    assert mGq>=0 and nuq>=0
    bnd=proposal['kind']!='int'; edge=proposal['kind']=='edge'
    assert bnd or (mGq==0 and nuq==0)
    assert edge or nuq==0
    assert not edge or p==EDGEP
    GQ=taylor(Gpoly,s)
    MtM=matmul(tr(M),M)
    chk1=ldl_psd([[(Rout**2*S2inv[i] if i==j else 0)-MtM[i][j] for j in range(3)] for i in range(3)])
    rho2=(rho_g+Fr(1,10**14))**2
    chk2=ldl_psd([[MtM[i][j]-(rho2*S2inv[i] if i==j else 0) for j in range(3)] for i in range(3)])
    chk3=ldl_psd([[(cM**2 if i==j else 0)-MtM[i][j] for j in range(3)] for i in range(3)])
    assert chk1 and chk2 and chk3, ('coordinate containment failed',ni)
    # Each operation in compose is a polynomial-ring homomorphism. Checking
    # its values on 1 and the three generators proves the stated substitution.
    assert compose({(0,0,0):Fr(1)},M)=={(0,0,0):Fr(1)}
    for i in range(3):
        ei=tuple(int(j==i) for j in range(3))
        expected={tuple(int(j==k) for j in range(3)):M[i][k] for k in range(3) if M[i][k]}
        assert compose({ei:Fr(1)},M)==expected
    Ly=compose(Q,M); Gy=compose(GQ,M)
    # ---- inner node lemma (rigorous)
    Lq=padd(Ly,Gy,-mGq) if bnd else Ly
    if edge:                                     # S-procedure term nu*(u+1), u+1 >= 0 on the domain
        Lq=padd(Lq,{(0,0,0):s[0]+1,(1,0,0):M[0][0],(0,1,0):M[0][1],(0,0,1):M[0][2]},-nuq)
    c0=Lq.get((0,0,0),Fr(0)); gy=[Lq.get(tuple(int(i==a) for i in range(3)),Fr(0)) for a in range(3)]
    Hq=[[Lq.get(tuple(int(i==a)+int(i==b) for i in range(3)),Fr(0))*(2 if a==b else 1) for b in range(3)] for a in range(3)]
    pd=ldl_psd([[Hq[a][b]-(Fr(9,10) if a==b else 0) for b in range(3)] for a in range(3)])
    high=[(sum(k),A(abs(v))) for k,v in Lq.items() if sum(k)>=3]
    yin=Fr(0)
    if pd:
        for ex in range(8,64):
            r=Fr(1,10**(ex//4))*Fr([10000000,5623413,3162277,1778279][ex%4],10**7)     # ~ 10^(-ex/4)
            if cM*r>Rout: continue                                                      # remainder bound eps needs |h| <= R_out
            Mr=arb(0); ra=A(r)
            for d_,av in high: Mr+=av*ra**(d_-3)
            if Mr*ra<=A(Fr(9,40)): yin=r; break
    gn=(A(gy[0])**2+A(gy[1])**2+A(gy[2])**2).sqrt()
    pos=pd and yin>0 and c0-eps-sum(v*v for v in gy)/Fr(9,20)>=0
    assert pos, ('inner node lemma failed',ni)
    ytin=arb_up(gn/arb('0.225')+((A(theta)+A(eps))/arb('0.225')).sqrt())
    # lambda >= 0 on |y| <= y_in (node lemma); lambda >= theta for y_tin <= |y| <= y_in (lemma) and for |y| > y_tube,
    # |y| >= y_in (bnb_local).  If y_tin > y_in the lemma gives no threshold statement and the tube is
    # {|y| <= max(y_tube, y_in)}; in general the tube radius is max(y_tube, min(y_tin, y_in)).
    okn=pos
    ytin=min(ytin,yin)
    # ---- cuts in y (conservative rounding)
    cuts=[]
    for (a,b0) in CUTS[p]:
        const=Fr(b0)+sum(Fr(a[i])*s[i] for i in range(3)); coef=[sum(Fr(a[i])*M[i][j] for i in range(3)) for j in range(3)]
        cd=[float(c) for c in coef]; slack=sum(abs(coef[j]-Fr(cd[j]))*Fr(sc[j])*Fr(1001,1000) for j in range(3))
        cuts.append((cd,fr_up(const+slack)))
    ytheta=math.sqrt(4*float(theta))
    tag=f'n{ni:02d}'
    nb=4; lo=[-sc[i] for i in range(3)]; wd=[Fr(2*sc[i]/nb) for i in range(3)]
    roots=[]
    for i in range(nb):
        for j in range(nb):
            for k in range(nb):
                L_=[Fr(lo[0])+i*wd[0],Fr(lo[1])+j*wd[1],Fr(lo[2])+k*wd[2]]; H_=[L_[a]+wd[a] for a in range(3)]
                cf=[float((L_[a]+H_[a])/2) for a in range(3)]; rad=[fr_up(max(Fr(cf[a])-L_[a],H_[a]-Fr(cf[a]))) for a in range(3)]
                Lc=taylor(Ly,[Fr(x) for x in cf]); Gc=taylor(Gy,[Fr(x) for x in cf]); roots.append((cf,rad,Lc,Gc))
    # the root boxes cover the bounding box of E
    assert all(Fr(lo[a])<=-Fr(sc[a]) and Fr(lo[a])+nb*wd[a]>=Fr(sc[a]) for a in range(3))
    with open(f'{outdir}/{tag}_ts.txt','w') as f:
        f.write(f'{D}\n{fr_up(eps)!r} {float(theta)!r} {ytheta!r} {fr_down(yin)!r} 1\n{sc[0]!r} {sc[1]!r} {sc[2]!r}\n{len(cuts)}\n')
        for coef,const in cuts: f.write(' '.join(repr(c) for c in coef)+f' {const!r}\n')
        f.write('1e-12\n')
    with open(f'{outdir}/{tag}_roots.txt','w') as f:
        f.write(f'{len(roots)}\n')
        for cf,rad,Lc,Gc in roots:
            f.write(' '.join(repr(x) for x in cf)+' '+' '.join(repr(x) for x in rad)+'\n')
            for a in range(D+1):
                for b in range(D+1-a):
                    for c in range(D+1-a-b):
                        v=Lc.get((a,b,c),Fr(0)); f.write(f'{fr_down(v)!r} {fr_up(v)!r}\n')
            for a in range(D+1):
                for b in range(D+1-a):
                    for c in range(D+1-a-b):
                        v=Gc.get((a,b,c),Fr(0)); f.write(f'{fr_down(v)!r} {fr_up(v)!r}\n')
    summary[ni]={'p':p,'sv':tuple(sv),'center':[float(x) for x in s],'yin':float(yin),'ytin':float(ytin),
                 'cM':float(cM),'eps':float(eps),'chk':(chk1,chk2,chk3),'node_lemma':okn,'kind':('edge' if edge else 'bnd') if bnd else 'int','mG':float(mGq),'nu':float(nuq),
                 'yin_q':yin,'ytin_q':ytin,'cM_q':cM,'eps_q':eps,'s_q':s,'M_q':M,'sc_q':[Fr(v) for v in sc],
                 'ok':bool(okn and chk1 and chk2 and chk3)}
    print(f'node {ni:2d} {p} {[round(v,4) for v in sv]} {"bnd" if bnd else "int"}: eps {float(eps):.1e}, '
          f'node lemma y_in={float(yin):.1e} y_tin={float(ytin):.2e} ({"OK" if okn else "FAIL"}), checks {chk1} {chk2} {chk3}, '
          f'c_M={float(cM):.1f}, ellipsoid {sc[0]:.1e},{sc[1]:.1e},{sc[2]:.1e}',flush=True)
pickle.dump(summary,open(f'{outdir}/summary_{sys.argv[6] if len(sys.argv)>6 else "all"}.pkl','wb'))

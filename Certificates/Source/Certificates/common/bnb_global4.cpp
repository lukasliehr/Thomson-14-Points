// Rigorous global branch and bound with outward binary64 interval arithmetic.
// Depth-first OpenMP task traversal; unresolved cells and early aborts fail.
// Exact polynomial root data are generated from certificate.json; see FORMAT.md.
// Lower bound for a three-point slack in the inner-product variables x=(u,v,t):
//     lambda(x) = sum_q w_q phi(x_{v_q}) + P(x),      phi(s) = (2-2s)^(-1/2),  w_q > 0,
// on  K = {Gram(x) >= 0} ∩ (union of root boxes) ∩ (linear cuts)  minus the union of excluded balls.
// RESULT VERIFIED implies lambda >= thr at every point of K (thr = 0 if not given).
//
// Soundness:
//  * every bound is computed in outward-rounded interval arithmetic (nextafter after each operation);
//    compile without -ffast-math and with -ffp-contract=off.
//  * P is given per root box by interval Taylor coefficients at the root center (a double, exact);
//    a child is obtained by an enclosing interval Taylor shift by the double delta = +-h (h = half the parent width).
//  * the TRUE center of a child is c_parent + delta (a real number).  The stored double center may differ by rounding;
//    the difference is computed exactly (TwoSum) and accumulated (rounded up) in the error radius e[].  Every geometric
//    test uses the inflated half-width r+e, and every quantity evaluated at the center (Gram coefficients, phi
//    coefficients, cut values) is evaluated on the interval [c-e, c+e], so that it encloses the value at the true center.
//  * P(c+z) is bounded on |z_i| <= r_i by  p_0 + sum_{m>0} |p_m| r^m [-1,1]   (upward-rounded monomial bounds).
//  * Gram and straddling cuts enter through the S-procedure lambda - sum mu_k g_k (mu_k >= 0, g_k >= 0 on K).
// File formats (also documented in Certificates/FORMAT.md):
//  problem (optional tail: thr / nballs + excluded balls "cx cy cz r" / ninc + include balls "cx cy cz r"):
//  problem: D / nphi / nphi lines "var wlo whi" / ncut / ncut lines "kind i j val" (0: x_i>=val, 1: x_i<=val,
//           2: x_i>=x_j) / minw / [thr] / [nballs / nballs lines "cx cy cz radius"]
//  roots:   nroots / per root "c0 c1 c2 r0 r1 r2" then NM lines "lo hi" (monomials a,b,c lexicographic, a+b+c<=D)
#include <cstdio>
#include <cfenv>
#include <limits>
#include <cstdlib>
#include <cmath>
#include <vector>
#include <algorithm>
#include <omp.h>
#include <array>
struct I { double lo, hi; };
static inline double DN(double x){ return std::nextafter(x,-INFINITY); }
static inline double UP(double x){ return std::nextafter(x, INFINITY); }
static inline I iv(double a){ return {a,a}; }
static inline I iv(double a,double b){ return {a,b}; }
static inline I operator+(I a,I b){ return {DN(a.lo+b.lo),UP(a.hi+b.hi)}; }
static inline I operator-(I a,I b){ return {DN(a.lo-b.hi),UP(a.hi-b.lo)}; }
static inline I operator*(I a,I b){ double p1=a.lo*b.lo,p2=a.lo*b.hi,p3=a.hi*b.lo,p4=a.hi*b.hi;
  return {DN(std::min(std::min(p1,p2),std::min(p3,p4))),UP(std::max(std::max(p1,p2),std::max(p3,p4)))}; }
static inline double mag(I a){ return std::max(std::fabs(a.lo),std::fabs(a.hi)); }
static int D, NM;
static std::vector<int> EA,EB,EC,IDX; static std::vector<double> BIN;
static inline int id(int a,int b,int c){ return IDX[(a*(D+1)+b)*(D+1)+c]; }
static inline double binom(int n,int k){ return BIN[n*(D+1)+k]; }
struct Box { double c[3], r[3], e[3]; std::vector<I> p; };
static void shift(std::vector<I>&p,int ax,double delta){
  if(delta==0) return;
  std::vector<I> q(NM, iv(0)); I dl=iv(delta);
  std::vector<I> dp(D+1); dp[0]=iv(1); for(int k=1;k<=D;k++) dp[k]=dp[k-1]*dl;
  for(int m=0;m<NM;m++){ if(p[m].lo==0&&p[m].hi==0) continue;
    int e[3]={EA[m],EB[m],EC[m]}; int n=e[ax];
    for(int j=0;j<=n;j++){ int f[3]={e[0],e[1],e[2]}; f[ax]=j;
      I term=p[m]*iv(binom(n,j))*dp[n-j]; int t=id(f[0],f[1],f[2]); q[t]=q[t]+term; } }
  p.swap(q);
}
static inline I phi_pt(double x){ // enclosure of (2-2x)^(-1/2) for x<1
  double b=2.0-2.0*x; double lo=DN(1.0/UP(std::sqrt(UP(b)))), hi=UP(1.0/DN(std::sqrt(DN(b))));
  return {lo,hi}; }
struct Prob { int nphi; int pv[3]; I pw[3]; int ncut; int cv[8][3]; double cval[8]; double minw; double thr; std::vector<std::array<double,4>> balls, incl; };
static Prob PR;
static bool inside_ball(const double c[3], const double R[3]){
  for(const auto&B:PR.balls){ double d2=0; for(int i=0;i<3;i++){ double d=UP(UP(std::fabs(c[i]-B[i]))+R[i]); d2=UP(d2+UP(d*d)); }
    if(d2<=DN(B[3]*B[3])) return true; }
  return false; }
// include region (optional): the domain is intersected with the union of the balls PR.incl; a cell is discarded if it
// provably misses every include ball (rigorous lower bound of the distance from the cell to the ball centre).
static bool outside_all_incl(const double c[3], const double R[3]){
  if(PR.incl.empty()) return false;
  for(const auto&B:PR.incl){ double d2=0; for(int i=0;i<3;i++){ double g=DN(DN(std::fabs(c[i]-B[i]))-R[i]); if(g<0) g=0; d2=DN(d2+DN(g*g)); }
    if(!(d2>UP(B[3]*B[3]))) return false; }
  return true; }
static double range_bound(const std::vector<I>&q,const double r[3],bool lower){ I s=q[0]; I acc=iv(0);
  for(int m=1;m<NM;m++){ if(q[m].lo==0&&q[m].hi==0) continue; double mon=1.0;
    for(int k=0;k<EA[m];k++) mon=UP(mon*r[0]); for(int k=0;k<EB[m];k++) mon=UP(mon*r[1]); for(int k=0;k<EC[m];k++) mon=UP(mon*r[2]);
    double w=UP(mag(q[m])*mon); acc=acc+iv(-w,w); }
  I t=s+acc; return lower?t.lo:t.hi; }
// S-procedure multipliers: maximize the range lower bound of q - sum_k mu_k g_k over mu >= 0 by coordinate ascent over
// the breakpoints of this concave piecewise-linear function (midpoint arithmetic: only the CHOICE of mu, which may be any
// mu >= 0, is heuristic; the bound itself is computed afterwards in interval arithmetic).  Starts from the NNLS multipliers.
static void sproc_apply(std::vector<I>&q, const std::vector<std::vector<I>>&gs, std::vector<double> mu, const double r[3]){
  int K=gs.size(); if(K==0) return;
  std::vector<int> S; std::vector<char> inS(NM,0); inS[0]=1; S.push_back(0);
  for(int k=0;k<K;k++) for(int m=0;m<NM;m++) if(!(gs[k][m].lo==0&&gs[k][m].hi==0) && !inS[m]){ inS[m]=1; S.push_back(m); }
  std::vector<double> mon(S.size(),1.0), qc(S.size()); std::vector<std::vector<double>> gc(K,std::vector<double>(S.size()));
  for(size_t i=0;i<S.size();i++){ int m=S[i]; double mo=1.0; for(int k=0;k<EA[m];k++) mo*=r[0]; for(int k=0;k<EB[m];k++) mo*=r[1]; for(int k=0;k<EC[m];k++) mo*=r[2]; mon[i]=mo;
    qc[i]=0.5*(q[m].lo+q[m].hi); for(int k=0;k<K;k++) gc[k][i]=0.5*(gs[k][m].lo+gs[k][m].hi); }
  auto val=[&](const std::vector<double>&mu)->double{ double s=0; for(size_t i=0;i<S.size();i++){ double c=qc[i]; for(int k=0;k<K;k++) c-=mu[k]*gc[k][i]; s+= (i==0)? c : -std::fabs(c)*mon[i]; } return s; };
  for(int k=0;k<K;k++) if(!(mu[k]>=0) || !std::isfinite(mu[k])) mu[k]=0;
  double best=val(mu);
  for(int round=0;round<4;round++){ bool imp=false;
    for(int k=0;k<K;k++){ double bm=mu[k], bk=best;
      std::vector<double> cand={0.0};
      for(size_t i=1;i<S.size();i++){ if(gc[k][i]==0) continue; double c=qc[i]; for(int j=0;j<K;j++) if(j!=k) c-=mu[j]*gc[j][i];
        double br=c/gc[k][i]; if(br>0 && std::isfinite(br)) cand.push_back(br); }
      for(double cv:cand){ double keep=mu[k]; mu[k]=cv; double l=val(mu); if(l>bk){bk=l;bm=cv;} mu[k]=keep; }
      if(bk>best){ best=bk; mu[k]=bm; imp=true; } }
    if(!imp) break; }
  for(int k=0;k<K;k++) if(mu[k]>0){ I M=iv(mu[k]); for(int mm=0;mm<NM;mm++) if(!(gs[k][mm].lo==0&&gs[k][mm].hi==0)) q[mm]=q[mm]-M*gs[k][mm]; }
}
static double lowerbound(const Box&b, bool&outside){
  outside=false;
  double R[3]; I C[3], X[3];
  for(int i=0;i<3;i++){ R[i]=UP(b.r[i]+b.e[i]); C[i]=iv(DN(b.c[i]-b.e[i]),UP(b.c[i]+b.e[i])); X[i]=iv(DN(b.c[i]-R[i]),UP(b.c[i]+R[i])); }
  for(int k=0;k<PR.ncut;k++){ int kind=PR.cv[k][0],i=PR.cv[k][1],j=PR.cv[k][2];
    if(kind==0 && X[i].hi<PR.cval[k]) {outside=true; return INFINITY;}
    if(kind==1 && X[i].lo>PR.cval[k]) {outside=true; return INFINITY;}
    if(kind==2 && X[i].hi<X[j].lo) {outside=true; return INFINITY;} }
  // Gram polynomial G = 1+2uvt-u^2-v^2-t^2, Taylor coefficients at the true center (enclosed by C)
  std::vector<I> g(NM, iv(0));
  { I U=C[0],V=C[1],T=C[2];
    g[id(0,0,0)]=iv(1)+iv(2)*U*V*T-U*U-V*V-T*T;
    g[id(1,0,0)]=iv(2)*V*T-iv(2)*U; g[id(0,1,0)]=iv(2)*U*T-iv(2)*V; g[id(0,0,1)]=iv(2)*U*V-iv(2)*T;
    if(D>=2){ g[id(2,0,0)]=iv(-1); g[id(0,2,0)]=iv(-1); g[id(0,0,2)]=iv(-1);
      g[id(1,1,0)]=iv(2)*T; g[id(1,0,1)]=iv(2)*V; g[id(0,1,1)]=iv(2)*U; }
    if(D>=3) g[id(1,1,1)]=iv(2); else { fprintf(stderr,"D<3 not supported\n"); exit(2); } }
  if(range_bound(g,b.r,false)<0){ outside=true; return INFINITY; }
  bool inside = range_bound(g,b.r,true)>=0;
  std::vector<I> q=b.p;
  for(int s=0;s<PR.nphi;s++){ int vv=PR.pv[s]; I w=PR.pw[s]; I xc=C[vv]; double rr=b.r[vv];
    double omlo=DN(1.0-xc.hi), omhi=UP(1.0-xc.lo);
    if(!(omlo>0) || rr>=0.5*omlo){ // near the singularity: phi increasing, w>0  =>  w phi(x) >= w.lo phi(x_lo)
      double xl=std::max(DN(xc.lo-rr),-1.0);
      if(xl>=1.0) return INFINITY;            // no admissible point (x<1 for distinct points): nothing to prove
      I ph=phi_pt(xl); q[0]=q[0]+iv(w.lo)*iv(ph.lo); continue; }
    // phi(c+z) = phi(c) sum_k beta_k (z/(1-c))^k, beta_k = binom(2k,k)/4^k <= 1; tail for |z|<=rr: phi(c) qq^(D+1)/(1-qq)
    I ph={phi_pt(xc.lo).lo, phi_pt(xc.hi).hi}; I inv=iv(DN(1.0/omhi),UP(1.0/omlo)); I powk=iv(1); I beta=iv(1);
    int e[3]={0,0,0};
    for(int k=0;k<=D;k++){
      if(k>0){ beta=beta*iv(2.0*k-1)*iv(DN(1.0/(2.0*k)),UP(1.0/(2.0*k))); powk=powk*inv; }
      I bk=beta; // exact beta_k enclosed by the interval recurrence above
      e[vv]=k; int m=id(e[0],e[1],e[2]); q[m]=q[m]+w*ph*bk*powk; }
    double qq=UP(rr/omlo); double pq=1.0; for(int k=0;k<=D;k++) pq=UP(pq*qq);
    double tail=UP(UP(UP(ph.hi*pq)*w.hi)/DN(1.0-qq));
    q[0]=q[0]+iv(-tail,0.0);
  }
  { std::vector<std::vector<I>> gs; std::vector<std::vector<double>> grads;
    auto grad_of=[&](const std::vector<I>&p){ std::vector<double> gr(3); gr[0]=0.5*(p[id(1,0,0)].lo+p[id(1,0,0)].hi); gr[1]=0.5*(p[id(0,1,0)].lo+p[id(0,1,0)].hi); gr[2]=0.5*(p[id(0,0,1)].lo+p[id(0,0,1)].hi); return gr; };
    if(!inside){ gs.push_back(g); grads.push_back(grad_of(g)); }
    for(int k=0;k<PR.ncut;k++){ int kind=PR.cv[k][0],i=PR.cv[k][1],j=PR.cv[k][2]; std::vector<I> lc(NM,iv(0)); bool strad=false;
      if(kind==0){ lc[0]=C[i]-iv(PR.cval[k]); int e[3]={0,0,0}; e[i]=1; lc[id(e[0],e[1],e[2])]=iv(1); strad=(X[i].lo<PR.cval[k]); }
      if(kind==1){ lc[0]=iv(PR.cval[k])-C[i]; int e[3]={0,0,0}; e[i]=1; lc[id(e[0],e[1],e[2])]=iv(-1); strad=(X[i].hi>PR.cval[k]); }
      if(kind==2){ lc[0]=C[i]-C[j]; int e[3]={0,0,0}; e[i]=1; int f2[3]={0,0,0}; f2[j]=1; lc[id(e[0],e[1],e[2])]=iv(1); lc[id(f2[0],f2[1],f2[2])]=iv(-1); strad=(X[i].lo<X[j].hi); }
      if(strad){ gs.push_back(lc); grads.push_back(grad_of(lc)); } }
    int K=gs.size();
    if(K>0){
      std::vector<double> gl=grad_of(q); double best=1e300; std::vector<double> bmu(K,0.0);
      for(int mask=1;mask<(1<<K);mask++){ std::vector<int> S; for(int k=0;k<K;k++) if(mask>>k&1) S.push_back(k); int m=S.size(); if(m>3) continue;
        double Mm[3][4];
        for(int a=0;a<m;a++){ for(int c=0;c<m;c++){ double sdot=0; for(int d=0;d<3;d++) sdot+=grads[S[a]][d]*grads[S[c]][d]; Mm[a][c]=sdot; } double sd=0; for(int d=0;d<3;d++) sd+=grads[S[a]][d]*gl[d]; Mm[a][m]=sd; }
        double sol[3]={0,0,0}; bool okk=true;
        for(int a=0;a<m;a++){ int piv=a; for(int c=a+1;c<m;c++) if(std::fabs(Mm[c][a])>std::fabs(Mm[piv][a])) piv=c; if(std::fabs(Mm[piv][a])<1e-300){okk=false;break;}
          for(int c=0;c<=m;c++) std::swap(Mm[a][c],Mm[piv][c]);
          for(int c=a+1;c<m;c++){ double fct=Mm[c][a]/Mm[a][a]; for(int d=a;d<=m;d++) Mm[c][d]-=fct*Mm[a][d]; } }
        if(!okk) continue;
        for(int a=m-1;a>=0;a--){ double sv=Mm[a][m]; for(int c=a+1;c<m;c++) sv-=Mm[a][c]*sol[c]; sol[a]=sv/Mm[a][a]; }
        bool nonneg=true; for(int a=0;a<m;a++) if(!(sol[a]>=0)) nonneg=false; if(!nonneg) continue;
        double res=0; for(int d=0;d<3;d++){ double z=gl[d]; for(int a=0;a<m;a++) z-=sol[a]*grads[S[a]][d]; res+=z*z; }
        if(res<best){ best=res; std::fill(bmu.begin(),bmu.end(),0.0); for(int a=0;a<m;a++) bmu[S[a]]=sol[a]; } }
      sproc_apply(q,gs,bmu,b.r);
    }
  }
  return range_bound(q,b.r,true);
}
static double centervalue(const Box&b){ Box z; z.p=b.p; for(int i=0;i<3;i++){z.c[i]=b.c[i]; z.r[i]=0.0; z.e[i]=b.e[i];} bool o; double v=lowerbound(z,o); return o?INFINITY:v; }

#include <atomic>
#include <string>
struct Stat { long long total=0,acc=0,outs=0,inball=0,ncex=0,fail=0,deep=0; double worst=INFINITY, emax=0; int maxdepth=0;
  std::vector<std::array<double,4>> cex; std::vector<std::array<double,5>> fails; char pad[64]; };
static std::vector<Stat> ST;
static std::atomic<long long> NDONE(0), NCEX(0), NFAIL(0);
static std::atomic<bool> ABORT(false);
static long long MAXCEX=-1, MAXBOXES=-1, MAXFAIL=-1;   // optional early stop (env BNB_MAXCEX, BNB_MAXBOXES, BNB_MAXFAIL); an aborted run is NOT_VERIFIED
static double CEXSLACK=1e-10;                 // a box is reported as counterexample candidate if its centre value is < thr - CEXSLACK (env BNB_CEXSLACK; reporting only)
static const int MAXLEV=80;
static void process(Box&b,int depth){
  if(ABORT.load(std::memory_order_relaxed)) return;
  Stat&S=ST[omp_get_thread_num()];
  S.total++; if(depth>S.maxdepth) S.maxdepth=depth;
  { long long nd=++NDONE; if((nd&((1LL<<20)-1))==0){
      #pragma omp critical(progress)
      fprintf(stderr,"progress: %lld boxes (counterexamples %lld, failed %lld)\n",nd,NCEX.load(),NFAIL.load()); }
    if(MAXBOXES>=0 && nd>MAXBOXES) ABORT=true; }
  double R[3]; for(int i=0;i<3;i++) R[i]=UP(b.r[i]+b.e[i]);
  if(outside_all_incl(b.c,R)){ S.outs++; return; }
  if(inside_ball(b.c,R)){ S.inball++; return; }
  bool out; double l=lowerbound(b,out);
  if(out){ S.outs++; return; }
  if(l>=PR.thr){ S.acc++; if(l<S.worst) S.worst=l; return; }
  { double cv=centervalue(b);
    if(cv< PR.thr-CEXSLACK && b.r[0]<2e-3 && b.r[1]<2e-3 && b.r[2]<2e-3){ S.ncex++; if(S.cex.size()<20000) S.cex.push_back({b.c[0],b.c[1],b.c[2],cv}); long long nc=++NCEX; if(MAXCEX>=0 && nc>MAXCEX) ABORT=true; return; } }
  int d=0; for(int q=1;q<3;q++) if(b.r[q]>b.r[d]) d=q;
  if(b.r[d]<PR.minw || depth>=MAXLEV-1){ S.fail++; { long long nf_=++NFAIL; if(MAXFAIL>=0 && nf_>MAXFAIL) ABORT=true; } if(depth>=MAXLEV-1) S.deep++; if(S.fails.size()<20000) S.fails.push_back({b.c[0],b.c[1],b.c[2],b.r[d],l}); return; }
  for(int s=-1;s<=1;s+=2){
    Box*ch=new Box; ch->p=b.p; for(int i=0;i<3;i++){ch->c[i]=b.c[i]; ch->r[i]=b.r[i]; ch->e[i]=b.e[i];}
    double h=0.5*b.r[d]; double dl=s*h;
    double cn=b.c[d]+dl; double bp=cn-b.c[d]; double err=(b.c[d]-(cn-bp))+(dl-bp);   // TwoSum: c+dl = cn+err exactly
    ch->c[d]=cn; ch->e[d]=UP(b.e[d]+std::fabs(err)); if(ch->e[d]>S.emax) S.emax=ch->e[d];
    ch->r[d]=UP(h); shift(ch->p,d,dl);
    #pragma omp task firstprivate(ch,depth)
    { process(*ch,depth+1); delete ch; }
  }
}
int main(int argc,char**argv){
  static_assert(std::numeric_limits<double>::is_iec559 && sizeof(double)==8, "IEEE binary64 required");
  if(std::fegetround()!=FE_TONEAREST){ fprintf(stderr,"round-to-nearest required\n"); return 2; }
  if(argc<3){ fprintf(stderr,"usage: bnb_global4 problem roots\n"); return 2; }
  FILE*f=fopen(argv[1],"r"); int nroots; if(!f) return 2;
  if(fscanf(f,"%d",&D)!=1 || D<3 || D>40) return 2; // binomial coefficients then fit exactly in binary64
  if(fscanf(f,"%d",&PR.nphi)!=1) return 2;
  for(int q=0;q<PR.nphi;q++){ double lo,hi; if(fscanf(f,"%d %lf %lf",&PR.pv[q],&lo,&hi)!=3) return 2; PR.pw[q]=iv(lo,hi);
    if(!(lo>0)){ fprintf(stderr,"phi weight must be positive\n"); return 2; } }
  if(fscanf(f,"%d",&PR.ncut)!=1) return 2;
  for(int q=0;q<PR.ncut;q++) if(fscanf(f,"%d %d %d %lf",&PR.cv[q][0],&PR.cv[q][1],&PR.cv[q][2],&PR.cval[q])!=4) return 2;
  if(fscanf(f,"%lf",&PR.minw)!=1) return 2;
  PR.thr=0.0; { double th; if(fscanf(f,"%lf",&th)==1) PR.thr=th; int nb=0; if(fscanf(f,"%d",&nb)==1){ for(int q=0;q<nb;q++){ std::array<double,4> B; if(fscanf(f,"%lf %lf %lf %lf",&B[0],&B[1],&B[2],&B[3])!=4) return 2; PR.balls.push_back(B);} int ni=0; if(fscanf(f,"%d",&ni)==1){ for(int q=0;q<ni;q++){ std::array<double,4> B; if(fscanf(f,"%lf %lf %lf %lf",&B[0],&B[1],&B[2],&B[3])!=4) return 2; PR.incl.push_back(B);} } } }
  fclose(f);
  fprintf(stderr,"bnb_global4: threshold %.6e, %zu excluded balls, %zu include balls\n",PR.thr,PR.balls.size(),PR.incl.size());
  IDX.assign((D+1)*(D+1)*(D+1),-1);
  for(int a=0;a<=D;a++) for(int bb=0;bb<=D-a;bb++) for(int c=0;c<=D-a-bb;c++){ IDX[(a*(D+1)+bb)*(D+1)+c]=EA.size(); EA.push_back(a);EB.push_back(bb);EC.push_back(c);}
  NM=EA.size(); BIN.assign((D+1)*(D+1),0); for(int n=0;n<=D;n++){ BIN[n*(D+1)]=1; for(int k=1;k<=n;k++) BIN[n*(D+1)+k]=BIN[(n-1)*(D+1)+k-1]+(k<=n-1?BIN[(n-1)*(D+1)+k]:0); }
  FILE*g=fopen(argv[2],"r"); if(!g||fscanf(g,"%d",&nroots)!=1) return 2;
  ST.resize(omp_get_max_threads());
  if(getenv("BNB_MAXCEX")) MAXCEX=atoll(getenv("BNB_MAXCEX"));
  if(getenv("BNB_MAXBOXES")) MAXBOXES=atoll(getenv("BNB_MAXBOXES"));
  if(getenv("BNB_MAXFAIL")) MAXFAIL=atoll(getenv("BNB_MAXFAIL"));
  if(getenv("BNB_CEXSLACK")) CEXSLACK=atof(getenv("BNB_CEXSLACK"));
  if(getenv("BNB_MINW")){ double mw=atof(getenv("BNB_MINW")); if(mw>PR.minw) PR.minw=mw; }   // coarser stop (sweeps for feedback); can only turn VERIFIED into NOT_VERIFIED
  // roots are read one at a time (the root file can be large) and processed as tasks
  long long nread=0; bool bad=false;
  #pragma omp parallel
  #pragma omp single
  {
    for(int n=0;n<nroots && !bad;n++){ Box*b=new Box;
      for(int i=0;i<3;i++) if(fscanf(g,"%lf",&b->c[i])!=1) bad=true;
      for(int i=0;i<3;i++) if(fscanf(g,"%lf",&b->r[i])!=1) bad=true;
      for(int i=0;i<3;i++){ b->e[i]=0.0; if(!(b->r[i]>=0)) bad=true; }
      b->p.resize(NM); for(int m=0;m<NM && !bad;m++){ double lo,hi; if(fscanf(g,"%lf %lf",&lo,&hi)!=2) bad=true; else if(!(lo<=hi)) bad=true; else b->p[m]=iv(lo,hi);}
      if(bad){ delete b; break; }
      nread++;
      #pragma omp task firstprivate(b)
      { process(*b,0); delete b; }
    }
    #pragma omp taskwait
  }
  fclose(g);
  if(bad || nread!=nroots){ fprintf(stderr,"root file error (read %lld of %d roots)\n",nread,nroots); printf("RESULT NOT_VERIFIED (root file error)\n"); return 2; }
  Stat T; std::vector<std::array<double,4>> cex; int nf=0;
  for(const Stat&S:ST){ T.total+=S.total; T.acc+=S.acc; T.outs+=S.outs; T.inball+=S.inball; T.ncex+=S.ncex; T.fail+=S.fail; T.deep+=S.deep;
    if(S.worst<T.worst) T.worst=S.worst; if(S.emax>T.emax) T.emax=S.emax; if(S.maxdepth>T.maxdepth) T.maxdepth=S.maxdepth;
    cex.insert(cex.end(),S.cex.begin(),S.cex.end());
    for(const auto&F:S.fails){ if(nf++<10) fprintf(stderr,"FAIL c=(%.12f %.12f %.12f) r=%.2e lb=%.3e\n",F[0],F[1],F[2],F[3],F[4]);
      if(nf<=20000) printf("FAILBOX %.15f %.15f %.15f %.3e %.6e\n",F[0],F[1],F[2],F[3],F[4]); } }
  std::sort(cex.begin(),cex.end());
  for(size_t i=0;i<cex.size() && i<20000;i++) printf("CEX %.15f %.15f %.15f %.6e\n",cex[i][0],cex[i][1],cex[i][2],cex[i][3]);
  fprintf(stderr,"done: %lld boxes, max depth %d, %lld failed (%lld at the depth limit)\n",T.total,T.maxdepth,T.fail,T.deep);
  bool aborted=ABORT.load();
  if(aborted) fprintf(stderr,"ABORTED early (limit on counterexamples or boxes reached): the run proves nothing\n");
  bool ok=(T.fail==0 && T.ncex==0 && !aborted);
  printf("RESULT %s boxes=%lld accepted=%lld outside=%lld in_node_balls=%lld failed=%lld counterexamples=%lld min_lb=%.4e threshold=%.4e max_center_err=%.2e\n",ok?"VERIFIED":(aborted?"NOT_VERIFIED(aborted)":"NOT_VERIFIED"),T.total,T.acc,T.outs,T.inball,T.fail,T.ncex,T.worst,PR.thr,T.emax);
  return ok?0:1;
}

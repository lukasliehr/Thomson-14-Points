// Rigorous local branch and bound in node coordinates y, with x = node + M*y.
// Outward interval bounds, exact-centre tracking and depth-first OpenMP tasks.
// An inner-node estimate and coverage checks are provided by prep_local3.py.
// See Certificates/FORMAT.md for the file formats and the mathematical role.
//   RESULT VERIFIED proves:
//     (a) Lambda(y) - eps >= 0    for every y in D_loc with |y| >= y_in,
//     (b) Lambda(y) - eps >= thr  for every y in D_loc with |y| > y_tube and |y| > y_in.
//   env BNB_MAXFAIL / BNB_MAXBOXES: optional early stop (an aborted run is NOT_VERIFIED).
//   problem: D / eps thr ytheta yin hasG / s0 s1 s2 / ncut / ncut lines "a0 a1 a2 b" / minw
//   roots:   nroots / per root "c0 c1 c2 r0 r1 r2", NM lines Lambda "lo hi", NM lines Gram "lo hi" (if hasG)
#include <cstdio>
#include <cfenv>
#include <limits>
#include <cstdlib>
#include <cmath>
#include <vector>
#include <algorithm>
#include <omp.h>
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
struct Box { double c[3], r[3], e[3]; std::vector<I> p, g; };
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
struct Prob { double eps, thr, ytheta, yin, s[3]; int ncut; double ca[16][3], cb[16]; double minw; bool hasG; };
static Prob PR;
static double range_bound(const std::vector<I>&q,const double r[3],bool lower){ I s=q[0]; I acc=iv(0);
  for(int m=1;m<NM;m++){ if(q[m].lo==0&&q[m].hi==0) continue; double mon=1.0;
    for(int k=0;k<EA[m];k++) mon=UP(mon*r[0]); for(int k=0;k<EB[m];k++) mon=UP(mon*r[1]); for(int k=0;k<EC[m];k++) mon=UP(mon*r[2]);
    double w=UP(mag(q[m])*mon); acc=acc+iv(-w,w); }
  I t=s+acc; return lower?t.lo:t.hi; }
// status: 0 subdivide, 1 accepted with thr, 6 accepted with threshold 0, 2 outside domain, 4 inner ball, 5 outside local region
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
static int classify(const Box&b,double&lb,double&ymax){
  lb=INFINITY;
  double R[3]; I C[3];
  for(int i=0;i<3;i++){ R[i]=UP(b.r[i]+b.e[i]); C[i]=iv(DN(b.c[i]-b.e[i]),UP(b.c[i]+b.e[i])); }
  double mn=0, mx=0, ymin2=0;
  for(int i=0;i<3;i++){ double lo=DN(b.c[i]-R[i]), hi=UP(b.c[i]+R[i]); double a=(lo<=0&&hi>=0)?0.0:std::min(std::fabs(lo),std::fabs(hi));
    double am=std::max(std::fabs(lo),std::fabs(hi)); double as=DN(a/PR.s[i]); mn=DN(mn+DN(as*as)); mx=UP(mx+UP(am*am)); ymin2=DN(ymin2+DN(a*a)); }
  if(mn>1.0) return 5;
  ymax=UP(std::sqrt(mx));
  if(ymax<=PR.yin) return 4;
  double thr=(ymin2>=UP(PR.ytheta*PR.ytheta))?PR.thr:0.0;
  std::vector<std::vector<I>> gs; std::vector<std::vector<double>> grads;
  for(int k=0;k<PR.ncut;k++){ I v=iv(PR.cb[k]); I rng=iv(0);
    for(int i=0;i<3;i++){ v=v+iv(PR.ca[k][i])*C[i]; double w=UP(std::fabs(PR.ca[k][i])*b.r[i]); rng=rng+iv(-w,w); }
    I tot=v+rng; if(tot.hi<0) return 2;
    if(tot.lo<0){ std::vector<I> lc(NM,iv(0)); lc[0]=v; lc[id(1,0,0)]=iv(PR.ca[k][0]); lc[id(0,1,0)]=iv(PR.ca[k][1]); lc[id(0,0,1)]=iv(PR.ca[k][2]);
      gs.push_back(lc); grads.push_back({PR.ca[k][0],PR.ca[k][1],PR.ca[k][2]}); } }
  if(PR.hasG){ if(range_bound(b.g,b.r,false)<0) return 2;
    if(range_bound(b.g,b.r,true)<0){ gs.push_back(b.g); grads.push_back({0.5*(b.g[id(1,0,0)].lo+b.g[id(1,0,0)].hi),0.5*(b.g[id(0,1,0)].lo+b.g[id(0,1,0)].hi),0.5*(b.g[id(0,0,1)].lo+b.g[id(0,0,1)].hi)}); } }
  std::vector<I> q=b.p; q[0]=q[0]+iv(-PR.eps,0.0);
  int K=gs.size();
  if(K>0){ std::vector<double> gl={0.5*(q[id(1,0,0)].lo+q[id(1,0,0)].hi),0.5*(q[id(0,1,0)].lo+q[id(0,1,0)].hi),0.5*(q[id(0,0,1)].lo+q[id(0,0,1)].hi)};
    double best=1e300; std::vector<double> bmu(K,0.0);
    for(int mask=1;mask<(1<<K);mask++){ std::vector<int> S; for(int k=0;k<K;k++) if(mask>>k&1) S.push_back(k); int m=S.size(); if(m>3) continue;
      double Mm[3][4];
      for(int a=0;a<m;a++){ for(int c=0;c<m;c++){ double sd=0; for(int d=0;d<3;d++) sd+=grads[S[a]][d]*grads[S[c]][d]; Mm[a][c]=sd; } double sd=0; for(int d=0;d<3;d++) sd+=grads[S[a]][d]*gl[d]; Mm[a][m]=sd; }
      double sol[3]={0,0,0}; bool okk=true;
      for(int a=0;a<m;a++){ int piv=a; for(int c=a+1;c<m;c++) if(std::fabs(Mm[c][a])>std::fabs(Mm[piv][a])) piv=c; if(std::fabs(Mm[piv][a])<1e-300){okk=false;break;}
        for(int c=0;c<=m;c++) std::swap(Mm[a][c],Mm[piv][c]);
        for(int c=a+1;c<m;c++){ double f=Mm[c][a]/Mm[a][a]; for(int d=a;d<=m;d++) Mm[c][d]-=f*Mm[a][d]; } }
      if(!okk) continue;
      for(int a=m-1;a>=0;a--){ double sv=Mm[a][m]; for(int c=a+1;c<m;c++) sv-=Mm[a][c]*sol[c]; sol[a]=sv/Mm[a][a]; }
      bool nn=true; for(int a=0;a<m;a++) if(!(sol[a]>=0)) nn=false; if(!nn) continue;
      double res=0; for(int d=0;d<3;d++){ double z=gl[d]; for(int a=0;a<m;a++) z-=sol[a]*grads[S[a]][d]; res+=z*z; }
      if(res<best){ best=res; std::fill(bmu.begin(),bmu.end(),0.0); for(int a=0;a<m;a++) bmu[S[a]]=sol[a]; } }
    sproc_apply(q,gs,bmu,b.r); }
  lb=range_bound(q,b.r,true);
  if(lb>=PR.thr) return 1;                  // Lambda - eps >= thr on the whole box
  if(thr==0.0 && lb>=0) return 6;           // Lambda - eps >= 0 on a box meeting |y| < y_theta (enters y_tube)
  return 0;
}

#include <atomic>
#include <array>
struct Stat { long long total=0,acc=0,acc0=0,outs=0,inner=0,glob=0,fail=0; double worst=INFINITY, ytube=0, emax=0; int maxdepth=0;
  std::vector<std::array<double,5>> fails; char pad[64]; };
static std::vector<Stat> ST;
static std::atomic<long long> NDONE(0), NFAIL(0);
static std::atomic<bool> ABORT(false);
static long long MAXFAIL=-1, MAXBOXES=-1;
static const int MAXLEV=200;
static void process(Box&b,int depth){
  if(ABORT.load(std::memory_order_relaxed)) return;
  Stat&S=ST[omp_get_thread_num()];
  S.total++; if(depth>S.maxdepth) S.maxdepth=depth;
  { long long nd=++NDONE; if((nd&((1LL<<20)-1))==0){
      #pragma omp critical(progress)
      fprintf(stderr,"progress: %lld boxes (failed %lld)\n",nd,NFAIL.load()); }
    if(MAXBOXES>=0 && nd>MAXBOXES) ABORT=true; }
  double l,y=0; int st=classify(b,l,y);
  if(st==2){S.outs++; return;} if(st==4){S.inner++; return;} if(st==5){S.glob++; return;}
  if(st==1){S.acc++; if(l<S.worst) S.worst=l; return;}
  if(st==6){S.acc0++; if(y>S.ytube) S.ytube=y; return;}
  int d=0; for(int q=1;q<3;q++) if(b.r[q]>b.r[d]) d=q;
  if(b.r[d]<PR.minw || depth>=MAXLEV-1){ S.fail++; long long nf=++NFAIL; if(MAXFAIL>=0 && nf>MAXFAIL) ABORT=true;
    if(S.fails.size()<20000) S.fails.push_back({b.c[0],b.c[1],b.c[2],b.r[d],l}); return; }
  for(int s=-1;s<=1;s+=2){ Box*ch=new Box; ch->p=b.p; ch->g=b.g; for(int i=0;i<3;i++){ch->c[i]=b.c[i]; ch->r[i]=b.r[i]; ch->e[i]=b.e[i];}
    double h=0.5*b.r[d]; double dl=s*h;
    double cn=b.c[d]+dl; double bp=cn-b.c[d]; double err=(b.c[d]-(cn-bp))+(dl-bp);   // TwoSum
    ch->c[d]=cn; ch->e[d]=UP(b.e[d]+std::fabs(err)); if(ch->e[d]>S.emax) S.emax=ch->e[d];
    ch->r[d]=UP(h); shift(ch->p,d,dl); if(PR.hasG) shift(ch->g,d,dl);
    #pragma omp task firstprivate(ch,depth)
    { process(*ch,depth+1); delete ch; }
  }
}
int main(int argc,char**argv){
  static_assert(std::numeric_limits<double>::is_iec559 && sizeof(double)==8, "IEEE binary64 required");
  if(std::fegetround()!=FE_TONEAREST){ fprintf(stderr,"round-to-nearest required\n"); return 2; }
  if(argc<3){ fprintf(stderr,"usage: bnb_local3 problem roots\n"); return 2; }
  FILE*f=fopen(argv[1],"r"); if(!f) return 2;
  if(fscanf(f,"%d",&D)!=1 || D<3 || D>40) return 2; // binomial coefficients then fit exactly in binary64
  int hg; if(fscanf(f,"%lf %lf %lf %lf %d",&PR.eps,&PR.thr,&PR.ytheta,&PR.yin,&hg)!=5) return 2; PR.hasG=hg;
  if(fscanf(f,"%lf %lf %lf",&PR.s[0],&PR.s[1],&PR.s[2])!=3) return 2;
  if(fscanf(f,"%d",&PR.ncut)!=1 || PR.ncut>16) return 2;
  for(int k=0;k<PR.ncut;k++) if(fscanf(f,"%lf %lf %lf %lf",&PR.ca[k][0],&PR.ca[k][1],&PR.ca[k][2],&PR.cb[k])!=4) return 2;
  if(fscanf(f,"%lf",&PR.minw)!=1) return 2;
  fclose(f);
  IDX.assign((D+1)*(D+1)*(D+1),-1);
  for(int a=0;a<=D;a++) for(int bb=0;bb<=D-a;bb++) for(int c=0;c<=D-a-bb;c++){ IDX[(a*(D+1)+bb)*(D+1)+c]=EA.size(); EA.push_back(a);EB.push_back(bb);EC.push_back(c);}
  NM=EA.size(); BIN.assign((D+1)*(D+1),0); for(int n=0;n<=D;n++){ BIN[n*(D+1)]=1; for(int k=1;k<=n;k++) BIN[n*(D+1)+k]=BIN[(n-1)*(D+1)+k-1]+(k<=n-1?BIN[(n-1)*(D+1)+k]:0); }
  FILE*g=fopen(argv[2],"r"); int nroots; if(!g||fscanf(g,"%d",&nroots)!=1) return 2;
  ST.resize(omp_get_max_threads());
  if(getenv("BNB_MAXFAIL")) MAXFAIL=atoll(getenv("BNB_MAXFAIL"));
  if(getenv("BNB_MAXBOXES")) MAXBOXES=atoll(getenv("BNB_MAXBOXES"));
  long long nread=0; bool bad=false;
  #pragma omp parallel
  #pragma omp single
  {
    for(int n=0;n<nroots && !bad;n++){ Box*b=new Box;
      for(int i=0;i<3;i++) if(fscanf(g,"%lf",&b->c[i])!=1) bad=true;
      for(int i=0;i<3;i++) if(fscanf(g,"%lf",&b->r[i])!=1) bad=true;
      for(int i=0;i<3;i++){ b->e[i]=0.0; if(!(b->r[i]>=0)) bad=true; }
      b->p.resize(NM); for(int m=0;m<NM && !bad;m++){ double lo,hi; if(fscanf(g,"%lf %lf",&lo,&hi)!=2) bad=true; else if(!(lo<=hi)) bad=true; else b->p[m]=iv(lo,hi);}
      b->g.assign(NM,iv(0)); if(PR.hasG) for(int m=0;m<NM && !bad;m++){ double lo,hi; if(fscanf(g,"%lf %lf",&lo,&hi)!=2) bad=true; else if(!(lo<=hi)) bad=true; else b->g[m]=iv(lo,hi);}
      if(bad){ delete b; break; }
      nread++;
      #pragma omp task firstprivate(b)
      { process(*b,0); delete b; }
    }
    #pragma omp taskwait
  }
  fclose(g);
  if(bad || nread!=nroots){ fprintf(stderr,"root file error (read %lld of %d roots)\n",nread,nroots); printf("RESULT NOT_VERIFIED (root file error)\n"); return 2; }
  Stat T; T.ytube=PR.ytheta; int nf=0;
  for(const Stat&S:ST){ T.total+=S.total; T.acc+=S.acc; T.acc0+=S.acc0; T.outs+=S.outs; T.inner+=S.inner; T.glob+=S.glob; T.fail+=S.fail;
    if(S.worst<T.worst) T.worst=S.worst;
    if(S.ytube>T.ytube) T.ytube=S.ytube;
    if(S.emax>T.emax) T.emax=S.emax;
    if(S.maxdepth>T.maxdepth) T.maxdepth=S.maxdepth;
    for(const auto&F:S.fails){ if(nf++<10) fprintf(stderr,"FAIL c=(%.3e %.3e %.3e) r=%.2e lb=%.3e\n",F[0],F[1],F[2],F[3],F[4]);
      if(nf<=20000) printf("FAILBOX %.17g %.17g %.17g %.3e %.6e\n",F[0],F[1],F[2],F[3],F[4]); } }
  bool aborted=ABORT.load();
  if(aborted) fprintf(stderr,"ABORTED early (limit on failures or boxes reached): the run proves nothing\n");
  fprintf(stderr,"done: %lld boxes, max depth %d, %lld failed\n",T.total,T.maxdepth,T.fail);
  bool ok=(T.fail==0 && !aborted);
  printf("RESULT %s boxes=%lld accepted=%lld accepted_thr0=%lld outside_domain=%lld inner_ball=%lld left_to_global=%lld failed=%lld min_lb=%.4e thr=%.3e ytheta=%.3e yin=%.3e ytube=%.17g max_center_err=%.2e\n",ok?"VERIFIED":(aborted?"NOT_VERIFIED(aborted)":"NOT_VERIFIED"),T.total,T.acc,T.acc0,T.outs,T.inner,T.glob,T.fail,T.worst,PR.thr,PR.ytheta,PR.yin,T.ytube,T.emax);
  return ok?0:1;
}

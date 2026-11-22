module

public import N14.Energy.Untyped
public import N14.Energy.Types

/-!
# T7, a certificate with the types P/R: its data and its identities

**Types.** Two points of a configuration, the pair `P`, have the type `0`; all other points (`R`) have the type
`1`. A triple has one of the patterns `PPR`, `PRR`, `RRR`, and a certificate has one run of `N14.Box` for each
(`TRun`: the run, its three tables, its three polynomials of one variable and its constant). The kernels are
rooted at a point of the type `0` (`blocks0`) or `1` (`blocks1`).

**Shares.** A pair of points gives a function of one variable to a third point. With the slots of the runs:

| pair | third point | slot | function |
|---|---|---|---|
| `PP` | `R` | `PPR`, first | `psiPPu` |
| `PR` | `P` | `PPR`, second and third | `psiPRp` |
| `PR` | `R` | `PRR`, first and second | `psiPRr` |
| `RR` | `P` | `PRR`, third | `psiRRp` |
| `RR` | `R` | `RRR`, all three | `psiRRr` |

**Identities.** `TCert.Ok` collects what the kernel verifies: the identity of each run (`id3Ok`) with the kernels
that contain the three points of a triple of its pattern (`termsPPR`, `termsPRR`, `termsRRR`; a kernel whose two
arguments have the types `1`, `0` in this order is zero in the stored triangle and does not occur), and the
identity of a pair (`id1Ok`) for each of the three pairs of types: `id00` (third points: `N - 2` of the type
`1`), `id11` (two of the type `0`, `N - 4` of the type `1`) and `id01`, which is the sum of the identities of the
two orders of a pair with different types (third points: one of the type `0` and `N - 3` of the type `1`, for
each order; the kernels rooted at the point of the type `0` and at the point of the type `1`). Only this sum is a
multiple of the Coulomb potential plus a constant.

**Theorems.**

* `slack_ppr`, `slack_prr`, `slack_rrr`: the slack function of each run is its functions of one variable minus
  the kernels; `ppr_swap23`, `prr_swap12`, `rrr_swap12`, `rrr_swap23`: their symmetries.
* `pair00`, `pair01`, `pair11`: the identities of the pairs for these functions.
* `slackOf_ppr`, `slackOf_prr`, `slackOf_rrr`: the slack of a triple of a configuration (`slackOf`, with the
  shares `TCert.psi` and the kernels `TCert.blk`) is `cM` times the slack function of the run of its pattern.
* **`TCert.energy`**: the sum of the slacks of the ordered triples of distinct points of a configuration of `N`
  points of the unit sphere, two of which have the type `0`, is at most a multiple of the energy plus a
  constant. **`TCert.energy_ge`**: the energy is at least a rational number `en / ed`, determined by an equation
  between natural numbers, plus a multiple of the sum of the slacks.
* `slackOf_nonneg`: the slacks of all triples are nonnegative if the slack functions of the three runs are
  nonnegative at the triples of their patterns.
-/

@[expose] public section

namespace N14.Energy

open CAP CAP.ThreePoint N14.Box N14.Ident Finset

/-- The kernel polynomials depend on the parameters only through the layout of the matrices. -/
theorem kernZFrom_congr (P P' : ThreePoint.Params) (hw : P'.w = P.w) (ha : P'.a = P.a) (sel : ℕ) :
    ∀ (l : List Blk) (k : ℕ), kernZFrom P' sel l k = kernZFrom P sel l k
  | [], _ => rfl
  | B :: l, k => by
    have e : partZ P' B sel = partZ P B sel := by
      unfold partZ phi00Z phi01Z phiZ entZ
      rw [hw, ha]
    rw [kernZFrom, kernZFrom, e, kernZFrom_congr P P' hw ha sel l (k + 1)]

/-- A run of a certificate with types: the parameters of its identity, the run, its tables, its three
polynomials of one variable and its constant `cp - cn`. -/
structure TRun where
  P : ThreePoint.Params
  R : Run
  U1 : Tab
  U2 : Tab
  U3 : Tab
  B0 : ℕ
  B1 : ℕ
  B2 : ℕ
  cp : ℕ
  cn : ℕ

/-- The slack function of a run. -/
noncomputable def TRun.lam (T : TRun) (u v t : ℝ) : ℝ := slackFn T.R T.U1 T.U2 T.U3 u v t

/-- The data of a certificate with the types P/R. -/
structure TCert where
  /-- the parameters of the identities of the pairs; `w` and `a` are those of all blocks -/
  P : ThreePoint.Params
  blocks0 : List Blk
  blocks1 : List Blk
  N : ℕ
  cM : ℕ
  cK : ℕ
  wB : ℕ
  aB : ℕ
  c1 : ℕ
  fS : ℕ
  ppr : TRun
  prr : TRun
  rrr : TRun
  k00p : ℕ
  k00n : ℕ
  k01p : ℕ
  k01n : ℕ
  k11p : ℕ
  k11n : ℕ

namespace TCert

/-- The kernels that contain the three points of a triple of the pattern `PPR`, `PRR`, `RRR`. -/
def termsPPR (C : TCert) : List Term :=
  [⟨C.blocks0, 1, 0, 1, 2⟩, ⟨C.blocks0, 1, 0, 2, 1⟩, ⟨C.blocks1, 0, 1, 2, 0⟩, ⟨C.blocks1, 0, 2, 1, 0⟩]

def termsPRR (C : TCert) : List Term :=
  [⟨C.blocks0, 2, 0, 1, 2⟩, ⟨C.blocks0, 2, 1, 0, 2⟩, ⟨C.blocks1, 1, 0, 2, 1⟩, ⟨C.blocks1, 1, 1, 2, 0⟩]

def termsRRR (C : TCert) : List Term :=
  [⟨C.blocks1, 2, 0, 1, 2⟩, ⟨C.blocks1, 2, 1, 0, 2⟩, ⟨C.blocks1, 2, 0, 2, 1⟩, ⟨C.blocks1, 2, 2, 0, 1⟩,
    ⟨C.blocks1, 2, 1, 2, 0⟩, ⟨C.blocks1, 2, 2, 1, 0⟩]

/-- The data of the identity of a run. -/
def id3 (C : TCert) (T : TRun) (terms : List Term) : Id3 :=
  { n := T.R.n, aH := T.R.aH, PpM := T.R.PpM, cM := C.cM, cK := C.cK, terms := terms, wB := C.wB, aB := C.aB,
    B0 := T.B0, B1 := T.B1, B2 := T.B2, cp := T.cp, cn := T.cn }

/-- The slots of the five shares, with a multiplicity. -/
def sPPu (C : TCert) (m : ℕ) : Slot := ⟨m, C.ppr.U1, C.ppr.B0, C.ppr.cp, C.ppr.cn⟩
def sPRp (C : TCert) (m : ℕ) : Slot := ⟨m, C.ppr.U2, C.ppr.B1, C.ppr.cp, C.ppr.cn⟩
def sPRr (C : TCert) (m : ℕ) : Slot := ⟨m, C.prr.U1, C.prr.B0, C.prr.cp, C.prr.cn⟩
def sRRp (C : TCert) (m : ℕ) : Slot := ⟨m, C.prr.U3, C.prr.B2, C.prr.cp, C.prr.cn⟩
def sRRr (C : TCert) (m : ℕ) : Slot := ⟨m, C.rrr.U1, C.rrr.B0, C.rrr.cp, C.rrr.cn⟩

/-- The data of the identity of a pair. -/
def id1 (C : TCert) (slots : List Slot) (terms : List DTerm) (kp kn fS : ℕ) : Id1 :=
  { n := C.P.D, wB := C.wB, aB := C.aB, cM := C.cM, cK := C.cK, c1 := C.c1, shares := slots.map Slot.share,
    terms := terms, kp := kp, kn := kn, fS := fS }

/-- A pair of two points of the type `0`. -/
def id00 (C : TCert) : Id1 :=
  C.id1 [C.sPPu (C.N - 2)] [⟨C.blocks0, 0, 0⟩, ⟨C.blocks0, 0, 2⟩, ⟨C.blocks0, 0, 1⟩] C.k00p C.k00n C.fS

/-- A pair of points of different types, in its two orders together. -/
def id01 (C : TCert) : Id1 :=
  C.id1 [C.sPRp 2, C.sPRr (2 * (C.N - 3))]
    [⟨C.blocks0, 2, 0⟩, ⟨C.blocks0, 1, 2⟩, ⟨C.blocks1, 0, 0⟩, ⟨C.blocks1, 1, 1⟩] C.k01p C.k01n (2 * C.fS)

/-- A pair of two points of the type `1`. -/
def id11 (C : TCert) : Id1 :=
  C.id1 [C.sRRp 2, C.sRRr (C.N - 4)] [⟨C.blocks1, 2, 0⟩, ⟨C.blocks1, 2, 2⟩, ⟨C.blocks1, 2, 1⟩] C.k11p C.k11n C.fS

/-- What the kernel verifies for the certificate, and what the statement module supplies. -/
structure Ok (C : TCert) : Prop where
  hppr : id3Ok C.ppr.P (C.id3 C.ppr C.termsPPR) = true
  hprr : id3Ok C.prr.P (C.id3 C.prr C.termsPRR) = true
  hrrr : id3Ok C.rrr.P (C.id3 C.rrr C.termsRRR) = true
  h00 : id1Ok C.P C.id00 = true
  h01 : id1Ok C.P C.id01 = true
  h11 : id1Ok C.P C.id11 = true
  hWppr : C.ppr.P.W = C.ppr.R.V
  hWprr : C.prr.P.W = C.prr.R.V
  hWrrr : C.rrr.P.W = C.rrr.R.V
  hwppr : C.ppr.P.w = C.P.w ∧ C.ppr.P.a = C.P.a
  hwprr : C.prr.P.w = C.P.w ∧ C.prr.P.a = C.P.a
  hwrrr : C.rrr.P.w = C.P.w ∧ C.rrr.P.a = C.P.a
  hnppr : C.ppr.R.n = C.P.D
  hnprr : C.prr.R.n = C.P.D
  hnrrr : C.rrr.R.n = C.P.D
  hPD0 : BlkPD C.P C.blocks0
  hPD1 : BlkPD C.P C.blocks1
  hc1 : 0 < C.c1
  hcM : 0 < C.cM
  hN : 4 ≤ C.N
  hcPPu : C.ppr.U1.c1 = C.c1
  hcPRp : C.ppr.U2.c1 = C.c1
  hcPRr : C.prr.U1.c1 = C.c1
  hcRRp : C.prr.U3.c1 = C.c1
  hcRRr : C.rrr.U1.c1 = C.c1
  hTppr : ∀ s, tabFn C.ppr.U3 s = tabFn C.ppr.U2 s
  hBppr : C.ppr.B2 = C.ppr.B1
  hTprr : ∀ s, tabFn C.prr.U2 s = tabFn C.prr.U1 s
  hBprr : C.prr.B1 = C.prr.B0
  hTrrr2 : ∀ s, tabFn C.rrr.U2 s = tabFn C.rrr.U1 s
  hTrrr3 : ∀ s, tabFn C.rrr.U3 s = tabFn C.rrr.U1 s
  hBrrr1 : C.rrr.B1 = C.rrr.B0
  hBrrr2 : C.rrr.B2 = C.rrr.B0

/-- The five functions of one variable. -/
noncomputable def psiPPu (C : TCert) (s : ℝ) : ℝ := psiOf C.cM C.wB C.aB C.P.D C.ppr.U1 C.ppr.B0 C.ppr.cp C.ppr.cn s
noncomputable def psiPRp (C : TCert) (s : ℝ) : ℝ := psiOf C.cM C.wB C.aB C.P.D C.ppr.U2 C.ppr.B1 C.ppr.cp C.ppr.cn s
noncomputable def psiPRr (C : TCert) (s : ℝ) : ℝ := psiOf C.cM C.wB C.aB C.P.D C.prr.U1 C.prr.B0 C.prr.cp C.prr.cn s
noncomputable def psiRRp (C : TCert) (s : ℝ) : ℝ := psiOf C.cM C.wB C.aB C.P.D C.prr.U3 C.prr.B2 C.prr.cp C.prr.cn s
noncomputable def psiRRr (C : TCert) (s : ℝ) : ℝ := psiOf C.cM C.wB C.aB C.P.D C.rrr.U1 C.rrr.B0 C.rrr.cp C.rrr.cn s

/-- The kernels rooted at a point of the type `0` and `1`, for two points of the types `σ`, `σ'`. -/
noncomputable def K0 (C : TCert) (σ σ' : ℕ) (u v t : ℝ) : ℝ := kerR C.P C.blocks0 0 σ σ' u v t
noncomputable def K1 (C : TCert) (σ σ' : ℕ) (u v t : ℝ) : ℝ := kerR C.P C.blocks1 0 σ σ' u v t

theorem n0_of_terms {m : ℕ} {T : Term} {l : List Term} (h : termsOk m (T :: l) = true) :
    (∀ B ∈ T.blocks, B.n0 ≤ B.N) ∧ termsOk m l = true := by
  rw [termsOk_cons] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨blocksOk_n0 _ _ 0 h.1.1.1.1.1.1.1, h.2⟩

theorem blocks0_n0 (C : TCert) (hC : C.Ok) : ∀ B ∈ C.blocks0, B.n0 ≤ B.N :=
  (n0_of_terms (facts3_of_ok hC.hppr).hterms).1

theorem blocks1_n0 (C : TCert) (hC : C.Ok) : ∀ B ∈ C.blocks1, B.n0 ≤ B.N :=
  (n0_of_terms (facts3_of_ok hC.hrrr).hterms).1

/-- The values of the kernel polynomials of a run are the kernels. -/
theorem evR_kern0 (C : TCert) (hC : C.Ok) (P' : ThreePoint.Params) (hP : P'.w = C.P.w ∧ P'.a = C.P.a)
    (σ σ' : ℕ) (hσ : ¬ (σ ≠ 0 ∧ σ' = 0)) (u v t : ℝ) :
    evR u v t (kernZ P' (selOf σ σ') C.blocks0) = C.K0 σ σ' u v t := by
  unfold K0 kernZ
  rw [kerR_eq C.P σ σ' u v t C.blocks0 0 (C.blocks0_n0 hC), if_neg hσ, kernZFrom_congr C.P P' hP.1 hP.2]

theorem evR_kern1 (C : TCert) (hC : C.Ok) (P' : ThreePoint.Params) (hP : P'.w = C.P.w ∧ P'.a = C.P.a)
    (σ σ' : ℕ) (hσ : ¬ (σ ≠ 0 ∧ σ' = 0)) (u v t : ℝ) :
    evR u v t (kernZ P' (selOf σ σ') C.blocks1) = C.K1 σ σ' u v t := by
  unfold K1 kernZ
  rw [kerR_eq C.P σ σ' u v t C.blocks1 0 (C.blocks1_n0 hC), if_neg hσ, kernZFrom_congr C.P P' hP.1 hP.2]

/-- A kernel whose arguments have the types `1`, `0` in this order vanishes. -/
theorem K0_10 (C : TCert) (hC : C.Ok) (u v t : ℝ) : C.K0 1 0 u v t = 0 := by
  unfold K0
  rw [kerR_eq C.P 1 0 u v t C.blocks0 0 (C.blocks0_n0 hC), if_pos ⟨by norm_num, rfl⟩]

theorem K1_10 (C : TCert) (hC : C.Ok) (u v t : ℝ) : C.K1 1 0 u v t = 0 := by
  unfold K1
  rw [kerR_eq C.P 1 0 u v t C.blocks1 0 (C.blocks1_n0 hC), if_pos ⟨by norm_num, rfl⟩]

/-! ## The slack functions of the three runs -/

theorem slack_ppr (C : TCert) (hC : C.Ok) (u v t : ℝ) :
    (C.cM : ℝ) * C.ppr.lam u v t = C.psiPPu u + C.psiPRp v + C.psiPRp t
      - (C.cK : ℝ) * (C.K0 0 1 u v t + C.K0 0 1 u t v + C.K1 0 0 v t u + C.K1 0 0 t v u) := by
  have h := slack_id3 C.ppr.P C.ppr.R C.ppr.U1 C.ppr.U2 C.ppr.U3 (C.id3 C.ppr C.termsPPR) hC.hppr hC.hWppr rfl
    rfl rfl u v t
  have e1 : psiOf (C.id3 C.ppr C.termsPPR).cM (C.id3 C.ppr C.termsPPR).wB (C.id3 C.ppr C.termsPPR).aB
      (C.id3 C.ppr C.termsPPR).n C.ppr.U1 (C.id3 C.ppr C.termsPPR).B0 (C.id3 C.ppr C.termsPPR).cp
      (C.id3 C.ppr C.termsPPR).cn u = C.psiPPu u := by
    unfold psiPPu
    rw [← hC.hnppr]
    rfl
  have e2 : psiOf (C.id3 C.ppr C.termsPPR).cM (C.id3 C.ppr C.termsPPR).wB (C.id3 C.ppr C.termsPPR).aB
      (C.id3 C.ppr C.termsPPR).n C.ppr.U2 (C.id3 C.ppr C.termsPPR).B1 (C.id3 C.ppr C.termsPPR).cp
      (C.id3 C.ppr C.termsPPR).cn v = C.psiPRp v := by
    unfold psiPRp
    rw [← hC.hnppr]
    rfl
  have e3 : psiOf (C.id3 C.ppr C.termsPPR).cM (C.id3 C.ppr C.termsPPR).wB (C.id3 C.ppr C.termsPPR).aB
      (C.id3 C.ppr C.termsPPR).n C.ppr.U3 (C.id3 C.ppr C.termsPPR).B2 (C.id3 C.ppr C.termsPPR).cp
      (C.id3 C.ppr C.termsPPR).cn t = C.psiPRp t := by
    unfold psiPRp psiOf
    rw [← hC.hnppr, hC.hTppr]
    show _ + uniR C.wB C.aB C.ppr.R.n C.ppr.B2 t + _ = _
    rw [hC.hBppr]
    rfl
  have et : termsR C.ppr.P (C.id3 C.ppr C.termsPPR).terms u v t
      = C.K0 0 1 u v t + C.K0 0 1 u t v + C.K1 0 0 v t u + C.K1 0 0 t v u := by
    rw [← C.evR_kern0 hC C.ppr.P hC.hwppr 0 1 (by norm_num), ← C.evR_kern0 hC C.ppr.P hC.hwppr 0 1 (by norm_num),
      ← C.evR_kern1 hC C.ppr.P hC.hwppr 0 0 (by norm_num), ← C.evR_kern1 hC C.ppr.P hC.hwppr 0 0 (by norm_num)]
    show termsR C.ppr.P C.termsPPR u v t = _
    simp only [termsPPR, termsR, termR, pick, selOf]
    norm_num
    ring
  rw [e1, e2, e3, et] at h
  exact h

theorem slack_prr (C : TCert) (hC : C.Ok) (u v t : ℝ) :
    (C.cM : ℝ) * C.prr.lam u v t = C.psiPRr u + C.psiPRr v + C.psiRRp t
      - (C.cK : ℝ) * (C.K0 1 1 u v t + C.K0 1 1 v u t + C.K1 0 1 u t v + C.K1 0 1 v t u) := by
  have h := slack_id3 C.prr.P C.prr.R C.prr.U1 C.prr.U2 C.prr.U3 (C.id3 C.prr C.termsPRR) hC.hprr hC.hWprr rfl
    rfl rfl u v t
  have e1 : psiOf (C.id3 C.prr C.termsPRR).cM (C.id3 C.prr C.termsPRR).wB (C.id3 C.prr C.termsPRR).aB
      (C.id3 C.prr C.termsPRR).n C.prr.U1 (C.id3 C.prr C.termsPRR).B0 (C.id3 C.prr C.termsPRR).cp
      (C.id3 C.prr C.termsPRR).cn u = C.psiPRr u := by
    unfold psiPRr
    rw [← hC.hnprr]
    rfl
  have e2 : psiOf (C.id3 C.prr C.termsPRR).cM (C.id3 C.prr C.termsPRR).wB (C.id3 C.prr C.termsPRR).aB
      (C.id3 C.prr C.termsPRR).n C.prr.U2 (C.id3 C.prr C.termsPRR).B1 (C.id3 C.prr C.termsPRR).cp
      (C.id3 C.prr C.termsPRR).cn v = C.psiPRr v := by
    unfold psiPRr psiOf
    rw [← hC.hnprr, hC.hTprr]
    show _ + uniR C.wB C.aB C.prr.R.n C.prr.B1 v + _ = _
    rw [hC.hBprr]
    rfl
  have e3 : psiOf (C.id3 C.prr C.termsPRR).cM (C.id3 C.prr C.termsPRR).wB (C.id3 C.prr C.termsPRR).aB
      (C.id3 C.prr C.termsPRR).n C.prr.U3 (C.id3 C.prr C.termsPRR).B2 (C.id3 C.prr C.termsPRR).cp
      (C.id3 C.prr C.termsPRR).cn t = C.psiRRp t := by
    unfold psiRRp
    rw [← hC.hnprr]
    rfl
  have et : termsR C.prr.P (C.id3 C.prr C.termsPRR).terms u v t
      = C.K0 1 1 u v t + C.K0 1 1 v u t + C.K1 0 1 u t v + C.K1 0 1 v t u := by
    rw [← C.evR_kern0 hC C.prr.P hC.hwprr 1 1 (by norm_num), ← C.evR_kern0 hC C.prr.P hC.hwprr 1 1 (by norm_num),
      ← C.evR_kern1 hC C.prr.P hC.hwprr 0 1 (by norm_num), ← C.evR_kern1 hC C.prr.P hC.hwprr 0 1 (by norm_num)]
    show termsR C.prr.P C.termsPRR u v t = _
    simp only [termsPRR, termsR, termR, pick, selOf]
    norm_num
    ring
  rw [e1, e2, e3, et] at h
  exact h

theorem slack_rrr (C : TCert) (hC : C.Ok) (u v t : ℝ) :
    (C.cM : ℝ) * C.rrr.lam u v t = C.psiRRr u + C.psiRRr v + C.psiRRr t
      - (C.cK : ℝ) * (C.K1 1 1 u v t + C.K1 1 1 v u t + C.K1 1 1 u t v + C.K1 1 1 t u v + C.K1 1 1 v t u
        + C.K1 1 1 t v u) := by
  have h := slack_id3 C.rrr.P C.rrr.R C.rrr.U1 C.rrr.U2 C.rrr.U3 (C.id3 C.rrr C.termsRRR) hC.hrrr hC.hWrrr rfl
    rfl rfl u v t
  have e1 : psiOf (C.id3 C.rrr C.termsRRR).cM (C.id3 C.rrr C.termsRRR).wB (C.id3 C.rrr C.termsRRR).aB
      (C.id3 C.rrr C.termsRRR).n C.rrr.U1 (C.id3 C.rrr C.termsRRR).B0 (C.id3 C.rrr C.termsRRR).cp
      (C.id3 C.rrr C.termsRRR).cn u = C.psiRRr u := by
    unfold psiRRr
    rw [← hC.hnrrr]
    rfl
  have e2 : psiOf (C.id3 C.rrr C.termsRRR).cM (C.id3 C.rrr C.termsRRR).wB (C.id3 C.rrr C.termsRRR).aB
      (C.id3 C.rrr C.termsRRR).n C.rrr.U2 (C.id3 C.rrr C.termsRRR).B1 (C.id3 C.rrr C.termsRRR).cp
      (C.id3 C.rrr C.termsRRR).cn v = C.psiRRr v := by
    unfold psiRRr psiOf
    rw [← hC.hnrrr, hC.hTrrr2]
    show _ + uniR C.wB C.aB C.rrr.R.n C.rrr.B1 v + _ = _
    rw [hC.hBrrr1]
    rfl
  have e3 : psiOf (C.id3 C.rrr C.termsRRR).cM (C.id3 C.rrr C.termsRRR).wB (C.id3 C.rrr C.termsRRR).aB
      (C.id3 C.rrr C.termsRRR).n C.rrr.U3 (C.id3 C.rrr C.termsRRR).B2 (C.id3 C.rrr C.termsRRR).cp
      (C.id3 C.rrr C.termsRRR).cn t = C.psiRRr t := by
    unfold psiRRr psiOf
    rw [← hC.hnrrr, hC.hTrrr3]
    show _ + uniR C.wB C.aB C.rrr.R.n C.rrr.B2 t + _ = _
    rw [hC.hBrrr2]
    rfl
  have et : termsR C.rrr.P (C.id3 C.rrr C.termsRRR).terms u v t
      = C.K1 1 1 u v t + C.K1 1 1 v u t + C.K1 1 1 u t v + C.K1 1 1 t u v + C.K1 1 1 v t u + C.K1 1 1 t v u := by
    rw [← C.evR_kern1 hC C.rrr.P hC.hwrrr 1 1 (by norm_num), ← C.evR_kern1 hC C.rrr.P hC.hwrrr 1 1 (by norm_num),
      ← C.evR_kern1 hC C.rrr.P hC.hwrrr 1 1 (by norm_num), ← C.evR_kern1 hC C.rrr.P hC.hwrrr 1 1 (by norm_num),
      ← C.evR_kern1 hC C.rrr.P hC.hwrrr 1 1 (by norm_num), ← C.evR_kern1 hC C.rrr.P hC.hwrrr 1 1 (by norm_num)]
    show termsR C.rrr.P C.termsRRR u v t = _
    simp only [termsRRR, termsR, termR, pick, selOf]
    norm_num
    ring
  rw [e1, e2, e3, et] at h
  exact h

/-! ## The symmetries of the slack functions -/

theorem ppr_swap23 (C : TCert) (hC : C.Ok) (u v t : ℝ) : C.ppr.lam u v t = C.ppr.lam u t v := by
  have hc : (C.cM : ℝ) ≠ 0 := by exact_mod_cast hC.hcM.ne'
  have e : (C.cM : ℝ) * C.ppr.lam u v t = (C.cM : ℝ) * C.ppr.lam u t v := by
    rw [C.slack_ppr hC, C.slack_ppr hC]
    ring
  exact mul_left_cancel₀ hc e

theorem prr_swap12 (C : TCert) (hC : C.Ok) (u v t : ℝ) : C.prr.lam u v t = C.prr.lam v u t := by
  have hc : (C.cM : ℝ) ≠ 0 := by exact_mod_cast hC.hcM.ne'
  have e : (C.cM : ℝ) * C.prr.lam u v t = (C.cM : ℝ) * C.prr.lam v u t := by
    rw [C.slack_prr hC, C.slack_prr hC]
    ring
  exact mul_left_cancel₀ hc e

theorem rrr_swap12 (C : TCert) (hC : C.Ok) (u v t : ℝ) : C.rrr.lam u v t = C.rrr.lam v u t := by
  have hc : (C.cM : ℝ) ≠ 0 := by exact_mod_cast hC.hcM.ne'
  have e : (C.cM : ℝ) * C.rrr.lam u v t = (C.cM : ℝ) * C.rrr.lam v u t := by
    rw [C.slack_rrr hC, C.slack_rrr hC]
    ring
  exact mul_left_cancel₀ hc e

theorem rrr_swap23 (C : TCert) (hC : C.Ok) (u v t : ℝ) : C.rrr.lam u v t = C.rrr.lam u t v := by
  have hc : (C.cM : ℝ) ≠ 0 := by exact_mod_cast hC.hcM.ne'
  have e : (C.cM : ℝ) * C.rrr.lam u v t = (C.cM : ℝ) * C.rrr.lam u t v := by
    rw [C.slack_rrr hC, C.slack_rrr hC]
    ring
  exact mul_left_cancel₀ hc e

/-! ## The identities of the pairs -/

theorem cast_sub_of_le {N k : ℕ} (h : k ≤ N) : ((N - k : ℕ) : ℝ) = (N : ℝ) - k := by
  push_cast [Nat.cast_sub h]
  ring

/-- The identity of a pair of two points of the type `0`. -/
theorem pair00 (C : TCert) (hC : C.Ok) (s : ℝ) :
    3 * (((C.N : ℝ) - 2) * C.psiPPu s) + 6 * (C.cK : ℝ) * (C.K0 0 0 s s 1 + C.K0 0 0 1 s s + C.K0 0 0 s 1 s)
      = 3 * (C.cM : ℝ) * (C.fS : ℝ) / (C.c1 : ℝ) / Real.sqrt (2 - 2 * s)
        + ((C.k00p : ℝ) - C.k00n) / (C.c1 : ℝ) := by
  have h := pair_id1 C.P C.id00 [C.sPPu (C.N - 2)] rfl (fun S hS => by
    rw [List.mem_singleton.mp hS]
    exact hC.hcPPu) hC.hc1 hC.h00 s
  have hN2 : ((C.N - 2 : ℕ) : ℝ) = (C.N : ℝ) - 2 := by
    have := hC.hN
    exact_mod_cast cast_sub_of_le (by omega : 2 ≤ C.N)
  have es : slotsR C.id00.cM C.id00.wB C.id00.aB C.id00.n [C.sPPu (C.N - 2)] s = ((C.N : ℝ) - 2) * C.psiPPu s := by
    simp only [slotsR, add_zero]
    rw [← hN2]
    rfl
  have et : dtermsR C.P C.id00.terms s = C.K0 0 0 s s 1 + C.K0 0 0 1 s s + C.K0 0 0 s 1 s := by
    rw [← C.evR_kern0 hC C.P ⟨rfl, rfl⟩ 0 0 (by norm_num), ← C.evR_kern0 hC C.P ⟨rfl, rfl⟩ 0 0 (by norm_num),
      ← C.evR_kern0 hC C.P ⟨rfl, rfl⟩ 0 0 (by norm_num)]
    show dtermsR C.P [⟨C.blocks0, 0, 0⟩, ⟨C.blocks0, 0, 2⟩, ⟨C.blocks0, 0, 1⟩] s = _
    simp only [dtermsR, dtermR, selOf]
    norm_num
    ring
  rw [es, et] at h
  exact h

/-- The identity of a pair of points of different types: its two orders together. -/
theorem pair01 (C : TCert) (hC : C.Ok) (s : ℝ) :
    3 * (2 * C.psiPRp s + 2 * ((C.N : ℝ) - 3) * C.psiPRr s)
        + 6 * (C.cK : ℝ) * (C.K0 1 1 s s 1 + C.K0 0 1 1 s s + C.K1 0 0 s s 1 + C.K1 0 1 s 1 s)
      = 3 * (C.cM : ℝ) * (2 * (C.fS : ℝ)) / (C.c1 : ℝ) / Real.sqrt (2 - 2 * s)
        + ((C.k01p : ℝ) - C.k01n) / (C.c1 : ℝ) := by
  have h := pair_id1 C.P C.id01 [C.sPRp 2, C.sPRr (2 * (C.N - 3))] rfl (fun S hS => by
    rcases List.mem_cons.mp hS with h1 | h1
    · rw [h1]
      exact hC.hcPRp
    · rw [List.mem_singleton.mp h1]
      exact hC.hcPRr) hC.hc1 hC.h01 s
  have hN3 : ((C.N - 3 : ℕ) : ℝ) = (C.N : ℝ) - 3 := by
    have := hC.hN
    exact_mod_cast cast_sub_of_le (by omega : 3 ≤ C.N)
  have es : slotsR C.id01.cM C.id01.wB C.id01.aB C.id01.n [C.sPRp 2, C.sPRr (2 * (C.N - 3))] s
      = 2 * C.psiPRp s + 2 * ((C.N : ℝ) - 3) * C.psiPRr s := by
    simp only [slotsR, add_zero]
    rw [← hN3]
    show ((2 : ℕ) : ℝ) * C.psiPRp s + ((2 * (C.N - 3) : ℕ) : ℝ) * C.psiPRr s = _
    push_cast
    ring
  have et : dtermsR C.P C.id01.terms s = C.K0 1 1 s s 1 + C.K0 0 1 1 s s + C.K1 0 0 s s 1 + C.K1 0 1 s 1 s := by
    rw [← C.evR_kern0 hC C.P ⟨rfl, rfl⟩ 1 1 (by norm_num), ← C.evR_kern0 hC C.P ⟨rfl, rfl⟩ 0 1 (by norm_num),
      ← C.evR_kern1 hC C.P ⟨rfl, rfl⟩ 0 0 (by norm_num), ← C.evR_kern1 hC C.P ⟨rfl, rfl⟩ 0 1 (by norm_num)]
    show dtermsR C.P [⟨C.blocks0, 2, 0⟩, ⟨C.blocks0, 1, 2⟩, ⟨C.blocks1, 0, 0⟩, ⟨C.blocks1, 1, 1⟩] s = _
    simp only [dtermsR, dtermR, selOf]
    norm_num
    ring
  have ef : ((C.id01.fS : ℕ) : ℝ) = 2 * (C.fS : ℝ) := by
    show ((2 * C.fS : ℕ) : ℝ) = _
    push_cast
    ring
  rw [es, et, ef] at h
  exact h

/-- The identity of a pair of two points of the type `1`. -/
theorem pair11 (C : TCert) (hC : C.Ok) (s : ℝ) :
    3 * (2 * C.psiRRp s + ((C.N : ℝ) - 4) * C.psiRRr s)
        + 6 * (C.cK : ℝ) * (C.K1 1 1 s s 1 + C.K1 1 1 1 s s + C.K1 1 1 s 1 s)
      = 3 * (C.cM : ℝ) * (C.fS : ℝ) / (C.c1 : ℝ) / Real.sqrt (2 - 2 * s)
        + ((C.k11p : ℝ) - C.k11n) / (C.c1 : ℝ) := by
  have h := pair_id1 C.P C.id11 [C.sRRp 2, C.sRRr (C.N - 4)] rfl (fun S hS => by
    rcases List.mem_cons.mp hS with h1 | h1
    · rw [h1]
      exact hC.hcRRp
    · rw [List.mem_singleton.mp h1]
      exact hC.hcRRr) hC.hc1 hC.h11 s
  have hN4 : ((C.N - 4 : ℕ) : ℝ) = (C.N : ℝ) - 4 := by
    have := hC.hN
    exact_mod_cast cast_sub_of_le (by omega : 4 ≤ C.N)
  have es : slotsR C.id11.cM C.id11.wB C.id11.aB C.id11.n [C.sRRp 2, C.sRRr (C.N - 4)] s
      = 2 * C.psiRRp s + ((C.N : ℝ) - 4) * C.psiRRr s := by
    simp only [slotsR, add_zero]
    rw [← hN4]
    show ((2 : ℕ) : ℝ) * C.psiRRp s + ((C.N - 4 : ℕ) : ℝ) * C.psiRRr s = _
    push_cast
    ring
  have et : dtermsR C.P C.id11.terms s = C.K1 1 1 s s 1 + C.K1 1 1 1 s s + C.K1 1 1 s 1 s := by
    rw [← C.evR_kern1 hC C.P ⟨rfl, rfl⟩ 1 1 (by norm_num), ← C.evR_kern1 hC C.P ⟨rfl, rfl⟩ 1 1 (by norm_num),
      ← C.evR_kern1 hC C.P ⟨rfl, rfl⟩ 1 1 (by norm_num)]
    show dtermsR C.P [⟨C.blocks1, 2, 0⟩, ⟨C.blocks1, 2, 2⟩, ⟨C.blocks1, 2, 1⟩] s = _
    simp only [dtermsR, dtermR, selOf]
    norm_num
    ring
  rw [es, et] at h
  exact h

/-! ## The slack of a triple of a configuration -/

/-- The blocks of the kernel rooted at a point of a type. -/
def blk (C : TCert) (r : ℕ) : List Blk := if r = 0 then C.blocks0 else C.blocks1

theorem blk_zero (C : TCert) : C.blk 0 = C.blocks0 := if_pos rfl

theorem blk_one (C : TCert) : C.blk 1 = C.blocks1 := if_neg (by norm_num)

/-- The share that a pair of the types `a`, `b` gives to a third point of the type `c`. -/
noncomputable def psi (C : TCert) (a b c : ℕ) : ℝ → ℝ :=
  if a = 0 ∧ b = 0 then C.psiPPu
  else if a = 0 ∨ b = 0 then (if c = 0 then C.psiPRp else C.psiPRr)
  else (if c = 0 then C.psiRRp else C.psiRRr)

theorem psi_symm (C : TCert) (a b c : ℕ) (s : ℝ) : C.psi a b c s = C.psi b a c s := by
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [psi, ha, hb]

theorem psi_00 (C : TCert) (c : ℕ) : C.psi 0 0 c = C.psiPPu := by simp [psi]

theorem psi_010 (C : TCert) : C.psi 0 1 0 = C.psiPRp := by simp [psi]

theorem psi_011 (C : TCert) : C.psi 0 1 1 = C.psiPRr := by simp [psi]

theorem psi_100 (C : TCert) : C.psi 1 0 0 = C.psiPRp := by simp [psi]

theorem psi_101 (C : TCert) : C.psi 1 0 1 = C.psiPRr := by simp [psi]

theorem psi_110 (C : TCert) : C.psi 1 1 0 = C.psiRRp := by simp [psi]

theorem psi_111 (C : TCert) : C.psi 1 1 1 = C.psiRRr := by simp [psi]

theorem Kf_zero (C : TCert) (σ σ' : ℕ) (u v t : ℝ) : Kf C.P C.blk 0 σ σ' u v t = C.K0 σ σ' u v t := by
  unfold Kf K0
  rw [blk_zero]

theorem Kf_one (C : TCert) (σ σ' : ℕ) (u v t : ℝ) : Kf C.P C.blk 1 σ σ' u v t = C.K1 σ σ' u v t := by
  unfold Kf K1
  rw [blk_one]

theorem blk_pd (C : TCert) (hC : C.Ok) (r : ℕ) : BlkPD C.P (C.blk r) := by
  unfold blk
  split_ifs
  · exact hC.hPD0
  · exact hC.hPD1

variable {ι : Type*}

/-- The slack of a triple with the types `0`, `0`, `1` is the slack function of the run `PPR`. -/
theorem slackOf_ppr (C : TCert) (hC : C.Ok) (τ : ι → ℕ) (x : ι → EuclideanSpace ℝ (Fin 3)) (i j k : ι)
    (hi : τ i = 0) (hj : τ j = 0) (hk : τ k = 1) :
    slackOf C.P C.blk (C.cK : ℝ) C.psi τ x i j k = (C.cM : ℝ) * C.ppr.lam (ip x i j) (ip x i k) (ip x j k) := by
  have h1 : ip x j i = ip x i j := real_inner_comm _ _
  have h2 : ip x k i = ip x i k := real_inner_comm _ _
  have h3 : ip x k j = ip x j k := real_inner_comm _ _
  rw [C.slack_ppr hC]
  unfold slackOf
  rw [hi, hj, hk, h1, h2, h3]
  simp only [Kf_zero, Kf_one, K0_10 C hC, psi_00, psi_010]
  ring

/-- The slack of a triple with the types `0`, `1`, `1` is the slack function of the run `PRR`. -/
theorem slackOf_prr (C : TCert) (hC : C.Ok) (τ : ι → ℕ) (x : ι → EuclideanSpace ℝ (Fin 3)) (i j k : ι)
    (hi : τ i = 0) (hj : τ j = 1) (hk : τ k = 1) :
    slackOf C.P C.blk (C.cK : ℝ) C.psi τ x i j k = (C.cM : ℝ) * C.prr.lam (ip x i j) (ip x i k) (ip x j k) := by
  have h1 : ip x j i = ip x i j := real_inner_comm _ _
  have h2 : ip x k i = ip x i k := real_inner_comm _ _
  have h3 : ip x k j = ip x j k := real_inner_comm _ _
  rw [C.slack_prr hC]
  unfold slackOf
  rw [hi, hj, hk, h1, h2, h3]
  simp only [Kf_zero, Kf_one, K1_10 C hC, psi_011, psi_110]
  ring

/-- The slack of a triple with the types `1`, `1`, `1` is the slack function of the run `RRR`. -/
theorem slackOf_rrr (C : TCert) (hC : C.Ok) (τ : ι → ℕ) (x : ι → EuclideanSpace ℝ (Fin 3)) (i j k : ι)
    (hi : τ i = 1) (hj : τ j = 1) (hk : τ k = 1) :
    slackOf C.P C.blk (C.cK : ℝ) C.psi τ x i j k = (C.cM : ℝ) * C.rrr.lam (ip x i j) (ip x i k) (ip x j k) := by
  have h1 : ip x j i = ip x i j := real_inner_comm _ _
  have h2 : ip x k i = ip x i k := real_inner_comm _ _
  have h3 : ip x k j = ip x j k := real_inner_comm _ _
  rw [C.slack_rrr hC]
  unfold slackOf
  rw [hi, hj, hk, h1, h2, h3]
  simp only [Kf_one, psi_111]

/-- **The slacks of all triples of a configuration are nonnegative** if the slack functions of the three runs
are nonnegative at the triples of their patterns: the pair `p`, `q` with a third point; a point of the pair with
two other points; three other points. -/
theorem slackOf_nonneg [DecidableEq ι] (C : TCert) (hC : C.Ok) (x : ι → EuclideanSpace ℝ (Fin 3)) (p q : ι)
    (hppr : ∀ k, k ≠ p → k ≠ q → 0 ≤ C.ppr.lam (ip x p q) (ip x p k) (ip x q k))
    (hprr : ∀ i j k, (i = p ∨ i = q) → j ≠ p → j ≠ q → k ≠ p → k ≠ q → j ≠ k →
      0 ≤ C.prr.lam (ip x i j) (ip x i k) (ip x j k))
    (hrrr : ∀ i j k, i ≠ p → i ≠ q → j ≠ p → j ≠ q → k ≠ p → k ≠ q → Distinct3 i j k →
      0 ≤ C.rrr.lam (ip x i j) (ip x i k) (ip x j k))
    (i j k : ι) (hd : Distinct3 i j k) : 0 ≤ slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x i j k := by
  have hcM : (0 : ℝ) ≤ C.cM := Nat.cast_nonneg _
  have s12 := slackOf_swap12 C.P C.blk (C.cK : ℝ) C.psi C.psi_symm (tau p q) x
  have s23 := slackOf_swap23 C.P C.blk (C.cK : ℝ) C.psi C.psi_symm (tau p q) x
  -- the three patterns with the points of the type `0` first
  have a001 : ∀ i j k, tau p q i = 0 → tau p q j = 0 → tau p q k = 1 → i ≠ j →
      0 ≤ slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x i j k := by
    intro i j k hi hj hk hij
    have hk' := tau_one hk
    rcases tau_zero hi with rfl | rfl <;> rcases tau_zero hj with rfl | rfl
    · exact absurd rfl hij
    · rw [C.slackOf_ppr hC _ x _ _ k hi hj hk]
      exact mul_nonneg hcM (hppr k hk'.1 hk'.2)
    · rw [s12, C.slackOf_ppr hC _ x _ _ k hj hi hk]
      exact mul_nonneg hcM (hppr k hk'.1 hk'.2)
    · exact absurd rfl hij
  have a011 : ∀ i j k, tau p q i = 0 → tau p q j = 1 → tau p q k = 1 → j ≠ k →
      0 ≤ slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x i j k := by
    intro i j k hi hj hk hjk
    rw [C.slackOf_prr hC _ x i j k hi hj hk]
    exact mul_nonneg hcM (hprr i j k (tau_zero hi) (tau_one hj).1 (tau_one hj).2 (tau_one hk).1 (tau_one hk).2 hjk)
  obtain ⟨hij, hik, hjk⟩ := hd
  rcases tau_cases p q i with hi | hi <;> rcases tau_cases p q j with hj | hj <;>
    rcases tau_cases p q k with hk | hk
  · exact absurd (not_three_of_two (tau_zero hi) (tau_zero hj) (tau_zero hk) ⟨hij, hik, hjk⟩) id
  · exact a001 i j k hi hj hk hij
  · rw [s23]
    exact a001 i k j hi hk hj hik
  · exact a011 i j k hi hj hk hjk
  · rw [s12, s23]
    exact a001 j k i hj hk hi hjk
  · rw [s12]
    exact a011 j i k hj hi hk hik
  · rw [s23, s12]
    exact a011 k i j hk hi hj hij
  · rw [C.slackOf_rrr hC _ x i j k hi hj hk]
    exact mul_nonneg hcM (hrrr i j k (tau_one hi).1 (tau_one hi).2 (tau_one hj).1 (tau_one hj).2 (tau_one hk).1
      (tau_one hk).2 ⟨hij, hik, hjk⟩)

/-! ## The bound for the energy -/

/-- The side of the energy of the identity of a pair with the types `a`, `b`: the shares that the pair gives to
the third points, and the kernels rooted at its first point that contain the pair. -/
noncomputable def pairG (C : TCert) (a b : ℕ) (s : ℝ) : ℝ :=
  3 * (2 * C.psi a b 0 s + ((C.N : ℝ) - 2) * C.psi a b 1 s - C.psi a b a s - C.psi a b b s)
    + 6 * (C.cK : ℝ) * (Kf C.P C.blk a b b s s 1 + Kf C.P C.blk a a b 1 s s + Kf C.P C.blk a b a s 1 s)

theorem pairG_00 (C : TCert) (hC : C.Ok) (s : ℝ) :
    C.pairG 0 0 s = 3 * (C.cM : ℝ) * (C.fS : ℝ) / (C.c1 : ℝ) * (1 / Real.sqrt (2 - 2 * s))
      + ((C.k00p : ℝ) - C.k00n) / (C.c1 : ℝ) := by
  have h := C.pair00 hC s
  unfold pairG
  simp only [Kf_zero, psi_00]
  linear_combination h

theorem pairG_11 (C : TCert) (hC : C.Ok) (s : ℝ) :
    C.pairG 1 1 s = 3 * (C.cM : ℝ) * (C.fS : ℝ) / (C.c1 : ℝ) * (1 / Real.sqrt (2 - 2 * s))
      + ((C.k11p : ℝ) - C.k11n) / (C.c1 : ℝ) := by
  have h := C.pair11 hC s
  unfold pairG
  simp only [Kf_one, psi_110, psi_111]
  linear_combination h

theorem pairG_01 (C : TCert) (hC : C.Ok) (s : ℝ) :
    C.pairG 0 1 s + C.pairG 1 0 s
      = 2 * (3 * (C.cM : ℝ) * (C.fS : ℝ) / (C.c1 : ℝ)) * (1 / Real.sqrt (2 - 2 * s))
        + ((C.k01p : ℝ) - C.k01n) / (C.c1 : ℝ) := by
  have h := C.pair01 hC s
  unfold pairG
  simp only [Kf_zero, Kf_one, K0_10 C hC, K1_10 C hC, psi_010, psi_011, psi_100, psi_101]
  linear_combination h

/-- **The bound for the sum of the slacks of a configuration** with the two points `p`, `q` of the type `0`. -/
theorem energy (C : TCert) (hC : C.Ok) (x : Fin C.N → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1)
    (p q : Fin C.N) (hpq : p ≠ q) :
    dsum (slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x)
      ≤ 3 * (C.cM : ℝ) * (C.fS : ℝ) / (C.c1 : ℝ)
          * (∑ i, ∑ j, if i ≠ j then 1 / Real.sqrt (2 - 2 * ip x i j) else 0)
        + (2 * ((C.k00p : ℝ) - C.k00n) + 2 * ((C.N : ℝ) - 2) * ((C.k01p : ℝ) - C.k01n)
          + ((C.N : ℝ) - 2) * ((C.N : ℝ) - 3) * ((C.k11p : ℝ) - C.k11n)) / (C.c1 : ℝ)
        + 6 * (C.cK : ℝ) * (2 * C.K0 0 0 1 1 1 + ((C.N : ℝ) - 2) * C.K1 1 1 1 1 1) := by
  have hsym : ∀ i j, ip x i j = ip x j i := fun i j => real_inner_comm _ _
  have hcard : (Fintype.card (Fin C.N) : ℝ) = C.N := by simp
  have main := slack_sum_le C.P C.blk (C.blk_pd hC) (C.cK : ℝ) (Nat.cast_nonneg _) C.psi (tau p q) x hx
    (fun i j => C.pairG (tau p q i) (tau p q j) (ip x i j)) (fun i j hij => by
      have hs : (∑ k, if i ≠ k ∧ j ≠ k then C.psi (tau p q i) (tau p q j) (tau p q k) (ip x i j) else 0)
          = (∑ k, C.psi (tau p q i) (tau p q j) (tau p q k) (ip x i j))
            - C.psi (tau p q i) (tau p q j) (tau p q i) (ip x i j)
            - C.psi (tau p q i) (tau p q j) (tau p q j) (ip x i j) :=
        sum_ne_ne hij (fun k => C.psi (tau p q i) (tau p q j) (tau p q k) (ip x i j))
      have ht : (∑ k, C.psi (tau p q i) (tau p q j) (tau p q k) (ip x i j))
          = 2 * C.psi (tau p q i) (tau p q j) 0 (ip x i j)
            + ((C.N : ℝ) - 2) * C.psi (tau p q i) (tau p q j) 1 (ip x i j) := by
        have h := sum_tau p q hpq (fun c => C.psi (tau p q i) (tau p q j) c (ip x i j))
        rw [hcard] at h
        exact h
      rw [hs, ht]
      rfl)
  have hG := typed_pairs p q hpq (ip x) hsym C.pairG (3 * (C.cM : ℝ) * (C.fS : ℝ) / (C.c1 : ℝ))
    (fun s => 1 / Real.sqrt (2 - 2 * s)) (((C.k00p : ℝ) - C.k00n) / (C.c1 : ℝ))
    (((C.k01p : ℝ) - C.k01n) / (C.c1 : ℝ)) (((C.k11p : ℝ) - C.k11n) / (C.c1 : ℝ)) (C.pairG_00 hC) (C.pairG_11 hC)
    (C.pairG_01 hC)
  rw [hcard] at hG
  have hK : (∑ i, Kf C.P C.blk (tau p q i) (tau p q i) (tau p q i) 1 1 1)
      = 2 * C.K0 0 0 1 1 1 + ((C.N : ℝ) - 2) * C.K1 1 1 1 1 1 := by
    have h := sum_tau p q hpq (fun r => Kf C.P C.blk r r r 1 1 1)
    rw [hcard] at h
    rw [h, Kf_zero, Kf_one]
  rw [hG, hK] at main
  refine main.trans (le_of_eq ?_)
  ring

/-- The value of a kernel at `(1, 1, 1)` from the two numbers that the kernel computes at this point. -/
theorem kernZ_one (P : ThreePoint.Params) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb) (sel : ℕ) (blocks : List Blk)
    (z1 z2 : ℕ) (hz : kern P ⟨0, 0, 0⟩ sel blocks = (z1, z2)) :
    evR 1 1 1 (kernZ P sel blocks) = (z1 : ℝ) - z2 := by
  have h := kern_zero P sel blocks
  rw [hz] at h
  have h1 : z1 = csum (kernP P sel blocks).1 := congrArg Prod.fst h
  have h2 : z2 = csum (kernP P sel blocks).2 := congrArg Prod.snd h
  rw [← val_kernP P heb hcb, ← evN_sub, UCert.evN_one, UCert.evN_one, h1, h2]

/-- **The bound for the energy.** With the numbers of the two kernels at `(1, 1, 1)` and a rational number
`en / ed` that satisfies the equation of the constants (an equation between natural numbers), the energy of `N`
points of the unit sphere is at least `en / ed` plus a multiple of the sum of the slacks, for every choice of the
two points of the type `0`. -/
theorem energy_ge (C : TCert) (hC : C.Ok) (a1 a2 b1 b2 en ed : ℕ)
    (hz0 : kern C.P ⟨0, 0, 0⟩ 0 C.blocks0 = (a1, a2)) (hz1 : kern C.P ⟨0, 0, 0⟩ 2 C.blocks1 = (b1, b2))
    (hed : 0 < ed) (hfS : 0 < C.fS)
    (hconst : en * (6 * C.cM * C.fS)
        + (2 * C.k00p + 2 * (C.N - 2) * C.k01p + (C.N - 2) * (C.N - 3) * C.k11p
          + 6 * C.c1 * C.cK * (2 * a1 + (C.N - 2) * b1)) * ed
      = (2 * C.k00n + 2 * (C.N - 2) * C.k01n + (C.N - 2) * (C.N - 3) * C.k11n
          + 6 * C.c1 * C.cK * (2 * a2 + (C.N - 2) * b2)) * ed)
    (x : Fin C.N → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1) (p q : Fin C.N) (hpq : p ≠ q) :
    (en : ℝ) / ed + (C.c1 : ℝ) * dsum (slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x)
        / (6 * (C.cM : ℝ) * (C.fS : ℝ))
      ≤ ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / dist (x i) (x j) := by
  have h := C.energy hC x hx p q hpq
  have F := facts1_of_ok hC.h00
  have hk0 : C.K0 0 0 1 1 1 = (a1 : ℝ) - a2 := by
    rw [← C.evR_kern0 hC C.P ⟨rfl, rfl⟩ 0 0 (by norm_num)]
    exact kernZ_one C.P F.heb F.hcb 0 C.blocks0 a1 a2 hz0
  have hk1 : C.K1 1 1 1 1 1 = (b1 : ℝ) - b2 := by
    rw [← C.evR_kern1 hC C.P ⟨rfl, rfl⟩ 1 1 (by norm_num)]
    exact kernZ_one C.P F.heb F.hcb 2 C.blocks1 b1 b2 hz1
  rw [hk0, hk1] at h
  -- the pairs
  have hpair : (∑ i, ∑ j, if i ≠ j then 1 / Real.sqrt (2 - 2 * ip x i j) else 0)
      = 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / dist (x i) (x j) := by
    have h4 := CAP.ThreePoint.sum_ne_eq_two_mul_sum_lt (fun i j => 1 / dist (x i) (x j))
      (fun i j => by rw [dist_comm])
    rw [← h4]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [UCert.dist_sphere x hx]
  rw [hpair] at h
  -- the constants as real numbers
  have hN := hC.hN
  have hN2 : ((C.N - 2 : ℕ) : ℝ) = (C.N : ℝ) - 2 := by exact_mod_cast cast_sub_of_le (by omega : 2 ≤ C.N)
  have hN3 : ((C.N - 3 : ℕ) : ℝ) = (C.N : ℝ) - 3 := by exact_mod_cast cast_sub_of_le (by omega : 3 ≤ C.N)
  have hc := congrArg (Nat.cast (R := ℝ)) hconst
  push_cast at hc
  rw [hN2, hN3] at hc
  have hc1 : (0 : ℝ) < C.c1 := by exact_mod_cast hC.hc1
  have hcM : (0 : ℝ) < C.cM := by exact_mod_cast hC.hcM
  have hfS' : (0 : ℝ) < C.fS := by exact_mod_cast hfS
  have hed' : (0 : ℝ) < ed := by exact_mod_cast hed
  set D := dsum (slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x) with hD
  set E := ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / dist (x i) (x j) with hE
  -- the bound multiplied by `c1`
  have key : (C.c1 : ℝ) * D
      ≤ 6 * (C.cM : ℝ) * (C.fS : ℝ) * E
        + (2 * ((C.k00p : ℝ) - C.k00n) + 2 * ((C.N : ℝ) - 2) * ((C.k01p : ℝ) - C.k01n)
          + ((C.N : ℝ) - 2) * ((C.N : ℝ) - 3) * ((C.k11p : ℝ) - C.k11n))
        + 6 * (C.c1 : ℝ) * (C.cK : ℝ) * (2 * ((a1 : ℝ) - a2) + ((C.N : ℝ) - 2) * ((b1 : ℝ) - b2)) := by
    have h' := mul_le_mul_of_nonneg_left h hc1.le
    have e : (C.c1 : ℝ) * (3 * (C.cM : ℝ) * (C.fS : ℝ) / (C.c1 : ℝ) * (2 * E)
          + (2 * ((C.k00p : ℝ) - C.k00n) + 2 * ((C.N : ℝ) - 2) * ((C.k01p : ℝ) - C.k01n)
            + ((C.N : ℝ) - 2) * ((C.N : ℝ) - 3) * ((C.k11p : ℝ) - C.k11n)) / (C.c1 : ℝ)
          + 6 * (C.cK : ℝ) * (2 * ((a1 : ℝ) - a2) + ((C.N : ℝ) - 2) * ((b1 : ℝ) - b2)))
        = 6 * (C.cM : ℝ) * (C.fS : ℝ) * E
          + (2 * ((C.k00p : ℝ) - C.k00n) + 2 * ((C.N : ℝ) - 2) * ((C.k01p : ℝ) - C.k01n)
            + ((C.N : ℝ) - 2) * ((C.N : ℝ) - 3) * ((C.k11p : ℝ) - C.k11n))
          + 6 * (C.c1 : ℝ) * (C.cK : ℝ) * (2 * ((a1 : ℝ) - a2) + ((C.N : ℝ) - 2) * ((b1 : ℝ) - b2)) := by
      field_simp
      ring
    rw [e] at h'
    exact h'
  have hpos : (0 : ℝ) < 6 * (C.cM : ℝ) * (C.fS : ℝ) * ed := by positivity
  have e2 : (en : ℝ) / ed + (C.c1 : ℝ) * D / (6 * (C.cM : ℝ) * (C.fS : ℝ))
      = ((en : ℝ) * (6 * (C.cM : ℝ) * (C.fS : ℝ)) + (C.c1 : ℝ) * D * ed) / (6 * (C.cM : ℝ) * (C.fS : ℝ) * ed) := by
    field_simp
  rw [e2, div_le_iff₀ hpos]
  have key2 := mul_le_mul_of_nonneg_right key hed'.le
  linarith

end TCert

end N14.Energy

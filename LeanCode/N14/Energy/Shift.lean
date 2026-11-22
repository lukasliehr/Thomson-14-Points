module

public import N14.Energy.Typed

/-!
# T7, a further run of a pattern of a certificate

A certificate with the types P/R has one run for each pattern. The runs of the nodes (statement 5: outside the
inner ball, between the tube and the inner ball, in the tube) are further runs of the same slack with another
threshold and another domain. `TCert.shift`: if the kernel accepts the identity of a further run with the kernels
of its pattern (`id3Ok`), its tables are the functions of the tables of the run of the certificate and its
polynomials of one variable are the same numbers, then

  `cM * (slack function of the further run) = cM * (slack function of the run of the certificate) + δ`

with the difference `δ` of the constants of the two identities. So Lean itself says that every run of a pattern
bounds the same slack function, shifted by a threshold.
-/

@[expose] public section

namespace N14.Energy

open CAP CAP.ThreePoint N14.Box N14.Ident Finset

/-- The kernels of a list of terms depend on the parameters only through the layout of the matrices. -/
theorem termsR_congr (P P' : ThreePoint.Params) (hw : P'.w = P.w) (ha : P'.a = P.a) (u v t : ℝ) :
    ∀ l : List Term, termsR P' l u v t = termsR P l u v t
  | [] => rfl
  | T :: l => by
    show termR P' T u v t + termsR P' l u v t = termR P T u v t + termsR P l u v t
    rw [termsR_congr P P' hw ha u v t l]
    unfold termR kernZ
    rw [kernZFrom_congr P P' hw ha]

namespace TCert

/-- **The slack function of a further run of a pattern.** `T0` is the run of the certificate, `T` the further
run, `terms` the kernels of the pattern. -/
theorem shift (C : TCert) (T0 T : TRun) (terms : List Term)
    (h0 : id3Ok T0.P (C.id3 T0 terms) = true) (h : id3Ok T.P (C.id3 T terms) = true)
    (hW0 : T0.P.W = T0.R.V) (hW : T.P.W = T.R.V) (hw : T.P.w = T0.P.w) (ha : T.P.a = T0.P.a)
    (hn : T.R.n = T0.R.n) (hT1 : ∀ s, tabFn T.U1 s = tabFn T0.U1 s) (hT2 : ∀ s, tabFn T.U2 s = tabFn T0.U2 s)
    (hT3 : ∀ s, tabFn T.U3 s = tabFn T0.U3 s) (hB0 : T.B0 = T0.B0) (hB1 : T.B1 = T0.B1) (hB2 : T.B2 = T0.B2)
    (u v t : ℝ) :
    (C.cM : ℝ) * T.lam u v t
      = (C.cM : ℝ) * T0.lam u v t + ((((T.cp : ℝ) - T.cn)) - ((T0.cp : ℝ) - T0.cn)) := by
  have h1 := slack_id3 T0.P T0.R T0.U1 T0.U2 T0.U3 (C.id3 T0 terms) h0 hW0 rfl rfl rfl u v t
  have h2 := slack_id3 T.P T.R T.U1 T.U2 T.U3 (C.id3 T terms) h hW rfl rfl rfl u v t
  have ht : termsR T.P (C.id3 T terms).terms u v t = termsR T0.P (C.id3 T0 terms).terms u v t :=
    termsR_congr T0.P T.P hw ha u v t terms
  have e : ∀ (U U0 : Tab) (B B0 : ℕ) (s : ℝ), (∀ x, tabFn U x = tabFn U0 x) → B = B0 →
      psiOf C.cM C.wB C.aB T.R.n U B T.cp T.cn s
        = psiOf C.cM C.wB C.aB T0.R.n U0 B0 T0.cp T0.cn s
          + ((((T.cp : ℝ) - T.cn)) - ((T0.cp : ℝ) - T0.cn)) / 3 := by
    intro U U0 B B0 s hU hB
    unfold psiOf
    rw [hU, hB, hn]
    ring
  have e1 := e T.U1 T0.U1 T.B0 T0.B0 u hT1 hB0
  have e2 := e T.U2 T0.U2 T.B1 T0.B1 v hT2 hB1
  have e3 := e T.U3 T0.U3 T.B2 T0.B2 t hT3 hB2
  have h1' : (C.cM : ℝ) * T0.lam u v t
      = psiOf C.cM C.wB C.aB T0.R.n T0.U1 T0.B0 T0.cp T0.cn u
        + psiOf C.cM C.wB C.aB T0.R.n T0.U2 T0.B1 T0.cp T0.cn v
        + psiOf C.cM C.wB C.aB T0.R.n T0.U3 T0.B2 T0.cp T0.cn t
        - (C.cK : ℝ) * termsR T0.P (C.id3 T0 terms).terms u v t := h1
  have h2' : (C.cM : ℝ) * T.lam u v t
      = psiOf C.cM C.wB C.aB T.R.n T.U1 T.B0 T.cp T.cn u + psiOf C.cM C.wB C.aB T.R.n T.U2 T.B1 T.cp T.cn v
        + psiOf C.cM C.wB C.aB T.R.n T.U3 T.B2 T.cp T.cn t
        - (C.cK : ℝ) * termsR T.P (C.id3 T terms).terms u v t := h2
  rw [h2', h1', e1, e2, e3, ht]
  ring

/-- The same with the difference of the constants as `cM` times a natural number `D`: the slack function of the
further run is that of the run of the certificate plus `D`. The equation between the constants is one between
natural numbers. -/
theorem shift_nat (C : TCert) (T0 T : TRun) (terms : List Term)
    (h0 : id3Ok T0.P (C.id3 T0 terms) = true) (h : id3Ok T.P (C.id3 T terms) = true)
    (hW0 : T0.P.W = T0.R.V) (hW : T.P.W = T.R.V) (hw : T.P.w = T0.P.w) (ha : T.P.a = T0.P.a)
    (hn : T.R.n = T0.R.n) (hT1 : ∀ s, tabFn T.U1 s = tabFn T0.U1 s) (hT2 : ∀ s, tabFn T.U2 s = tabFn T0.U2 s)
    (hT3 : ∀ s, tabFn T.U3 s = tabFn T0.U3 s) (hB0 : T.B0 = T0.B0) (hB1 : T.B1 = T0.B1) (hB2 : T.B2 = T0.B2)
    (hcM : 0 < C.cM) (D : ℕ) (hD : T.cp + T0.cn = T0.cp + T.cn + C.cM * D) (u v t : ℝ) :
    T.lam u v t = T0.lam u v t + D := by
  have hs := C.shift T0 T terms h0 h hW0 hW hw ha hn hT1 hT2 hT3 hB0 hB1 hB2 u v t
  have hc : ((T.cp : ℝ) - T.cn) - ((T0.cp : ℝ) - T0.cn) = (C.cM : ℝ) * D := by
    have h2 := congrArg (Nat.cast (R := ℝ)) hD
    push_cast at h2
    linarith
  have hpos : (C.cM : ℝ) ≠ 0 := by exact_mod_cast hcM.ne'
  have e : (C.cM : ℝ) * T.lam u v t = (C.cM : ℝ) * (T0.lam u v t + D) := by
    rw [hs, hc]
    ring
  exact mul_left_cancel₀ hpos e

end TCert

end N14.Energy

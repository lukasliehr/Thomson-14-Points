module

public import N14.Box.Cover
public import N14.Ident.Sound1
public import N14.Energy.Schema

/-!
# T7, the slack of a run and the identities of a certificate

The two checkers of `N14.Ident` speak about polynomials of numbers; the theorem of a run (`N14.Box`) speaks about
the function `slackFn` of the same numbers. This file joins them.

* `mixR_eq_pEval`: the polynomial of the identity of a run is the polynomial of `slackFn`.
* `psiOf`: the function of one variable of a slot of a run with the factors of the identity,
  `cM * tabFn U + B + (cp - cn) / 3`.
* **`slack_id3`**: if the checker accepts the identity of a run, then

    `cM * slackFn R U₁ U₂ U₃ (u, v, t) = ψ₁ (u) + ψ₂ (v) + ψ₃ (t) - cK * ∑ terms (u, v, t)`

  at all real points. So Lean itself says that the function of `slack_nonneg` is the slack of the certificate:
  its functions of one variable minus the kernels.
* **`pair_id1`**: if the checker accepts the identity of a pair for the shares of a list of slots, then for
  `s < 1`

    `3 * ∑ m_c * ψ_c (s) + 6 * cK * ∑ terms (s) = (3 * cM * fS / c1) * (2 - 2 s) ^ (-1/2) + (kp - kn) / c1`.
-/

@[expose] public section

namespace N14.Energy

open CAP CAP.ThreePoint CAP.Bernstein N14.Box N14.Ident Finset

/-- The polynomial of the identity of a run is the polynomial of the mixed part of the run. -/
theorem mixR_eq_pEval (R : Run) (u v t : ℝ) :
    mixR R.V R.n R.aH R.PpM u v t = pEval (boxP R R.aH R.A 0 0 0) R.PpM u v t := by
  unfold mixR pEval
  refine sum_congr rfl fun e3 _ => sum_congr rfl fun e2 _ => sum_congr rfl fun e1 _ => ?_
  unfold coef
  show (((slot R.V R.PpM (e1 + (R.n + 1) * (e2 + (R.n + 1) * e3)) : ℕ) : ℝ) - 2 ^ (R.aH - 1))
      * (u ^ e1 * v ^ e2 * t ^ e3)
    = (((slot R.V R.PpM (e1 + (R.n + 1) * (e2 + (R.n + 1) * e3)) : ℤ) - 2 ^ (R.aH - 1) : ℤ) : ℝ)
      * u ^ e1 * v ^ e2 * t ^ e3
  push_cast
  ring

/-- The function of one variable of a slot of a run with the factors of the identity. -/
noncomputable def psiOf (cM wB aB n : ℕ) (U : Tab) (B cp cn : ℕ) (s : ℝ) : ℝ :=
  (cM : ℝ) * tabFn U s + uniR wB aB n B s + ((cp : ℝ) - cn) / 3

/-- **The slack of a run is its functions of one variable minus the kernels.** -/
theorem slack_id3 (P : ThreePoint.Params) (R : Run) (U1 U2 U3 : Tab) (I : Id3) (h : id3Ok P I = true)
    (hW : P.W = R.V) (hn : I.n = R.n) (haH : I.aH = R.aH) (hM : I.PpM = R.PpM) (u v t : ℝ) :
    (I.cM : ℝ) * slackFn R U1 U2 U3 u v t
      = psiOf I.cM I.wB I.aB I.n U1 I.B0 I.cp I.cn u + psiOf I.cM I.wB I.aB I.n U2 I.B1 I.cp I.cn v
        + psiOf I.cM I.wB I.aB I.n U3 I.B2 I.cp I.cn t - (I.cK : ℝ) * termsR P I.terms u v t := by
  have hs := id3_sound P I h u v t
  rw [hW, hn, haH, hM, mixR_eq_pEval] at hs
  unfold slackFn psiOf
  rw [hn]
  linear_combination hs

/-- Two tables with the same numbers have the same function. -/
theorem tabFn_congr (U U' : Tab) (hDn : U.Dn = U'.Dn) (hK : U.K = U'.K) (hc : U.c1 = U'.c1)
    (hW : U.P.W = U'.P.W) (haH : U.P.aH = U'.P.aH) (hD : U.P.D = U'.P.D) (s : ℝ) : tabFn U s = tabFn U' s := by
  unfold tabFn CAP.UniPos.hEval CAP.UniPos.coefZ
  rw [hDn, hK, hc, hW, haH, hD]

/-- A slot of a run in the identity of a pair: its multiplicity, its table, its polynomial of one variable and
the constant of its run. -/
structure Slot where
  mult : ℕ
  U : Tab
  B : ℕ
  cp : ℕ
  cn : ℕ

/-- The share of a slot. -/
def Slot.share (S : Slot) : Share := ⟨S.mult, S.U.P.W, S.U.P.aH, S.U.P.D, S.U.K, S.U.Dn, S.B, S.cp, S.cn⟩

/-- The polynomial of the share of a slot is the polynomial `Ĥ` of its table. -/
theorem hR_share (S : Slot) (s : ℝ) : hR S.share s = CAP.UniPos.hEval S.U.P S.U.K s := by
  unfold hR CAP.UniPos.hEval CAP.UniPos.coefZ Slot.share
  refine sum_congr rfl fun d _ => ?_
  push_cast
  ring

/-- The sum of the functions of the slots with their multiplicities. -/
noncomputable def slotsR (cM wB aB n : ℕ) : List Slot → ℝ → ℝ
  | [], _ => 0
  | S :: l, s => (S.mult : ℝ) * psiOf cM wB aB n S.U S.B S.cp S.cn s + slotsR cM wB aB n l s

theorem slots_shares (I : Id1) (hc1 : 0 < I.c1) (s : ℝ) : ∀ l : List Slot, (∀ S ∈ l, S.U.c1 = I.c1) →
    3 * (I.c1 : ℝ) * slotsR I.cM I.wB I.aB I.n l s
      = 3 * (I.cM : ℝ) * (sharesDn (l.map Slot.share) : ℝ) / Real.sqrt (2 - 2 * s)
        + sharesR I (l.map Slot.share) s
  | [], _ => by simp [slotsR, sharesDn, sharesR]
  | S :: l, h => by
    have ih := slots_shares I hc1 s l (fun S' hS' => h S' (List.mem_cons_of_mem _ hS'))
    have hS := h S List.mem_cons_self
    have hc : (I.c1 : ℝ) ≠ 0 := by exact_mod_cast hc1.ne'
    have e : (I.c1 : ℝ) * tabFn S.U s = (S.U.Dn : ℝ) / Real.sqrt (2 - 2 * s) - CAP.UniPos.hEval S.U.P S.U.K s := by
      unfold tabFn
      rw [hS]
      field_simp
    simp only [List.map_cons, slotsR, sharesDn, sharesR]
    rw [hR_share]
    have e2 : (S.share).mult = S.mult := rfl
    have e3 : (S.share).Dn = S.U.Dn := rfl
    have e4 : (S.share).B = S.B := rfl
    have e5 : (S.share).cp = S.cp := rfl
    have e6 : (S.share).cn = S.cn := rfl
    rw [e2, e3, e4, e5, e6]
    unfold psiOf
    push_cast
    have e7 : 3 * (I.c1 : ℝ) * ((S.mult : ℝ) * ((I.cM : ℝ) * tabFn S.U s + uniR I.wB I.aB I.n S.B s
          + ((S.cp : ℝ) - S.cn) / 3))
        = 3 * (S.mult : ℝ) * ((I.cM : ℝ) * ((I.c1 : ℝ) * tabFn S.U s) + (I.c1 : ℝ) * uniR I.wB I.aB I.n S.B s)
          + (S.mult : ℝ) * ((I.c1 : ℝ) * ((S.cp : ℝ) - S.cn)) := by ring
    rw [mul_add, e7, e, ih]
    ring

/-- **The identity of a pair for the functions of the slots.** -/
theorem pair_id1 (P : ThreePoint.Params) (I : Id1) (slots : List Slot) (hsh : I.shares = slots.map Slot.share)
    (hU : ∀ S ∈ slots, S.U.c1 = I.c1) (hc1 : 0 < I.c1) (h : id1Ok P I = true) (s : ℝ) :
    3 * slotsR I.cM I.wB I.aB I.n slots s + 6 * (I.cK : ℝ) * dtermsR P I.terms s
      = 3 * (I.cM : ℝ) * (I.fS : ℝ) / (I.c1 : ℝ) / Real.sqrt (2 - 2 * s) + ((I.kp : ℝ) - I.kn) / (I.c1 : ℝ) := by
  have h1 := id1_sound P I h s
  have h2 := id1_dn P I h
  rw [hsh] at h1 h2
  have h3 := slots_shares I hc1 s slots hU
  rw [h2] at h3
  have hc : (I.c1 : ℝ) ≠ 0 := by exact_mod_cast hc1.ne'
  have key : (3 * slotsR I.cM I.wB I.aB I.n slots s + 6 * (I.cK : ℝ) * dtermsR P I.terms s) * (I.c1 : ℝ)
      = 3 * (I.cM : ℝ) * (I.fS : ℝ) / Real.sqrt (2 - 2 * s) + ((I.kp : ℝ) - I.kn) := by
    linear_combination h3 + h1
  have e : 3 * (I.cM : ℝ) * (I.fS : ℝ) / (I.c1 : ℝ) / Real.sqrt (2 - 2 * s) + ((I.kp : ℝ) - I.kn) / (I.c1 : ℝ)
      = (3 * (I.cM : ℝ) * (I.fS : ℝ) / Real.sqrt (2 - 2 * s) + ((I.kp : ℝ) - I.kn)) / (I.c1 : ℝ) := by ring
  rw [e, eq_div_iff hc]
  exact key

end N14.Energy

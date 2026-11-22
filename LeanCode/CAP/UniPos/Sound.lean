module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import CAP.UniPos.Packed

/-!
# E3, the minorant condition: soundness of the checker

**Theorem** (`CAP.UniPos.check_sound`). If `CAP.UniPos.check P Hp Dn cuts = true`, then

  `Ĥ(t) ≤ Dn / √(2 - 2 * t)`  for all real `t` with `-1 ≤ t < 1`,

where `Ĥ(t) = hEval P Hp t = ∑ d ≤ 2 * D, coefZ P Hp d * t ^ d` and `coefZ P Hp d` is slot `d` of
`Hp` minus the bias.

The proof follows the checker.

1. The numbers of the checker are the values at `2 ^ V` of polynomials in `y` with natural
   coefficients (`hornerGo_eq`, `bern_eq`); for `V = 0` these are the sums of the coefficients.
2. Hence the test `geTest` compares the coefficients of the two parts of `B` (`geTest_sound`,
   `intervalOk_coeff`), and `B(y) ≥ 0` for real `y ≥ 0` (`interval_real`).
3. For `t` in a piece, `y` is chosen such that `t = (L2 - M) / L2`; then `B(y) ≥ 0` is the
   inequality `(2 - 2 * t) * Ĥ(t) ^ 2 ≤ Dn ^ 2` (`interval_bound`).
4. The pieces cover `[-1, 1)` (`cutsGo_cover`).
-/

@[expose] public section

namespace CAP.UniPos

open Polynomial Finset

/-! ## The linear forms and Horner's rule -/

/-- The linear form `2 ^ s * (1 + y)`. -/
noncomputable def L2 (s : ℕ) : ℕ[X] := C (2 ^ s) * (1 + X)

/-- The linear form `lk + lk1 * y`. -/
noncomputable def Mf (lk lk1 : ℕ) : ℕ[X] := C lk + C lk1 * X

theorem mulL2_eval (V s : ℕ) (F : ℕ[X]) : mulL2 V s (F.eval (2 ^ V)) = (F * L2 s).eval (2 ^ V) := by
  show (F.eval (2 ^ V) + F.eval (2 ^ V) <<< V) <<< s = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  simp only [L2, eval_mul, eval_C, eval_add, eval_one, eval_X]
  ring

theorem mulM_eval (V lk lk1 : ℕ) (F : ℕ[X]) :
    mulM V lk lk1 (F.eval (2 ^ V)) = (F * Mf lk lk1).eval (2 ^ V) := by
  show lk * F.eval (2 ^ V) + lk1 * (F.eval (2 ^ V) <<< V) = _
  rw [Nat.shiftLeft_eq]
  simp only [Mf, eval_mul, eval_C, eval_add, eval_X]
  ring

/-! ## Horner's rule -/

/-- The state of Horner's rule as polynomials: with `k` coefficients left. -/
noncomputable def hornerP (P : Params) (Hp lk lk1 : ℕ) : ℕ → ℕ[X] → ℕ[X] → ℕ[X] → ℕ[X] × ℕ[X]
  | 0, Sp, Sn, _ => (Sp, Sn)
  | k + 1, Sp, Sn, Pw =>
    hornerP P Hp lk lk1 k (Sp * L2 P.s + Sn * Mf lk lk1 + C (slot P.W Hp k) * Pw)
      (Sn * L2 P.s + Sp * Mf lk lk1 + C (2 ^ (P.aH - 1)) * Pw) (Pw * L2 P.s)

theorem hornerGo_succ (P : Params) (V Hp lk lk1 k Sp Sn Pw : ℕ) :
    hornerGo P V Hp lk lk1 (k + 1) Sp Sn Pw =
      hornerGo P V Hp lk lk1 k (mulL2 V P.s Sp + mulM V lk lk1 Sn + slot P.W Hp k * Pw)
        (mulL2 V P.s Sn + mulM V lk lk1 Sp + 2 ^ (P.aH - 1) * Pw) (mulL2 V P.s Pw) := by
  rw [← Nat.one_shiftLeft]
  rfl

theorem hornerGo_eq (P : Params) (V Hp lk lk1 : ℕ) : ∀ (k : ℕ) (Sp Sn Pw : ℕ[X]),
    hornerGo P V Hp lk lk1 k (Sp.eval (2 ^ V)) (Sn.eval (2 ^ V)) (Pw.eval (2 ^ V)) =
      ((hornerP P Hp lk lk1 k Sp Sn Pw).1.eval (2 ^ V), (hornerP P Hp lk lk1 k Sp Sn Pw).2.eval (2 ^ V))
  | 0, _, _, _ => rfl
  | k + 1, Sp, Sn, Pw => by
    have e1 : (Sp * L2 P.s).eval (2 ^ V) + (Sn * Mf lk lk1).eval (2 ^ V) + slot P.W Hp k * Pw.eval (2 ^ V)
        = (Sp * L2 P.s + Sn * Mf lk lk1 + C (slot P.W Hp k) * Pw).eval (2 ^ V) := by
      simp only [eval_add, eval_mul, eval_C]
    have e2 : (Sn * L2 P.s).eval (2 ^ V) + (Sp * Mf lk lk1).eval (2 ^ V) + 2 ^ (P.aH - 1) * Pw.eval (2 ^ V)
        = (Sn * L2 P.s + Sp * Mf lk lk1 + C (2 ^ (P.aH - 1)) * Pw).eval (2 ^ V) := by
      simp only [eval_add, eval_mul, eval_C]
    rw [hornerGo_succ, mulL2_eval, mulL2_eval, mulL2_eval, mulM_eval, mulM_eval, e1, e2, hornerP]
    exact hornerGo_eq P V Hp lk lk1 k _ _ _

/-- The pair of `Hb = ∑ d, Hh d * (L2 - M) ^ d * L2 ^ (2 * D - d)`. -/
noncomputable def hbP (P : Params) (Hp lk lk1 : ℕ) : ℕ[X] × ℕ[X] :=
  hornerP P Hp lk lk1 (2 * P.D + 1) 0 0 1

theorem hornerGo_top (P : Params) (V Hp lk lk1 : ℕ) :
    hornerGo P V Hp lk lk1 (2 * P.D + 1) 0 0 1 =
      ((hbP P Hp lk lk1).1.eval (2 ^ V), (hbP P Hp lk lk1).2.eval (2 ^ V)) := by
  have h := hornerGo_eq P V Hp lk lk1 (2 * P.D + 1) 0 0 1
  rw [eval_zero, eval_one] at h
  exact h

theorem powL2_eq (V s : ℕ) : ∀ cnt, powL2 V s cnt = ((L2 s) ^ cnt).eval (2 ^ V)
  | 0 => by
    show (1 : ℕ) = _
    simp
  | cnt + 1 => by
    have h : powL2 V s (cnt + 1) = mulL2 V s (powL2 V s cnt) := rfl
    rw [h, powL2_eq V s cnt, mulL2_eval, pow_succ]

/-- The pair of `B = Dn ^ 2 * L2 ^ (4 * D + 1) - 2 * M * Hb ^ 2`. -/
noncomputable def bernP (P : Params) (Hp Dn lk lk1 : ℕ) : ℕ[X] × ℕ[X] :=
  (C (Dn * Dn) * (L2 P.s) ^ (4 * P.D + 1)
      + 2 * ((2 * ((hbP P Hp lk lk1).1 * (hbP P Hp lk lk1).2)) * Mf lk lk1),
    2 * (((hbP P Hp lk lk1).1 * (hbP P Hp lk lk1).1 + (hbP P Hp lk lk1).2 * (hbP P Hp lk lk1).2)
      * Mf lk lk1))

theorem bern_eq (P : Params) (V Hp Dn lk lk1 : ℕ) :
    bern P V Hp Dn lk lk1 =
      ((bernP P Hp Dn lk lk1).1.eval (2 ^ V), (bernP P Hp Dn lk lk1).2.eval (2 ^ V)) := by
  have h : bern P V Hp Dn lk lk1 =
      (Dn * Dn * powL2 V P.s (4 * P.D + 1)
        + 2 * mulM V lk lk1 (2 * ((hornerGo P V Hp lk lk1 (2 * P.D + 1) 0 0 1).1
          * (hornerGo P V Hp lk lk1 (2 * P.D + 1) 0 0 1).2)),
       2 * mulM V lk lk1 ((hornerGo P V Hp lk lk1 (2 * P.D + 1) 0 0 1).1
          * (hornerGo P V Hp lk lk1 (2 * P.D + 1) 0 0 1).1
        + (hornerGo P V Hp lk lk1 (2 * P.D + 1) 0 0 1).2
          * (hornerGo P V Hp lk lk1 (2 * P.D + 1) 0 0 1).2)) := rfl
  have e1 : 2 * ((hbP P Hp lk lk1).1.eval (2 ^ V) * (hbP P Hp lk lk1).2.eval (2 ^ V))
      = (2 * ((hbP P Hp lk lk1).1 * (hbP P Hp lk lk1).2)).eval (2 ^ V) := by
    simp only [eval_mul, eval_ofNat]
  have e2 : (hbP P Hp lk lk1).1.eval (2 ^ V) * (hbP P Hp lk lk1).1.eval (2 ^ V)
      + (hbP P Hp lk lk1).2.eval (2 ^ V) * (hbP P Hp lk lk1).2.eval (2 ^ V)
      = ((hbP P Hp lk lk1).1 * (hbP P Hp lk lk1).1 + (hbP P Hp lk lk1).2 * (hbP P Hp lk lk1).2).eval (2 ^ V) := by
    simp only [eval_add, eval_mul]
  rw [h, hornerGo_top, powL2_eq, e1, e2, mulM_eval, mulM_eval]
  simp only [bernP, eval_add, eval_mul, eval_C, eval_ofNat]

/-! ## Degrees -/

theorem natDegree_L2 (s : ℕ) : (L2 s).natDegree ≤ 1 := by
  refine (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans ?_)
  rw [natDegree_one]
  exact max_le (Nat.zero_le 1) natDegree_X_le

theorem natDegree_Mf (lk lk1 : ℕ) : (Mf lk lk1).natDegree ≤ 1 := by
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · rw [natDegree_C]
    exact Nat.zero_le 1
  · exact (natDegree_C_mul_le _ _).trans natDegree_X_le

theorem natDegree_mul_lin {F L : ℕ[X]} {j : ℕ} (hF : F.natDegree ≤ j) (hL : L.natDegree ≤ 1) :
    (F * L).natDegree ≤ j + 1 :=
  natDegree_mul_le.trans (add_le_add hF hL)

theorem natDegree_two_mul_le (F : ℕ[X]) : (2 * F).natDegree ≤ F.natDegree := by
  rw [two_mul]
  exact (natDegree_add_le _ _).trans (max_le le_rfl le_rfl)

theorem natDegree_hornerP (P : Params) (Hp lk lk1 : ℕ) : ∀ (k j : ℕ) (Sp Sn Pw : ℕ[X]),
    Sp.natDegree ≤ j → Sn.natDegree ≤ j → Pw.natDegree ≤ j →
    (hornerP P Hp lk lk1 k Sp Sn Pw).1.natDegree ≤ j + k ∧
      (hornerP P Hp lk lk1 k Sp Sn Pw).2.natDegree ≤ j + k
  | 0, j, Sp, Sn, _, h1, h2, _ => ⟨h1, h2⟩
  | k + 1, j, Sp, Sn, Pw, h1, h2, h3 => by
    have hc : ∀ c : ℕ, (C c * Pw).natDegree ≤ j + 1 := fun c =>
      (natDegree_C_mul_le _ _).trans (h3.trans (Nat.le_succ j))
    have a1 : (Sp * L2 P.s + Sn * Mf lk lk1 + C (slot P.W Hp k) * Pw).natDegree ≤ j + 1 :=
      (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans
        (max_le (natDegree_mul_lin h1 (natDegree_L2 _)) (natDegree_mul_lin h2 (natDegree_Mf _ _)))) (hc _))
    have a2 : (Sn * L2 P.s + Sp * Mf lk lk1 + C (2 ^ (P.aH - 1)) * Pw).natDegree ≤ j + 1 :=
      (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans
        (max_le (natDegree_mul_lin h2 (natDegree_L2 _)) (natDegree_mul_lin h1 (natDegree_Mf _ _)))) (hc _))
    have a3 : (Pw * L2 P.s).natDegree ≤ j + 1 := natDegree_mul_lin h3 (natDegree_L2 _)
    have h := natDegree_hornerP P Hp lk lk1 k (j + 1) _ _ _ a1 a2 a3
    have e : j + 1 + k = j + (k + 1) := by ring
    rw [e] at h
    rw [hornerP]
    exact h

theorem natDegree_hbP (P : Params) (Hp lk lk1 : ℕ) :
    (hbP P Hp lk lk1).1.natDegree ≤ 2 * P.D + 1 ∧ (hbP P Hp lk lk1).2.natDegree ≤ 2 * P.D + 1 := by
  have h := natDegree_hornerP P Hp lk lk1 (2 * P.D + 1) 0 0 0 1 (by simp) (by simp) (by simp)
  rw [zero_add] at h
  exact h

theorem natDegree_bernP (P : Params) (Hp Dn lk lk1 : ℕ) :
    (bernP P Hp Dn lk lk1).1.natDegree < 4 * P.D + 4 ∧ (bernP P Hp Dn lk lk1).2.natDegree < 4 * P.D + 4 := by
  obtain ⟨h1, h2⟩ := natDegree_hbP P Hp lk lk1
  have hM := natDegree_Mf lk lk1
  have hprod : ∀ F G : ℕ[X], F.natDegree ≤ 2 * P.D + 1 → G.natDegree ≤ 2 * P.D + 1 →
      (F * G).natDegree ≤ 4 * P.D + 2 := fun F G hF hG =>
    natDegree_mul_le.trans (by omega)
  have hpow : (C (Dn * Dn) * (L2 P.s) ^ (4 * P.D + 1)).natDegree ≤ 4 * P.D + 1 := by
    refine (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans ?_)
    have := natDegree_L2 P.s
    nlinarith
  constructor
  · have a : ((2 * ((hbP P Hp lk lk1).1 * (hbP P Hp lk lk1).2)) * Mf lk lk1).natDegree ≤ 4 * P.D + 3 :=
      natDegree_mul_lin ((natDegree_two_mul_le _).trans (hprod _ _ h1 h2)) hM
    have b := (natDegree_add_le (C (Dn * Dn) * (L2 P.s) ^ (4 * P.D + 1))
      (2 * ((2 * ((hbP P Hp lk lk1).1 * (hbP P Hp lk lk1).2)) * Mf lk lk1))).trans
      (max_le (hpow.trans (by omega)) ((natDegree_two_mul_le _).trans a))
    exact Nat.lt_succ_of_le b
  · have a : (((hbP P Hp lk lk1).1 * (hbP P Hp lk lk1).1 + (hbP P Hp lk lk1).2 * (hbP P Hp lk lk1).2)
        * Mf lk lk1).natDegree ≤ 4 * P.D + 3 :=
      natDegree_mul_lin ((natDegree_add_le _ _).trans (max_le (hprod _ _ h1 h1) (hprod _ _ h2 h2))) hM
    exact Nat.lt_succ_of_le ((natDegree_two_mul_le _).trans a)

/-! ## The comparison of the coefficients -/

theorem intervalOk_coeff (P : Params) (Hp Dn lk lk1 : ℕ) (hV : 1 ≤ P.V)
    (h : intervalOk P Hp Dn lk lk1 = true) :
    ∀ i, (bernP P Hp Dn lk lk1).2.coeff i ≤ (bernP P Hp Dn lk lk1).1.coeff i := by
  have h0 : (Nat.blt (bern P 0 Hp Dn lk lk1).1 (1 <<< (P.V - 1))
      && Nat.blt (bern P 0 Hp Dn lk lk1).2 (1 <<< (P.V - 1))
      && geTest P.V (4 * P.D + 4) (bern P P.V Hp Dn lk lk1).1 (bern P P.V Hp Dn lk lk1).2) = true := h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, Nat.one_shiftLeft, bern_eq, bern_eq,
    pow_zero] at h0
  obtain ⟨⟨hb1, hb2⟩, hg⟩ := h0
  obtain ⟨d1, d2⟩ := natDegree_bernP P Hp Dn lk lk1
  have hg' : geTest P.V (4 * P.D + 4) (packSum P.V (4 * P.D + 4) (bernP P Hp Dn lk lk1).1.coeff)
      (packSum P.V (4 * P.D + 4) (bernP P Hp Dn lk lk1).2.coeff) = true := by
    rw [← eval_two_pow P.V _ _ d1, ← eval_two_pow P.V _ _ d2]
    exact hg
  have key := geTest_sound P.V (4 * P.D + 4) _ _ hV
    (fun i _ => lt_of_le_of_lt (coeff_le_eval_one _ i) hb1)
    (fun i _ => lt_of_le_of_lt (coeff_le_eval_one _ i) hb2) hg'
  intro i
  by_cases hi : i < 4 * P.D + 4
  · exact key i hi
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le d2 (not_lt.mp hi))]
    exact Nat.zero_le _

/-! ## Real values -/

/-- The value of a polynomial with natural coefficients at a real number. -/
noncomputable def rv (y : ℝ) : ℕ[X] →+* ℝ := eval₂RingHom (Nat.castRingHom ℝ) y

theorem rv_C (y : ℝ) (c : ℕ) : rv y (C c) = c := by simp [rv]

theorem rv_X (y : ℝ) : rv y X = y := by simp [rv]

theorem rv_L2 (y : ℝ) (s : ℕ) : rv y (L2 s) = 2 ^ s * (1 + y) := by
  unfold L2
  rw [map_mul, rv_C, map_add, map_one, rv_X]
  push_cast
  ring

theorem rv_Mf (y : ℝ) (lk lk1 : ℕ) : rv y (Mf lk lk1) = lk + lk1 * y := by
  unfold Mf
  rw [map_add, rv_C, map_mul, rv_C, rv_X]

/-- Coefficientwise order implies the order of the values at `y ≥ 0`. -/
theorem rv_mono (y : ℝ) (hy : 0 ≤ y) (F G : ℕ[X]) (h : ∀ i, F.coeff i ≤ G.coeff i) : rv y F ≤ rv y G := by
  have hF : F.natDegree < max F.natDegree G.natDegree + 1 := Nat.lt_succ_of_le (le_max_left _ _)
  have hG : G.natDegree < max F.natDegree G.natDegree + 1 := Nat.lt_succ_of_le (le_max_right _ _)
  show eval₂ (Nat.castRingHom ℝ) y F ≤ eval₂ (Nat.castRingHom ℝ) y G
  rw [eval₂_eq_sum_range' _ hF, eval₂_eq_sum_range' _ hG]
  refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (pow_nonneg hy i)
  exact Nat.cast_le.mpr (h i)

/-- The integer coefficient `d` of `Ĥ`: slot `d` of `Hp` minus the bias. -/
def coefZ (P : Params) (Hp d : ℕ) : ℤ := (slot P.W Hp d : ℤ) - 2 ^ (P.aH - 1)

/-- `Ĥ(t) = ∑ d ≤ 2 * D, Hh d * t ^ d`. -/
noncomputable def hEval (P : Params) (Hp : ℕ) (t : ℝ) : ℝ :=
  ∑ d ∈ range (2 * P.D + 1), (coefZ P Hp d : ℝ) * t ^ d

/-- The real value of the state of Horner's rule. -/
theorem hornerP_rv (P : Params) (Hp lk lk1 : ℕ) (y : ℝ) : ∀ (k : ℕ) (Sp Sn Pw : ℕ[X]),
    rv y (hornerP P Hp lk lk1 k Sp Sn Pw).1 - rv y (hornerP P Hp lk lk1 k Sp Sn Pw).2 =
      (rv y Sp - rv y Sn) * (rv y (L2 P.s) - rv y (Mf lk lk1)) ^ k
        + rv y Pw * ∑ d ∈ range k, (coefZ P Hp d : ℝ) * (rv y (L2 P.s) - rv y (Mf lk lk1)) ^ d
          * rv y (L2 P.s) ^ (k - 1 - d)
  | 0, Sp, Sn, Pw => by simp [hornerP]
  | k + 1, Sp, Sn, Pw => by
    have e : ∀ d ∈ range k, (coefZ P Hp d : ℝ) * (rv y (L2 P.s) - rv y (Mf lk lk1)) ^ d
          * rv y (L2 P.s) ^ (k + 1 - 1 - d)
        = rv y (L2 P.s) * ((coefZ P Hp d : ℝ) * (rv y (L2 P.s) - rv y (Mf lk lk1)) ^ d
          * rv y (L2 P.s) ^ (k - 1 - d)) := by
      intro d hd
      have hd' := mem_range.mp hd
      have e' : k + 1 - 1 - d = (k - 1 - d) + 1 := by omega
      rw [e', pow_succ]
      ring
    rw [hornerP, hornerP_rv P Hp lk lk1 y k, sum_range_succ, sum_congr rfl e, ← mul_sum]
    simp only [map_add, map_mul, rv_C, Nat.add_sub_cancel, Nat.sub_self, pow_zero, coefZ]
    push_cast
    ring

theorem hbP_rv (P : Params) (Hp lk lk1 : ℕ) (y : ℝ) :
    rv y (hbP P Hp lk lk1).1 - rv y (hbP P Hp lk lk1).2 =
      ∑ d ∈ range (2 * P.D + 1), (coefZ P Hp d : ℝ) * (rv y (L2 P.s) - rv y (Mf lk lk1)) ^ d
        * rv y (L2 P.s) ^ (2 * P.D - d) := by
  have h := hornerP_rv P Hp lk lk1 y (2 * P.D + 1) 0 0 1
  simp only [map_zero, map_one, sub_self, zero_mul, zero_add, one_mul, Nat.add_sub_cancel] at h
  exact h

theorem bernP_rv (P : Params) (Hp Dn lk lk1 : ℕ) (y : ℝ) :
    rv y (bernP P Hp Dn lk lk1).1 - rv y (bernP P Hp Dn lk lk1).2 =
      (Dn : ℝ) ^ 2 * rv y (L2 P.s) ^ (4 * P.D + 1)
        - 2 * rv y (Mf lk lk1) * (rv y (hbP P Hp lk lk1).1 - rv y (hbP P Hp lk lk1).2) ^ 2 := by
  have h2 : rv y 2 = 2 := map_ofNat (rv y) 2
  simp only [bernP, map_add, map_mul, map_pow, rv_C, h2]
  ring

/-- On a piece, `B(y) ≥ 0` for `y ≥ 0`. -/
theorem interval_real (P : Params) (Hp Dn lk lk1 : ℕ) (hV : 1 ≤ P.V) (h : intervalOk P Hp Dn lk lk1 = true)
    (y : ℝ) (hy : 0 ≤ y) :
    2 * ((lk : ℝ) + lk1 * y) * (∑ d ∈ range (2 * P.D + 1), (coefZ P Hp d : ℝ)
        * (2 ^ P.s * (1 + y) - ((lk : ℝ) + lk1 * y)) ^ d * (2 ^ P.s * (1 + y)) ^ (2 * P.D - d)) ^ 2
      ≤ (Dn : ℝ) ^ 2 * (2 ^ P.s * (1 + y)) ^ (4 * P.D + 1) := by
  have hmono := rv_mono y hy _ _ (intervalOk_coeff P Hp Dn lk lk1 hV h)
  have hb := bernP_rv P Hp Dn lk lk1 y
  rw [hbP_rv, rv_L2, rv_Mf] at hb
  linarith

/-- On a piece, `(2 - 2 * t) * Ĥ(t) ^ 2 ≤ Dn ^ 2`. -/
theorem interval_bound (P : Params) (Hp Dn lk lk1 : ℕ) (hV : 1 ≤ P.V) (h : intervalOk P Hp Dn lk lk1 = true)
    (t : ℝ) (h1 : (lk1 : ℝ) < 2 ^ P.s * (1 - t)) (h2 : 2 ^ P.s * (1 - t) ≤ lk) :
    (2 - 2 * t) * hEval P Hp t ^ 2 ≤ (Dn : ℝ) ^ 2 := by
  have hδ : 0 < 2 ^ P.s * (1 - t) - lk1 := sub_pos.mpr h1
  have hy : 0 ≤ ((lk : ℝ) - 2 ^ P.s * (1 - t)) / (2 ^ P.s * (1 - t) - lk1) :=
    div_nonneg (sub_nonneg.mpr h2) hδ.le
  have key := interval_real P Hp Dn lk lk1 hV h _ hy
  generalize hyd : ((lk : ℝ) - 2 ^ P.s * (1 - t)) / (2 ^ P.s * (1 - t) - lk1) = y at key hy
  -- `M (y) = 2 ^ s * (1 - t) * (1 + y)`
  have hm : (lk : ℝ) + lk1 * y = 2 ^ P.s * (1 + y) * (1 - t) := by
    rw [← hyd]
    field_simp
    ring
  have hpos : (0 : ℝ) < 2 ^ P.s * (1 + y) := by positivity
  have hsub : (2 : ℝ) ^ P.s * (1 + y) - 2 ^ P.s * (1 + y) * (1 - t) = 2 ^ P.s * (1 + y) * t := by ring
  have hsum : ∑ d ∈ range (2 * P.D + 1), (coefZ P Hp d : ℝ) * (2 ^ P.s * (1 + y) * t) ^ d
        * (2 ^ P.s * (1 + y)) ^ (2 * P.D - d)
      = (2 ^ P.s * (1 + y)) ^ (2 * P.D) * hEval P Hp t := by
    unfold hEval
    rw [mul_sum]
    refine sum_congr rfl fun d hd => ?_
    have hd' : d ≤ 2 * P.D := Nat.lt_succ_iff.mp (mem_range.mp hd)
    have e : (2 ^ P.s * (1 + y)) ^ (2 * P.D) = (2 ^ P.s * (1 + y)) ^ d * (2 ^ P.s * (1 + y)) ^ (2 * P.D - d) := by
      rw [← pow_add, Nat.add_sub_of_le hd']
    rw [e, mul_pow]
    ring
  rw [hm, hsub, hsum] at key
  have e : 2 * (2 ^ P.s * (1 + y) * (1 - t)) * ((2 ^ P.s * (1 + y)) ^ (2 * P.D) * hEval P Hp t) ^ 2
      = (2 - 2 * t) * hEval P Hp t ^ 2 * (2 ^ P.s * (1 + y)) ^ (4 * P.D + 1) := by ring
  rw [e] at key
  exact le_of_mul_le_mul_right key (pow_pos hpos _)

/-! ## The cover and the theorem -/

theorem cutsGo_cover (P : Params) (Hp Dn : ℕ) : ∀ (l : List ℕ) (prev : ℕ), cutsGo P Hp Dn l prev = true →
    ∀ μ : ℝ, 0 < μ → μ ≤ prev →
      ∃ lk lk1 : ℕ, intervalOk P Hp Dn lk lk1 = true ∧ (lk1 : ℝ) < μ ∧ μ ≤ lk
  | [], prev, h, μ, h0, h1 => by
    have hp : prev = 0 := Nat.eq_of_beq_eq_true h
    rw [hp, Nat.cast_zero] at h1
    exact absurd h0 (not_lt.mpr h1)
  | lam :: l, prev, h, μ, h0, h1 => by
    have h' : (Nat.blt lam prev && intervalOk P Hp Dn prev lam && cutsGo P Hp Dn l lam) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h'
    by_cases hμ : (lam : ℝ) < μ
    · exact ⟨prev, lam, h'.1.2, hμ, h1⟩
    · exact cutsGo_cover P Hp Dn l lam h'.2 μ h0 (not_lt.mp hμ)

theorem le_div_sqrt {h D x : ℝ} (hx : 0 < x) (hD : 0 ≤ D) (hle : x * h ^ 2 ≤ D ^ 2) :
    h ≤ D / Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  rw [le_div_iff₀ hs]
  by_contra hcon
  have hlt : D < h * Real.sqrt x := not_le.mp hcon
  have h2 : D ^ 2 < (h * Real.sqrt x) ^ 2 := by nlinarith
  rw [mul_pow, Real.sq_sqrt hx.le] at h2
  linarith

/-- **Soundness of the checker of the minorant condition.** If the checker accepts, then
`Ĥ(t) ≤ Dn / √(2 - 2 * t)` for all `-1 ≤ t < 1`. -/
theorem check_sound (P : Params) (Hp Dn : ℕ) (cuts : List ℕ) (h : check P Hp Dn cuts = true) :
    ∀ t : ℝ, -1 ≤ t → t < 1 → hEval P Hp t ≤ Dn / Real.sqrt (2 - 2 * t) := by
  have h' : (Nat.ble 1 P.V && cutsGo P Hp Dn cuts (1 <<< (P.s + 1))) = true := h
  rw [Bool.and_eq_true, Nat.ble_eq, Nat.one_shiftLeft] at h'
  intro t ht1 ht2
  have hμ0 : (0 : ℝ) < 2 ^ P.s * (1 - t) := by
    have : (0 : ℝ) < 1 - t := by linarith
    positivity
  have hμ1 : (2 : ℝ) ^ P.s * (1 - t) ≤ ((2 ^ (P.s + 1) : ℕ) : ℝ) := by
    push_cast
    rw [pow_succ]
    have : (0 : ℝ) < 2 ^ P.s := by positivity
    nlinarith
  obtain ⟨lk, lk1, hok, hl, hu⟩ := cutsGo_cover P Hp Dn cuts _ h'.2 _ hμ0 hμ1
  have hb := interval_bound P Hp Dn lk lk1 h'.1 hok t hl hu
  exact le_div_sqrt (by linarith) (Nat.cast_nonneg Dn) hb

end CAP.UniPos

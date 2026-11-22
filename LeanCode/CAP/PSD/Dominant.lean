module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# E2, positive definiteness: the mathematical part of the soundness

Two statements about real matrices, independent of the packed arithmetic of the checker.

* `CAP.PSD.posDef_of_dominant`: a real symmetric matrix that is strictly diagonally dominant with
  positive diagonal is positive definite.
* `CAP.PSD.posDef_of_witness`: if `G` and `L` are integer matrices, `G` is symmetric, and
  `R = 2 ^ s • G - L * Lᵀ` satisfies `|R i j| ≤ 2 ^ e` for `i ≠ j` and `R i i > (n - 1) * 2 ^ e`,
  then `G` is positive definite as a real matrix. These are the conditions that the checker
  `CAP.PSD.check` verifies.
-/

@[expose] public section

namespace CAP.PSD

open Matrix Finset

/-- For real numbers, `2 * r * a * b + |r| * (a ^ 2 + b ^ 2) ≥ 0`. -/
theorem two_mul_abs_nonneg (r a b : ℝ) : 0 ≤ 2 * (r * a * b) + |r| * (a ^ 2 + b ^ 2) := by
  rcases le_total 0 r with h | h
  · rw [abs_of_nonneg h]
    nlinarith [mul_nonneg h (sq_nonneg (a + b))]
  · rw [abs_of_nonpos h]
    nlinarith [mul_nonneg (neg_nonneg.mpr h) (sq_nonneg (a - b))]

/-- A real symmetric matrix that is strictly diagonally dominant with positive diagonal is
positive definite. -/
theorem posDef_of_dominant {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) (hsymm : ∀ i j, R i j = R j i)
    (hdom : ∀ i, (∑ j, if j = i then 0 else |R i j|) < R i i) : R.PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    simp [conjTranspose_apply, hsymm j i]
  · intro x hx
    -- the margin of row `i`
    set d : Fin n → ℝ := fun i => R i i - ∑ j, if j = i then 0 else |R i j| with hd
    have hdpos : ∀ i, 0 < d i := fun i => sub_pos.mpr (hdom i)
    -- the terms of the quadratic form that remain after the margins are removed
    set g : Fin n → Fin n → ℝ := fun i j => if j = i then 0 else R i j * x i * x j + |R i j| * x i ^ 2 with hg
    have hquad : star x ⬝ᵥ (R *ᵥ x) = ∑ i, d i * x i ^ 2 + ∑ i, ∑ j, g i j := by
      have h1 : star x ⬝ᵥ (R *ᵥ x) = ∑ i, ∑ j, R i j * x i * x j := by
        simp only [dotProduct, mulVec, star_trivial, Pi.star_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [h1, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h2 : ∑ j, R i j * x i * x j = R i i * x i ^ 2 + ∑ j, if j = i then 0 else R i j * x i * x j := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        congr 1
        · ring
        · rw [← Finset.add_sum_erase (s := Finset.univ) (a := i)
            (f := fun j => if j = i then 0 else R i j * x i * x j) (Finset.mem_univ i)]
          simp only [if_true, zero_add]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [if_neg (Finset.ne_of_mem_erase hj)]
      have h3 : (∑ j, g i j) = (∑ j, if j = i then 0 else R i j * x i * x j)
          + (∑ j, if j = i then 0 else |R i j|) * x i ^ 2 := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hg]
        split_ifs <;> ring
      rw [h2, h3, hd]
      ring
    have hswap : ∑ i, ∑ j, g i j = ∑ i, ∑ j, g j i := Finset.sum_comm
    have hnonneg : 0 ≤ ∑ i, ∑ j, g i j := by
      have h2 : 0 ≤ ∑ i, ∑ j, (g i j + g j i) := by
        refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
        simp only [hg]
        by_cases hij : j = i
        · simp [hij]
        · have hji : ¬ i = j := fun h => hij h.symm
          rw [if_neg hij, if_neg hji, hsymm j i]
          have := two_mul_abs_nonneg (R i j) (x i) (x j)
          nlinarith [this]
      have h3 : ∑ i, ∑ j, (g i j + g j i) = 2 * ∑ i, ∑ j, g i j := by
        simp only [Finset.sum_add_distrib]
        rw [← hswap]
        ring
      linarith
    obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := Function.ne_iff.mp hx
    have hpos : 0 < ∑ i, d i * x i ^ 2 := by
      refine Finset.sum_pos' (fun i _ => mul_nonneg (hdpos i).le (sq_nonneg _)) ⟨k, Finset.mem_univ k, ?_⟩
      exact mul_pos (hdpos k) (by positivity)
    rw [hquad]
    linarith

/-- The conditions of the checker imply positive definiteness: if `G` is a symmetric integer
matrix and `L` an integer matrix such that `R = 2 ^ s • G - L * Lᵀ` has off-diagonal entries of
absolute value at most `2 ^ e` and diagonal entries larger than `(n - 1) * 2 ^ e`, then `G` is
positive definite as a real matrix. -/
theorem posDef_of_witness {n : ℕ} (G L : Matrix (Fin n) (Fin n) ℤ) (s e : ℕ)
    (hG : ∀ i j, G i j = G j i)
    (hoff : ∀ i j, i ≠ j → |(2 : ℤ) ^ s * G i j - ∑ k, L i k * L j k| ≤ 2 ^ e)
    (hdiag : ∀ i, ((n : ℤ) - 1) * 2 ^ e < (2 : ℤ) ^ s * G i i - ∑ k, L i k * L i k) :
    (G.map (Int.cast : ℤ → ℝ)).PosDef := by
  set Gr : Matrix (Fin n) (Fin n) ℝ := G.map (Int.cast : ℤ → ℝ) with hGr
  set Lr : Matrix (Fin n) (Fin n) ℝ := L.map (Int.cast : ℤ → ℝ) with hLr
  set R : Matrix (Fin n) (Fin n) ℝ := (2 : ℝ) ^ s • Gr - Lr * Lrᵀ with hR
  have hRentry : ∀ i j, R i j = (((2 : ℤ) ^ s * G i j - ∑ k, L i k * L j k : ℤ) : ℝ) := by
    intro i j
    simp [hR, hGr, hLr, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply]
  have hRsymm : ∀ i j, R i j = R j i := by
    intro i j
    rw [hRentry, hRentry, hG i j]
    congr 2
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hRpd : R.PosDef := by
    refine posDef_of_dominant R hRsymm fun i => ?_
    have hle : (∑ j, if j = i then 0 else |R i j|) ≤ ((n : ℝ) - 1) * 2 ^ e := by
      have h1 : (∑ j, if j = i then 0 else |R i j|) ≤ ∑ j, if j = i then 0 else (2 : ℝ) ^ e := by
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases hji : j = i
        · simp [hji]
        · rw [if_neg hji, if_neg hji, hRentry, ← Int.cast_abs]
          have := hoff i j (fun h => hji h.symm)
          exact_mod_cast this
      have h2 : (∑ j : Fin n, if j = i then 0 else (2 : ℝ) ^ e) = ((n : ℝ) - 1) * 2 ^ e := by
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
        congr 1
        have : (Finset.univ.filter fun j : Fin n => ¬ j = i).card = n - 1 := by
          rw [Finset.filter_ne' Finset.univ i, Finset.card_erase_of_mem (Finset.mem_univ i),
            Finset.card_univ, Fintype.card_fin]
        rw [this]
        have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (fun h => by subst h; exact i.elim0))
        push_cast [Nat.cast_sub hn]
        ring
      linarith
    have hd : ((n : ℝ) - 1) * 2 ^ e < R i i := by
      rw [hRentry]
      have := hdiag i
      exact_mod_cast this
    linarith
  have hLL : (Lr * Lrᵀ).PosSemidef := by
    have := posSemidef_self_mul_conjTranspose Lr
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hsG : ((2 : ℝ) ^ s • Gr).PosDef := by
    have h := hRpd.add_posSemidef hLL
    have hEq : R + Lr * Lrᵀ = (2 : ℝ) ^ s • Gr := by rw [hR]; abel
    rwa [hEq] at h
  have hpow : (0 : ℝ) < ((2 : ℝ) ^ s)⁻¹ := by positivity
  have h := hsG.smul hpow
  have hEq : ((2 : ℝ) ^ s)⁻¹ • ((2 : ℝ) ^ s • Gr) = Gr := by
    rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  rwa [hEq] at h

end CAP.PSD

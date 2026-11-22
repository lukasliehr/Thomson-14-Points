module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity

/-!
# Gram matrices in three dimensions

* `eq_zero_of_orth`: a vector orthogonal to three vectors with invertible Gram matrix vanishes.
* `inner_face` (**the inner product through a face**): let `B 0, B 1, B 2` be unit vectors with pairwise inner
  products `γ`, `γ ≠ 1`, `1 + 2 γ ≠ 0`. Then the inner product of two vectors is the form `Qg γ` of their inner
  products with `B 0, B 1, B 2`.
* `congr_of_gram` (**congruence**): two configurations with the same inner products, one of which contains three
  vectors with invertible Gram matrix, differ by an orthogonal map.
-/

@[expose] public section

namespace N32

open Finset Matrix

/-- The Gram matrix of three vectors. -/
noncomputable def gram3 (B : Fin 3 → Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun k l => ∑ c, B k c * B l c

theorem gram3_eq (B : Fin 3 → Fin 3 → ℝ) : gram3 B = Matrix.of B * (Matrix.of B)ᵀ := by
  ext k l
  simp [gram3, Matrix.mul_apply]

theorem det_ne_of_gram (B : Fin 3 → Fin 3 → ℝ) (h : (gram3 B).det ≠ 0) : (Matrix.of B).det ≠ 0 := by
  intro h0
  apply h
  rw [gram3_eq, det_mul, det_transpose, h0, zero_mul]

/-- A vector orthogonal to three vectors with invertible Gram matrix vanishes. -/
theorem eq_zero_of_orth (B : Fin 3 → Fin 3 → ℝ) (hG : (gram3 B).det ≠ 0) (w : Fin 3 → ℝ)
    (hw : ∀ k, ∑ c, B k c * w c = 0) : w = 0 :=
  Matrix.eq_zero_of_mulVec_eq_zero (det_ne_of_gram B hG)
    (funext fun k => by simpa [Matrix.mulVec, dotProduct] using hw k)

/-- The form of a face: the inner product of two vectors with the inner products `s`, `t` with the vectors of a
face whose Gram matrix has `1` on the diagonal and `γ` off it. -/
noncomputable def Qg (γ : ℝ) (s t : Fin 3 → ℝ) : ℝ :=
  ((1 + 2 * γ) * ∑ l, s l * t l - γ * (∑ l, s l) * (∑ l, t l)) / ((1 - γ) * (1 + 2 * γ))

theorem det_face (γ : ℝ) (B : Fin 3 → Fin 3 → ℝ) (hB : ∀ k l, ∑ c, B k c * B l c = if k = l then 1 else γ) :
    (gram3 B).det = (1 - γ) ^ 2 * (1 + 2 * γ) := by
  rw [det_fin_three]
  simp only [gram3, of_apply, hB]
  simp
  ring

/-- **The inner product through a face.** -/
theorem inner_face (γ : ℝ) (h1 : γ ≠ 1) (h2 : 1 + 2 * γ ≠ 0) (B : Fin 3 → Fin 3 → ℝ)
    (hB : ∀ k l, ∑ c, B k c * B l c = if k = l then 1 else γ) (z z' : Fin 3 → ℝ) :
    ∑ c, z c * z' c = Qg γ (fun k => ∑ c, z c * B k c) (fun k => ∑ c, z' c * B k c) := by
  have hD : (1 - γ) * (1 + 2 * γ) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm h1)) h2
  have hdet : (gram3 B).det ≠ 0 := by
    rw [det_face γ B hB]
    exact mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm h1))) h2
  -- the coefficients of `z` in the face, times `(1 - γ) (1 + 2 γ)`
  have hw := eq_zero_of_orth B hdet (fun c => (1 - γ) * (1 + 2 * γ) * z c
      - ∑ k, ((1 + 2 * γ) * (∑ c, z c * B k c) - γ * ∑ l, ∑ c, z c * B l c) * B k c) (fun l => by
    have e : ∑ c, B l c * ((1 - γ) * (1 + 2 * γ) * z c
        - ∑ k, ((1 + 2 * γ) * (∑ c, z c * B k c) - γ * ∑ l, ∑ c, z c * B l c) * B k c)
        = (1 - γ) * (1 + 2 * γ) * (∑ c, z c * B l c)
          - ∑ k, ((1 + 2 * γ) * (∑ c, z c * B k c) - γ * ∑ l, ∑ c, z c * B l c) * ∑ c, B k c * B l c := by
      simp only [mul_sub, sum_sub_distrib, mul_sum]
      congr 1
      · exact sum_congr rfl fun c _ => by ring
      · rw [sum_comm]
        exact sum_congr rfl fun k _ => sum_congr rfl fun c _ => by ring
    rw [e]
    simp only [hB, Fin.sum_univ_three]
    fin_cases l <;> simp <;> ring)
  have hz : ∀ c, (1 - γ) * (1 + 2 * γ) * z c
      = ∑ k, ((1 + 2 * γ) * (∑ c, z c * B k c) - γ * ∑ l, ∑ c, z c * B l c) * B k c := by
    intro c
    have := congrFun hw c
    simp only [Pi.zero_apply] at this
    linarith
  have key : (1 - γ) * (1 + 2 * γ) * ∑ c, z c * z' c
      = (1 + 2 * γ) * ∑ l, (∑ c, z c * B l c) * (∑ c, z' c * B l c)
        - γ * (∑ l, ∑ c, z c * B l c) * (∑ l, ∑ c, z' c * B l c) := by
    rw [mul_sum]
    simp only [← mul_assoc, hz]
    simp only [sum_mul]
    rw [sum_comm]
    simp only [Fin.sum_univ_three, mul_sum]
    ring
  unfold Qg
  rw [eq_div_iff hD]
  linarith

/-- **Congruence from the inner products.** -/
theorem congr_of_gram {N : ℕ} (x y : Fin N → Fin 3 → ℝ) (h : ∀ i j, ∑ c, y i c * y j c = ∑ c, x i c * x j c)
    (k : Fin 3 → Fin N) (hk : (gram3 fun a => x (k a)).det ≠ 0) :
    ∃ U ∈ Matrix.orthogonalGroup (Fin 3) ℝ, ∀ i, y i = U.mulVec (x i) := by
  have hG : gram3 (fun a => y (k a)) = gram3 (fun a => x (k a)) := by
    ext a b
    simp [gram3, h]
  have hMd : (Matrix.of fun a => x (k a)).det ≠ 0 := det_ne_of_gram _ hk
  have hNd : (Matrix.of fun a => y (k a)).det ≠ 0 := det_ne_of_gram _ (by rw [hG]; exact hk)
  set M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun a => x (k a) with hM
  set Nm : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun a => y (k a) with hN
  have hMN : Nm * Nmᵀ = M * Mᵀ := by
    rw [hM, hN, ← gram3_eq, ← gram3_eq, hG]
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hMd
  have hMtu : IsUnit Mᵀ.det := by rw [det_transpose]; exact hMu
  refine ⟨Nmᵀ * Mᵀ⁻¹, ?_, fun i => ?_⟩
  · rw [mem_orthogonalGroup_iff', transpose_mul, transpose_transpose, ← transpose_nonsing_inv, transpose_transpose,
      transpose_nonsing_inv]
    calc M⁻¹ * Nm * (Nmᵀ * Mᵀ⁻¹) = M⁻¹ * (Nm * Nmᵀ) * Mᵀ⁻¹ := by simp only [Matrix.mul_assoc]
      _ = M⁻¹ * (M * Mᵀ) * Mᵀ⁻¹ := by rw [hMN]
      _ = (M⁻¹ * M) * (Mᵀ * Mᵀ⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [nonsing_inv_mul _ hMu, mul_nonsing_inv _ hMtu, Matrix.one_mul]
  · have hz : Nm.mulVec ((Nmᵀ * Mᵀ⁻¹).mulVec (x i) - y i) = 0 := by
      rw [mulVec_sub, mulVec_mulVec, ← Matrix.mul_assoc, hMN, Matrix.mul_assoc, mul_nonsing_inv _ hMtu,
        Matrix.mul_one]
      funext a
      simp only [Pi.sub_apply, Pi.zero_apply, Matrix.mulVec, dotProduct, hM, hN, of_apply]
      rw [h (k a) i]
      ring
    have := eq_zero_of_mulVec_eq_zero hNd hz
    exact (sub_eq_zero.mp this).symm

end N32

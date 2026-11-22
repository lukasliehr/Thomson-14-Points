module

public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import CAP.Schema.ThreePoint.Sound
public import CAP.Schema.ThreePoint.Triples

/-!
# Schema S2, the bound: the polynomials of the identity at real points

The polynomials of the identity have integer coefficients. `evR u v t` is their value at a real
point `(u, v, t)`. This file proves the facts about these values that the bound needs.

* **The kernels.** If `z` is a complex number with real part `t - u v` and squared absolute value
  `(1 - u²) (1 - v²)`, then `Qₖ (u, v, t) = Re (z ^ k)` (`evR_QZ`): both sides satisfy the
  recurrence `Qₖ₊₂ = 2 (t - u v) Qₖ₊₁ - (1 - u²) (1 - v²) Qₖ`.
* **Positive definite kernels.** Let `u j` be real and `w j` complex numbers, indexed by a finite
  set. For a block with a positive definite matrix,
  `∑ j l, φ (u j, u l) Re ((w j conj (w l)) ^ k) ≥ 0` (`block_kernel_nonneg`): the sum is the
  quadratic form of the matrix at the two vectors `∑ j, u j ^ r Re (w j ^ k)` and
  `∑ j, u j ^ r Im (w j ^ k)`.
* **Sums of squares.** The polynomial of a block with a positive definite matrix and a nonnegative
  weight is nonnegative (`evR_sosZ_nonneg`).
* **The polynomial `Z`** at a real point is the function `Zf` of `Triples.lean` (`evR_ZZ`), and the
  six renamings of `symm6` are the six permutations of the arguments (`evR_symm6`).

The matrix of a block is `symMat`: the stored upper triangular array has the diagonal entries
`Dn M i i` and the entries `2 Dn M i j` above the diagonal, so `symMat = 2 Dn M`.
-/

@[expose] public section

namespace CAP.ThreePoint

open MvPolynomial Finset Matrix

/-! ## Values at real points -/

/-- The value of a polynomial with integer coefficients at the real point `(u, v, t)`. -/
noncomputable def evR (u v t : ℝ) : PolyZ →ₐ[ℤ] ℝ := aeval ![u, v, t]

@[simp] theorem evR_X0 (u v t : ℝ) : evR u v t (X 0) = u := by simp [evR]

@[simp] theorem evR_X1 (u v t : ℝ) : evR u v t (X 1) = v := by simp [evR]

@[simp] theorem evR_X2 (u v t : ℝ) : evR u v t (X 2) = t := by simp [evR]

@[simp] theorem evR_C (u v t : ℝ) (c : ℤ) : evR u v t (C c) = c := by simp [evR]

/-- The six renamings of `symm6` are the six permutations of the arguments. -/
theorem evR_symm6 (u v t : ℝ) (F : PolyZ) :
    evR u v t (symm6 F) = evR u v t F + evR u t v F + evR v u t F + evR v t u F + evR t u v F + evR t v u F := by
  have e1 : (![u, v, t] : Fin 3 → ℝ) ∘ (Equiv.swap (1 : Fin 3) 2) = ![u, t, v] := by
    funext i
    fin_cases i <;> rfl
  have e2 : (![u, v, t] : Fin 3 → ℝ) ∘ (Equiv.swap (0 : Fin 3) 1) = ![v, u, t] := by
    funext i
    fin_cases i <;> rfl
  have e3 : (![u, v, t] : Fin 3 → ℝ) ∘ (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) = ![v, t, u] := by
    funext i
    fin_cases i <;> rfl
  have e4 : (![u, v, t] : Fin 3 → ℝ) ∘ (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1) = ![t, u, v] := by
    funext i
    fin_cases i <;> rfl
  have e5 : (![u, v, t] : Fin 3 → ℝ) ∘ (Equiv.swap (0 : Fin 3) 2) = ![t, v, u] := by
    funext i
    fin_cases i <;> rfl
  unfold symm6 evR
  simp only [map_add, aeval_rename, e1, e2, e3, e4, e5]

theorem evR_s1Z (u v t : ℝ) (F : PolyZ) : evR u v t (s1Z F) = evR u u 1 F := by
  have h : (fun i => aeval ![u, v, t] ((![X 0, X 0, 1] : Fin 3 → PolyZ) i)) = ![u, u, 1] := by
    funext i
    fin_cases i <;> simp
  show aeval ![u, v, t] (bind₁ ![X 0, X 0, 1] F) = aeval ![u, u, 1] F
  rw [aeval_bind₁, h]

theorem evR_s2Z (u v t : ℝ) (F : PolyZ) : evR u v t (s2Z F) = evR u 1 u F := by
  have h : (fun i => aeval ![u, v, t] ((![X 0, 1, X 0] : Fin 3 → PolyZ) i)) = ![u, 1, u] := by
    funext i
    fin_cases i <;> simp
  show aeval ![u, v, t] (bind₁ ![X 0, 1, X 0] F) = aeval ![u, 1, u] F
  rw [aeval_bind₁, h]

theorem evR_s3Z (u v t : ℝ) (F : PolyZ) : evR u v t (s3Z F) = evR 1 u u F := by
  have h : (fun i => aeval ![u, v, t] ((![1, X 0, X 0] : Fin 3 → PolyZ) i)) = ![1, u, u] := by
    funext i
    fin_cases i <;> simp
  show aeval ![u, v, t] (bind₁ ![1, X 0, X 0] F) = aeval ![1, u, u] F
  rw [aeval_bind₁, h]

/-- The value of `Z`. The polynomial `Ĥ` has the variable `u` only. -/
theorem evR_ZZ (P : Params) (mrows : List ℕ) (sos : List Sos) (Hp cp : ℕ) (u v t : ℝ) :
    evR u v t (ZZ P mrows sos Hp cp)
      = Zf (P.N : ℝ) (fun u v t => evR u v t (momentZ P mrows 0)) (fun u v t => evR u v t (sosSumZ P sos))
          (fun u => evR u 0 0 (HZ P Hp)) (x0Z P (hdNat mrows) : ℝ) (cp : ℝ) u v t := by
  have hH : evR u v t (HZ P Hp) = evR u 0 0 (HZ P Hp) := by
    unfold HZ
    simp only [map_sum, map_mul, map_pow, evR_C, evR_X0]
  unfold ZZ Zf
  simp only [map_add, map_sub, map_mul, evR_C, evR_s1Z, evR_s2Z, evR_s3Z, hH]
  push_cast
  ring

/-! ## The kernels -/

/-- The kernels are the real parts of the powers of a complex number. -/
theorem evR_QZ (u v t : ℝ) (z : ℂ) (h1 : z.re = t - u * v) (h2 : Complex.normSq z = (1 - u ^ 2) * (1 - v ^ 2)) :
    ∀ k, evR u v t (QZ k) = (z ^ k).re ∧ evR u v t (QZ (k + 1)) = (z ^ (k + 1)).re
  | 0 => by
    constructor
    · simp [QZ]
    · simp [QZ, h1]
  | k + 1 => by
    obtain ⟨a, b⟩ := evR_QZ u v t z h1 h2 k
    refine ⟨b, ?_⟩
    have hq : z * z = ((2 * z.re : ℝ) : ℂ) * z - ((Complex.normSq z : ℝ) : ℂ) := by
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
        ring
      · simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
    have hz : z ^ (k + 1 + 1)
        = ((2 * z.re : ℝ) : ℂ) * z ^ (k + 1) - ((Complex.normSq z : ℝ) : ℂ) * z ^ k := by
      calc z ^ (k + 1 + 1) = z ^ k * (z * z) := by ring
        _ = z ^ k * (((2 * z.re : ℝ) : ℂ) * z - ((Complex.normSq z : ℝ) : ℂ)) := by rw [hq]
        _ = _ := by ring
    have hQ : QZ (k + 1 + 1) = 2 * (X 2 - X 0 * X 1) * QZ (k + 1) - (1 - X 0 ^ 2) * (1 - X 1 ^ 2) * QZ k := rfl
    rw [hz, hQ, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, h1, h2, ← a, ← b]
    simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, evR_X0, evR_X1, evR_X2]

theorem evR_one_QZ (k : ℕ) : evR 1 1 1 (QZ (k + 1)) = 0 := by
  have h := (evR_QZ 1 1 1 0 (by simp) (by simp) k).2
  rw [h]
  simp

/-! ## Quadratic forms -/

/-- The entries of the symmetric matrix of a block: twice the stored entry on the diagonal, and
the stored entry `(min i j, max i j)` elsewhere. -/
noncomputable def symEnt (P : Params) (n rows i j : ℕ) : ℝ :=
  if i = j then 2 * (entZ P n rows i 0 : ℝ)
  else if i < j then (entZ P n rows i (j - i) : ℝ) else (entZ P n rows j (i - j) : ℝ)

/-- The symmetric matrix of a block. -/
noncomputable def symMat (P : Params) (n rows : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j => symEnt P n rows i j

/-- The quadratic form of the symmetric matrix as a sum over the stored upper triangle. -/
theorem sym_sum (P : Params) (n rows : ℕ) (c : ℕ → ℕ → ℝ) (hc : ∀ i j, c i j = c j i) :
    ∑ i ∈ range n, ∑ j ∈ range n, symEnt P n rows i j * c i j
      = 2 * ∑ r ∈ range n, ∑ s ∈ range (n - r), (entZ P n rows r s : ℝ) * c r (r + s) := by
  have hp : ∀ i j, symEnt P n rows i j * c i j
      = (if i ≤ j then (entZ P n rows i (j - i) : ℝ) * c i j else 0)
        + (if j ≤ i then (entZ P n rows j (i - j) : ℝ) * c j i else 0) := by
    intro i j
    unfold symEnt
    rcases lt_trichotomy i j with h | h | h
    · rw [if_neg h.ne, if_pos h, if_pos h.le, if_neg (not_le.mpr h), add_zero]
    · subst h
      rw [if_pos rfl, if_pos (le_refl i), Nat.sub_self]
      ring
    · rw [if_neg h.ne', if_neg (not_lt.mpr h.le), if_neg (not_le.mpr h), if_pos h.le, zero_add, hc i j]
  have hrow : ∀ i ∈ range n, (∑ j ∈ range n, if i ≤ j then (entZ P n rows i (j - i) : ℝ) * c i j else 0)
      = ∑ s ∈ range (n - i), (entZ P n rows i s : ℝ) * c i (i + s) := by
    intro i _
    have e : (range n).filter (fun j => i ≤ j) = Ico i n := by
      ext j
      simp only [mem_filter, mem_range, mem_Ico]
      tauto
    rw [← sum_filter, e, sum_Ico_eq_sum_range]
    refine sum_congr rfl fun s _ => ?_
    rw [Nat.add_sub_cancel_left]
  have e2 : (∑ i ∈ range n, ∑ j ∈ range n, if j ≤ i then (entZ P n rows j (i - j) : ℝ) * c j i else 0)
      = ∑ i ∈ range n, ∑ j ∈ range n, if i ≤ j then (entZ P n rows i (j - i) : ℝ) * c i j else 0 := sum_comm
  rw [sum_congr rfl fun i _ => sum_congr rfl fun j _ => hp i j]
  simp only [sum_add_distrib]
  rw [e2, sum_congr rfl hrow]
  ring

theorem posDef_quad_nonneg {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (x : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * G i j * x j := by
  have e : ∑ i, ∑ j, x i * G i j * x j = star x ⬝ᵥ G *ᵥ x := by
    simp only [dotProduct, mulVec, star_trivial, Pi.star_apply, Finset.mul_sum, mul_assoc]
  rw [e]
  by_cases hx : x = 0
  · subst hx
    simp
  · exact (hG.dotProduct_mulVec_pos hx).le

/-- The quadratic form of a block with a positive definite matrix, written with the stored upper
triangle, is nonnegative. -/
theorem quad_nonneg (P : Params) (n rows : ℕ) (h : (symMat P n rows).PosDef) (α : ℕ → ℝ) :
    0 ≤ ∑ r ∈ range n, ∑ s ∈ range (n - r), (entZ P n rows r s : ℝ) * (α r * α (r + s)) := by
  have h1 := sym_sum P n rows (fun i j => α i * α j) (fun i j => mul_comm _ _)
  have h2 := posDef_quad_nonneg (symMat P n rows) h (fun i => α i)
  have e : ∑ i : Fin n, ∑ j : Fin n, α i * symMat P n rows i j * α j
      = ∑ i ∈ range n, ∑ j ∈ range n, symEnt P n rows i j * (α i * α j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range n, symEnt P n rows i j * (α i * α j)) n]
    refine sum_congr rfl fun i _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun j => symEnt P n rows i j * (α i * α j)) n]
    refine sum_congr rfl fun j _ => ?_
    show α i * symEnt P n rows i j * α j = _
    ring
  rw [e, h1] at h2
  linarith

/-! ## The moment blocks -/

theorem evR_phiZ (P : Params) (n rows : ℕ) (u v t : ℝ) :
    evR u v t (phiZ P n rows)
      = ∑ r ∈ range n, ∑ s ∈ range (n - r), (entZ P n rows r s : ℝ) * (u ^ r * v ^ (r + s)) := by
  unfold phiZ
  simp only [map_sum, map_mul, map_pow, evR_C, evR_X0, evR_X1]

theorem sum4_reorder {ι : Type*} [Fintype ι] (n : ℕ) (m : ℕ → ℕ) (F : ι → ι → ℕ → ℕ → ℝ) :
    ∑ j, ∑ l, ∑ r ∈ range n, ∑ s ∈ range (m r), F j l r s
      = ∑ r ∈ range n, ∑ s ∈ range (m r), ∑ j, ∑ l, F j l r s := by
  calc ∑ j, ∑ l, ∑ r ∈ range n, ∑ s ∈ range (m r), F j l r s
      = ∑ j, ∑ r ∈ range n, ∑ l, ∑ s ∈ range (m r), F j l r s := sum_congr rfl fun j _ => sum_comm
    _ = ∑ r ∈ range n, ∑ j, ∑ l, ∑ s ∈ range (m r), F j l r s := sum_comm
    _ = ∑ r ∈ range n, ∑ j, ∑ s ∈ range (m r), ∑ l, F j l r s :=
        sum_congr rfl fun r _ => sum_congr rfl fun j _ => sum_comm
    _ = ∑ r ∈ range n, ∑ s ∈ range (m r), ∑ j, ∑ l, F j l r s := sum_congr rfl fun r _ => sum_comm

/-- The kernel of a moment block with a positive definite matrix is positive definite. -/
theorem block_kernel_nonneg {ι : Type*} [Fintype ι] (P : Params) (n rows k : ℕ)
    (h : (symMat P n rows).PosDef) (u : ι → ℝ) (w : ι → ℂ) :
    0 ≤ ∑ j, ∑ l,
      (∑ r ∈ range n, ∑ s ∈ range (n - r), (entZ P n rows r s : ℝ) * (u j ^ r * u l ^ (r + s)))
        * ((w j * (starRingEnd ℂ) (w l)) ^ k).re := by
  have hre : ∀ j l, ((w j * (starRingEnd ℂ) (w l)) ^ k).re
      = (w j ^ k).re * (w l ^ k).re + (w j ^ k).im * (w l ^ k).im := by
    intro j l
    rw [mul_pow, ← map_pow, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have key : ∀ A : ι → ℝ,
      (∑ j, ∑ l, (∑ r ∈ range n, ∑ s ∈ range (n - r), (entZ P n rows r s : ℝ) * (u j ^ r * u l ^ (r + s)))
        * (A j * A l))
      = ∑ r ∈ range n, ∑ s ∈ range (n - r),
          (entZ P n rows r s : ℝ) * ((∑ j, u j ^ r * A j) * (∑ j, u j ^ (r + s) * A j)) := by
    intro A
    have e1 : ∀ j l, (∑ r ∈ range n, ∑ s ∈ range (n - r), (entZ P n rows r s : ℝ) * (u j ^ r * u l ^ (r + s)))
          * (A j * A l)
        = ∑ r ∈ range n, ∑ s ∈ range (n - r),
            (entZ P n rows r s : ℝ) * ((u j ^ r * A j) * (u l ^ (r + s) * A l)) := by
      intro j l
      rw [sum_mul]
      refine sum_congr rfl fun r _ => ?_
      rw [sum_mul]
      refine sum_congr rfl fun s _ => ?_
      ring
    rw [sum_congr rfl fun j _ => sum_congr rfl fun l _ => e1 j l,
      sum4_reorder n (fun r => n - r)
        (fun j l r s => (entZ P n rows r s : ℝ) * ((u j ^ r * A j) * (u l ^ (r + s) * A l)))]
    refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
    rw [sum_mul_sum, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
  have hA := quad_nonneg P n rows h (fun r => ∑ j, u j ^ r * (w j ^ k).re)
  have hB := quad_nonneg P n rows h (fun r => ∑ j, u j ^ r * (w j ^ k).im)
  have e : (∑ j, ∑ l,
      (∑ r ∈ range n, ∑ s ∈ range (n - r), (entZ P n rows r s : ℝ) * (u j ^ r * u l ^ (r + s)))
        * ((w j * (starRingEnd ℂ) (w l)) ^ k).re)
      = (∑ j, ∑ l, (∑ r ∈ range n, ∑ s ∈ range (n - r), (entZ P n rows r s : ℝ) * (u j ^ r * u l ^ (r + s)))
          * ((w j ^ k).re * (w l ^ k).re))
        + ∑ j, ∑ l, (∑ r ∈ range n, ∑ s ∈ range (n - r), (entZ P n rows r s : ℝ) * (u j ^ r * u l ^ (r + s)))
          * ((w j ^ k).im * (w l ^ k).im) := by
    simp only [← sum_add_distrib]
    refine sum_congr rfl fun j _ => sum_congr rfl fun l _ => ?_
    rw [hre, mul_add]
  rw [e, key (fun j => (w j ^ k).re), key (fun j => (w j ^ k).im)]
  exact add_nonneg hA hB

/-- The matrices of the moment blocks with the indices `k, k + 1, …` are positive definite. -/
def MomentPD (P : Params) : List ℕ → ℕ → Prop
  | [], _ => True
  | rows :: l, k => (symMat P (P.D + 1 - k) rows).PosDef ∧ MomentPD P l (k + 1)

/-- **The kernels of the three-point bound are positive definite.** Let `u j` be real numbers,
`w j` complex numbers and `tt j m` real numbers such that `w j conj (w m)` has the real part
`tt j m - u j u m` and the squared absolute value `(1 - (u j)²) (1 - (u m)²)`. If the matrices of
the moment blocks are positive definite, then `∑ j m, M (u j, u m, tt j m) ≥ 0`. -/
theorem moment_kernel_nonneg {ι : Type*} [Fintype ι] (P : Params) (u : ι → ℝ) (tt : ι → ι → ℝ) (w : ι → ℂ)
    (h1 : ∀ j m, (w j * (starRingEnd ℂ) (w m)).re = tt j m - u j * u m)
    (h2 : ∀ j m, Complex.normSq (w j * (starRingEnd ℂ) (w m)) = (1 - u j ^ 2) * (1 - u m ^ 2)) :
    ∀ (l : List ℕ) (k : ℕ), MomentPD P l k → 0 ≤ ∑ j, ∑ m, evR (u j) (u m) (tt j m) (momentZ P l k)
  | [], _, _ => by simp [momentZ]
  | rows :: l, k, h => by
    have h' : (symMat P (P.D + 1 - k) rows).PosDef ∧ MomentPD P l (k + 1) := h
    have ih := moment_kernel_nonneg P u tt w h1 h2 l (k + 1) h'.2
    have hb := block_kernel_nonneg P (P.D + 1 - k) rows k h'.1 u w
    have e : ∀ j m, evR (u j) (u m) (tt j m) (momentZ P (rows :: l) k)
        = (∑ r ∈ range (P.D + 1 - k), ∑ s ∈ range (P.D + 1 - k - r),
              (entZ P (P.D + 1 - k) rows r s : ℝ) * (u j ^ r * u m ^ (r + s)))
            * ((w j * (starRingEnd ℂ) (w m)) ^ k).re
          + evR (u j) (u m) (tt j m) (momentZ P l (k + 1)) := by
      intro j m
      rw [momentZ, map_add, map_mul, evR_phiZ, (evR_QZ (u j) (u m) (tt j m) _ (h1 j m) (h2 j m) k).1]
    simp only [e, sum_add_distrib]
    exact add_nonneg hb ih

theorem evR_one_moment (P : Params) : ∀ (l : List ℕ) (k : ℕ), evR 1 1 1 (momentZ P l (k + 1)) = 0
  | [], _ => by simp [momentZ]
  | rows :: l, k => by
    rw [momentZ, map_add, map_mul, evR_one_QZ, mul_zero, zero_add, evR_one_moment P l (k + 1)]

/-- At the point `(1, 1, 1)` only the first moment block contributes. -/
theorem evR_one_moment_zero (P : Params) (rows : ℕ) (l : List ℕ) :
    evR 1 1 1 (momentZ P (rows :: l) 0) = (x0Z P rows : ℝ) := by
  have hQ : evR 1 1 1 (QZ 0) = 1 := by simp [QZ]
  rw [momentZ, map_add, map_mul, evR_one_moment P l 0, add_zero, evR_phiZ, hQ, mul_one]
  unfold x0Z
  push_cast
  simp only [one_pow, mul_one]

/-! ## The blocks with a sum of squares -/

/-- The polynomial of a block with a positive definite matrix is nonnegative where its weight is. -/
theorem evR_sosZ_nonneg (P : Params) (B : Sos) (h : (symMat P B.n B.rows).PosDef) (u v t : ℝ)
    (hg : 0 ≤ evR u v t (polyZ P B.gT B.weight)) : 0 ≤ evR u v t (sosZ P B) := by
  have hq := quad_nonneg P B.n B.rows h (fun r => evR u v t (zZ P B r))
  have e : evR u v t (sosZ P B) = evR u v t (polyZ P B.gT B.weight)
      * ∑ r ∈ range B.n, ∑ s ∈ range (B.n - r),
          (entZ P B.n B.rows r s : ℝ) * (evR u v t (zZ P B r) * evR u v t (zZ P B (r + s))) := by
    unfold sosZ
    simp only [map_mul, map_sum, evR_C, mul_sum]
    refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
    ring
  rw [e]
  exact mul_nonneg hg hq

/-- The matrices of the blocks with a sum of squares are positive definite. -/
def SosPD (P : Params) : List Sos → Prop
  | [] => True
  | B :: l => (symMat P B.n B.rows).PosDef ∧ SosPD P l

theorem evR_sosSumZ_nonneg (P : Params) (u v t : ℝ) :
    ∀ l : List Sos, SosPD P l → (∀ B ∈ l, 0 ≤ evR u v t (polyZ P B.gT B.weight)) →
      0 ≤ evR u v t (sosSumZ P l)
  | [], _, _ => by simp [sosSumZ]
  | B :: l, h, hg => by
    have h' : (symMat P B.n B.rows).PosDef ∧ SosPD P l := h
    have hf : (0 : ℝ) ≤ ((B.f : ℤ) : ℝ) := by positivity
    rw [sosSumZ, map_add, map_mul, evR_C]
    exact add_nonneg (mul_nonneg hf (evR_sosZ_nonneg P B h'.1 u v t (hg B (by simp))))
      (evR_sosSumZ_nonneg P u v t l h'.2 fun B' hB' => hg B' (List.mem_cons_of_mem _ hB'))

end CAP.ThreePoint

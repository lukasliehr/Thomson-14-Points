module

public import N14.Jet.Kernel
public import N14.Jet.Root
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.GCongr

/-!
# Jets: polynomials in four variables as sequences of coefficients on the slots

A slot `e < 1296` stands for the monomial `x₀^a₀ x₁^a₁ x₂^a₂ x₃^a₃` with the degree `d = e / 216` and the
exponents `a₁ = e % 216 % 6`, `a₂ = e % 216 / 6 % 6`, `a₃ = e % 216 / 36`, `a₀ = d - a₁ - a₂ - a₃`; the slot is
*valid* if `a₁ + a₂ + a₃ ≤ d` (`Valid`; these are the 126 slots of `idxs`, `valid_iff_mem`). The slot of a
product of two monomials of total degree at most 5 is the sum of their slots (`valid_add`, `mval_add`), and two
valid slots whose degrees add up to at least 6 have a sum of at least 1296.

A polynomial of degree at most 5 is a sequence `c : ℕ → ℝ` that vanishes outside the valid slots (`Supp`), with
the value `pev c x`. Its part of degree `d` is `blk c d x`, bounded by `nrm c d * m ^ d` for `|x_k| ≤ m`
(`blk_abs_le`). The product of two polynomials, truncated at degree 5, is the convolution `cmul` of the two
sequences as sequences on the natural numbers, and the rest is the sum of the products of the parts whose
degrees add up to at least 6 (`pev_mul`).
-/

@[expose] public section

namespace N14.Jet

open Finset

/-- The degree of a slot. -/
def sdeg (e : ℕ) : ℕ := e / 216

/-- The exponents of the variables 1, 2, 3 of a slot. -/
def sa1 (e : ℕ) : ℕ := e % 216 % 6

def sa2 (e : ℕ) : ℕ := e % 216 / 6 % 6

def sa3 (e : ℕ) : ℕ := e % 216 / 36

/-- The slots of the monomials of degree at most 5. -/
def Valid (e : ℕ) : Prop := e < 1296 ∧ sa1 e + sa2 e + sa3 e ≤ sdeg e

instance (e : ℕ) : Decidable (Valid e) := by
  unfold Valid
  infer_instance

theorem idxs_lt : ∀ e ∈ idxs, e < 1296 := by decide +kernel

theorem valid_iff_mem_lt : ∀ e, e < 1296 → (Valid e ↔ e ∈ idxs) := by decide +kernel

theorem valid_iff_mem (e : ℕ) : Valid e ↔ e ∈ idxs := by
  by_cases h : e < 1296
  · exact valid_iff_mem_lt e h
  · constructor
    · intro hv
      exact absurd hv.1 h
    · intro hm
      exact absurd (idxs_lt e hm) h

theorem valid_zero : Valid 0 := by decide

theorem sdeg_lt {e : ℕ} (h : e < 1296) : sdeg e < 6 := by
  unfold sdeg
  omega

/-- A slot from its degree and its three digits. -/
theorem slot_decomp (e : ℕ) : e = 216 * sdeg e + (sa1 e + 6 * sa2 e + 36 * sa3 e)
    ∧ sa1 e < 6 ∧ sa2 e < 6 ∧ sa3 e < 6 := by
  unfold sdeg sa1 sa2 sa3
  omega

/-- The degree and the digits of a slot that is given by them. -/
theorem slot_of_digits (d a1 a2 a3 : ℕ) (h1 : a1 < 6) (h2 : a2 < 6) (h3 : a3 < 6) :
    sdeg (216 * d + (a1 + 6 * a2 + 36 * a3)) = d ∧ sa1 (216 * d + (a1 + 6 * a2 + 36 * a3)) = a1
      ∧ sa2 (216 * d + (a1 + 6 * a2 + 36 * a3)) = a2 ∧ sa3 (216 * d + (a1 + 6 * a2 + 36 * a3)) = a3 := by
  unfold sdeg sa1 sa2 sa3
  omega

/-- **The slot of a product.** -/
theorem valid_add {e1 e2 : ℕ} (h1 : Valid e1) (h2 : Valid e2) (h : sdeg e1 + sdeg e2 ≤ 5) :
    Valid (e1 + e2) ∧ sdeg (e1 + e2) = sdeg e1 + sdeg e2 ∧ sa1 (e1 + e2) = sa1 e1 + sa1 e2
      ∧ sa2 (e1 + e2) = sa2 e1 + sa2 e2 ∧ sa3 (e1 + e2) = sa3 e1 + sa3 e2 := by
  obtain ⟨d1, _, _, _⟩ := slot_decomp e1
  obtain ⟨d2, _, _, _⟩ := slot_decomp e2
  have v1 := h1.2
  have v2 := h2.2
  have hs : e1 + e2 = 216 * (sdeg e1 + sdeg e2)
      + ((sa1 e1 + sa1 e2) + 6 * (sa2 e1 + sa2 e2) + 36 * (sa3 e1 + sa3 e2)) := by omega
  obtain ⟨g0, g1, g2, g3⟩ := slot_of_digits (sdeg e1 + sdeg e2) (sa1 e1 + sa1 e2) (sa2 e1 + sa2 e2)
    (sa3 e1 + sa3 e2) (by omega) (by omega) (by omega)
  rw [← hs] at g0 g1 g2 g3
  refine ⟨⟨?_, ?_⟩, g0, g1, g2, g3⟩
  · omega
  · rw [g0, g1, g2, g3]
    omega

/-- Two valid slots whose sum is a slot have degrees that add up to at most 5. -/
theorem sdeg_add_le {e1 e2 : ℕ} (h : e1 + e2 < 1296) : sdeg e1 + sdeg e2 ≤ 5 := by
  unfold sdeg
  omega

/-- The monomial of a slot. -/
noncomputable def mval (e : ℕ) (x : Fin 4 → ℝ) : ℝ :=
  x 0 ^ (sdeg e - (sa1 e + sa2 e + sa3 e)) * x 1 ^ sa1 e * x 2 ^ sa2 e * x 3 ^ sa3 e

theorem mval_zero (x : Fin 4 → ℝ) : mval 0 x = 1 := by
  simp [mval, sdeg, sa1, sa2, sa3]

theorem mval_add (x : Fin 4 → ℝ) {e1 e2 : ℕ} (h1 : Valid e1) (h2 : Valid e2) (h : sdeg e1 + sdeg e2 ≤ 5) :
    mval (e1 + e2) x = mval e1 x * mval e2 x := by
  obtain ⟨_, hd, ha1, ha2, ha3⟩ := valid_add h1 h2 h
  have e0 : sdeg e1 + sdeg e2 - (sa1 e1 + sa1 e2 + (sa2 e1 + sa2 e2) + (sa3 e1 + sa3 e2))
      = (sdeg e1 - (sa1 e1 + sa2 e1 + sa3 e1)) + (sdeg e2 - (sa1 e2 + sa2 e2 + sa3 e2)) := by
    have := h1.2
    have := h2.2
    omega
  unfold mval
  rw [hd, ha1, ha2, ha3, e0, pow_add, pow_add, pow_add, pow_add]
  ring

theorem mval_abs_le (x : Fin 4 → ℝ) (m : ℝ) (hx : ∀ k, |x k| ≤ m) {e : ℕ} (he : Valid e) :
    |mval e x| ≤ m ^ sdeg e := by
  have hm : 0 ≤ m := le_trans (abs_nonneg _) (hx 0)
  have e0 : m ^ sdeg e
      = m ^ (sdeg e - (sa1 e + sa2 e + sa3 e)) * m ^ sa1 e * m ^ sa2 e * m ^ sa3 e := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    have := he.2
    omega
  unfold mval
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_pow, abs_pow, e0]
  gcongr <;> exact hx _

/-! ## Polynomials -/

/-- A sequence of coefficients vanishes outside the valid slots. -/
def Supp (c : ℕ → ℝ) : Prop := ∀ e, ¬ Valid e → c e = 0

/-- The value of the polynomial with the coefficients `c`. -/
noncomputable def pev (c : ℕ → ℝ) (x : Fin 4 → ℝ) : ℝ := ∑ e ∈ range 1296, c e * mval e x

/-- The part of degree `d`. -/
noncomputable def blk (c : ℕ → ℝ) (d : ℕ) (x : Fin 4 → ℝ) : ℝ :=
  ∑ e ∈ range 1296, if sdeg e = d then c e * mval e x else 0

/-- The sum of the absolute values of the coefficients of degree `d`. -/
noncomputable def nrm (c : ℕ → ℝ) (d : ℕ) : ℝ := ∑ e ∈ range 1296, if sdeg e = d then |c e| else 0

theorem nrm_nonneg (c : ℕ → ℝ) (d : ℕ) : 0 ≤ nrm c d :=
  sum_nonneg fun e _ => by
    split_ifs
    · exact abs_nonneg _
    · exact le_refl 0

/-- A sum over the slots, by degrees. -/
theorem sum_by_deg {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ e ∈ range 1296, f e = ∑ d ∈ range 6, ∑ e ∈ range 1296, if sdeg e = d then f e else 0 := by
  rw [Finset.sum_comm]
  refine sum_congr rfl fun e he => ?_
  rw [Finset.sum_ite_eq (range 6) (sdeg e), if_pos (mem_range.mpr (sdeg_lt (mem_range.mp he)))]

theorem pev_eq_blk (c : ℕ → ℝ) (x : Fin 4 → ℝ) : pev c x = ∑ d ∈ range 6, blk c d x :=
  sum_by_deg fun e => c e * mval e x

theorem blk_abs_le (c : ℕ → ℝ) (hc : Supp c) (d : ℕ) (x : Fin 4 → ℝ) (m : ℝ) (hx : ∀ k, |x k| ≤ m) :
    |blk c d x| ≤ nrm c d * m ^ d := by
  unfold blk nrm
  rw [Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (sum_le_sum fun e _ => ?_)
  by_cases h : sdeg e = d
  · rw [if_pos h, if_pos h]
    by_cases hv : Valid e
    · rw [abs_mul]
      have h1 := mval_abs_le x m hx hv
      rw [h] at h1
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    · rw [hc e hv]
      simp
  · rw [if_neg h, if_neg h]
    simp

/-- A double sum over the slots with a condition on the two degrees, by degrees. -/
theorem sum_by_deg2 (A B : ℕ → ℝ) (P : ℕ → ℕ → Prop) [DecidableRel P] :
    (∑ e1 ∈ range 1296, ∑ e2 ∈ range 1296, if P (sdeg e1) (sdeg e2) then A e1 * B e2 else 0)
      = ∑ d1 ∈ range 6, ∑ d2 ∈ range 6, if P d1 d2 then
          (∑ e ∈ range 1296, if sdeg e = d1 then A e else 0) * (∑ e ∈ range 1296, if sdeg e = d2 then B e else 0)
        else 0 := by
  -- the right side as a sum over the degrees and the slots
  have hR : ∀ d1 d2 : ℕ, (if P d1 d2 then
        (∑ e ∈ range 1296, if sdeg e = d1 then A e else 0) * (∑ e ∈ range 1296, if sdeg e = d2 then B e else 0)
      else 0)
      = ∑ e1 ∈ range 1296, ∑ e2 ∈ range 1296,
          if sdeg e1 = d1 then (if sdeg e2 = d2 then (if P d1 d2 then A e1 * B e2 else 0) else 0) else 0 := by
    intro d1 d2
    by_cases hP : P d1 d2
    · rw [if_pos hP, Finset.sum_mul_sum]
      refine sum_congr rfl fun e1 _ => sum_congr rfl fun e2 _ => ?_
      by_cases h1 : sdeg e1 = d1 <;> by_cases h2 : sdeg e2 = d2 <;> simp [h1, h2, hP]
    · rw [if_neg hP]
      symm
      refine sum_eq_zero fun e1 _ => sum_eq_zero fun e2 _ => ?_
      by_cases h1 : sdeg e1 = d1 <;> by_cases h2 : sdeg e2 = d2 <;> simp [h1, h2, hP]
  simp only [hR]
  -- the order of the sums: the slots first
  have hswap : (∑ d1 ∈ range 6, ∑ d2 ∈ range 6, ∑ e1 ∈ range 1296, ∑ e2 ∈ range 1296,
        if sdeg e1 = d1 then (if sdeg e2 = d2 then (if P d1 d2 then A e1 * B e2 else 0) else 0) else 0)
      = ∑ e1 ∈ range 1296, ∑ e2 ∈ range 1296, ∑ d1 ∈ range 6, ∑ d2 ∈ range 6,
        if sdeg e1 = d1 then (if sdeg e2 = d2 then (if P d1 d2 then A e1 * B e2 else 0) else 0) else 0 := by
    calc (∑ d1 ∈ range 6, ∑ d2 ∈ range 6, ∑ e1 ∈ range 1296, ∑ e2 ∈ range 1296,
          if sdeg e1 = d1 then (if sdeg e2 = d2 then (if P d1 d2 then A e1 * B e2 else 0) else 0) else 0)
        = ∑ d1 ∈ range 6, ∑ e1 ∈ range 1296, ∑ d2 ∈ range 6, ∑ e2 ∈ range 1296,
          if sdeg e1 = d1 then (if sdeg e2 = d2 then (if P d1 d2 then A e1 * B e2 else 0) else 0) else 0 :=
          sum_congr rfl fun d1 _ => Finset.sum_comm
      _ = ∑ e1 ∈ range 1296, ∑ d1 ∈ range 6, ∑ d2 ∈ range 6, ∑ e2 ∈ range 1296,
          if sdeg e1 = d1 then (if sdeg e2 = d2 then (if P d1 d2 then A e1 * B e2 else 0) else 0) else 0 :=
          Finset.sum_comm
      _ = ∑ e1 ∈ range 1296, ∑ d1 ∈ range 6, ∑ e2 ∈ range 1296, ∑ d2 ∈ range 6,
          if sdeg e1 = d1 then (if sdeg e2 = d2 then (if P d1 d2 then A e1 * B e2 else 0) else 0) else 0 :=
          sum_congr rfl fun e1 _ => sum_congr rfl fun d1 _ => Finset.sum_comm
      _ = ∑ e1 ∈ range 1296, ∑ e2 ∈ range 1296, ∑ d1 ∈ range 6, ∑ d2 ∈ range 6,
          if sdeg e1 = d1 then (if sdeg e2 = d2 then (if P d1 d2 then A e1 * B e2 else 0) else 0) else 0 :=
          sum_congr rfl fun e1 _ => Finset.sum_comm
  rw [hswap]
  refine sum_congr rfl fun e1 he1 => sum_congr rfl fun e2 he2 => ?_
  have h1 := mem_range.mpr (sdeg_lt (mem_range.mp he1))
  have h2 := mem_range.mpr (sdeg_lt (mem_range.mp he2))
  have inner : ∀ d1 : ℕ, (∑ d2 ∈ range 6,
        if sdeg e1 = d1 then (if sdeg e2 = d2 then (if P d1 d2 then A e1 * B e2 else 0) else 0) else 0)
      = if sdeg e1 = d1 then (if P d1 (sdeg e2) then A e1 * B e2 else 0) else 0 := by
    intro d1
    by_cases h : sdeg e1 = d1
    · simp only [if_pos h]
      rw [Finset.sum_ite_eq (range 6) (sdeg e2), if_pos h2]
    · simp only [if_neg h]
      exact Finset.sum_const_zero
  rw [Finset.sum_congr rfl (fun d1 _ => inner d1), Finset.sum_ite_eq (range 6) (sdeg e1), if_pos h1]

/-- The product of two sequences: the convolution on the slots. -/
noncomputable def cmul (c c' : ℕ → ℝ) : ℕ → ℝ :=
  fun e => if e < 1296 then ∑ i ∈ range (e + 1), c i * c' (e - i) else 0

theorem cmul_supp (c c' : ℕ → ℝ) (hc : Supp c) (hc' : Supp c') : Supp (cmul c c') := by
  intro e he
  unfold cmul
  by_cases h : e < 1296
  · rw [if_pos h]
    refine sum_eq_zero fun i hi => ?_
    have hi' : i ≤ e := by
      have := mem_range.mp hi
      omega
    by_cases h1 : Valid i
    · by_cases h2 : Valid (e - i)
      · have hs : sdeg i + sdeg (e - i) ≤ 5 := sdeg_add_le (by omega)
        have hv := (valid_add h1 h2 hs).1
        rw [show i + (e - i) = e by omega] at hv
        exact absurd hv he
      · rw [hc' _ h2, mul_zero]
    · rw [hc _ h1, zero_mul]
  · rw [if_neg h]

/-- **The product of two polynomials**: the polynomial of the convolution, plus the products of the parts whose
degrees add up to at least 6. -/
theorem pev_mul (c c' : ℕ → ℝ) (hc : Supp c) (hc' : Supp c') (x : Fin 4 → ℝ) :
    pev c x * pev c' x - pev (cmul c c') x
      = ∑ d1 ∈ range 6, ∑ d2 ∈ range 6, if 6 ≤ d1 + d2 then blk c d1 x * blk c' d2 x else 0 := by
  -- the product of the values as a double sum
  have hprod : pev c x * pev c' x
      = ∑ e1 ∈ range 1296, ∑ e2 ∈ range 1296, (c e1 * mval e1 x) * (c' e2 * mval e2 x) := by
    unfold pev
    rw [Finset.sum_mul_sum]
  -- the polynomial of the convolution as a double sum
  have hconv : pev (cmul c c') x
      = ∑ e1 ∈ range 1296, ∑ e2 ∈ range 1296,
          if sdeg e1 + sdeg e2 ≤ 5 then (c e1 * mval e1 x) * (c' e2 * mval e2 x) else 0 := by
    have h1 : pev (cmul c c') x
        = ∑ e ∈ range 1296, ∑ i ∈ range (e + 1), c i * c' (e - i) * mval (i + (e - i)) x := by
      unfold pev cmul
      refine sum_congr rfl fun e he => ?_
      rw [if_pos (mem_range.mp he), Finset.sum_mul]
      refine sum_congr rfl fun i hi => ?_
      have : i + (e - i) = e := by
        have := mem_range.mp hi
        omega
      rw [this]
    have h2 := Finset.sum_range_diag_flip 1296 (fun i j => c i * c' j * mval (i + j) x)
    rw [h1, h2]
    refine sum_congr rfl fun e1 he1 => ?_
    have he1' := mem_range.mp he1
    -- the inner sum over the slots below `1296 - e1`, as a sum over all slots with a condition
    have h3 : ∑ k ∈ range (1296 - e1), c e1 * c' k * mval (e1 + k) x
        = ∑ e2 ∈ range 1296, if e2 < 1296 - e1 then c e1 * c' e2 * mval (e1 + e2) x else 0 := by
      rw [← Finset.sum_filter]
      refine sum_congr ?_ fun _ _ => rfl
      ext k
      simp only [mem_range, mem_filter]
      omega
    rw [h3]
    refine sum_congr rfl fun e2 he2 => ?_
    have he2' := mem_range.mp he2
    by_cases hv1 : Valid e1
    · by_cases hv2 : Valid e2
      · by_cases hs : sdeg e1 + sdeg e2 ≤ 5
        · have hlt : e2 < 1296 - e1 := by
            have := (valid_add hv1 hv2 hs).1.1
            omega
          rw [if_pos hlt, if_pos hs, mval_add x hv1 hv2 hs]
          ring
        · have hge : ¬ e2 < 1296 - e1 := fun hlt => hs (sdeg_add_le (by omega))
          rw [if_neg hge, if_neg hs]
      · rw [hc' e2 hv2]
        simp
    · rw [hc e1 hv1]
      simp
  rw [hprod, hconv, ← Finset.sum_sub_distrib]
  have hdiff : ∀ e1 ∈ range 1296, (∑ e2 ∈ range 1296, (c e1 * mval e1 x) * (c' e2 * mval e2 x))
      - (∑ e2 ∈ range 1296, if sdeg e1 + sdeg e2 ≤ 5 then (c e1 * mval e1 x) * (c' e2 * mval e2 x) else 0)
      = ∑ e2 ∈ range 1296, if 6 ≤ sdeg e1 + sdeg e2 then (c e1 * mval e1 x) * (c' e2 * mval e2 x) else 0 := by
    intro e1 _
    rw [← Finset.sum_sub_distrib]
    refine sum_congr rfl fun e2 _ => ?_
    by_cases hs : sdeg e1 + sdeg e2 ≤ 5
    · rw [if_pos hs, if_neg (by omega), sub_self]
    · rw [if_neg hs, if_pos (by omega), sub_zero]
  rw [Finset.sum_congr rfl hdiff]
  exact sum_by_deg2 (fun e => c e * mval e x) (fun e => c' e * mval e x) (fun d1 d2 => 6 ≤ d1 + d2)

end N14.Jet

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination

/-!
# Schema S2, the bound: sums over triples of points

The three-point bound is obtained by summing the identity of a certificate over all triples of
distinct points of a configuration. This file contains the part of the argument that does not
depend on the sphere. Let `a i j` be a symmetric array with `a i i = 1` (the inner products of the
points), and let `M`, `G`, `H` be real functions and `x0`, `c` real numbers. With

  `Z (u, v, t) = (n - 1) (9 (n - 2) M (u, v, t) + G (u, v, t))
      + 9 (n - 1) (M (u, u, 1) + M (u, 1, u) + M (1, u, u)) + 9 x0 - 9 (n - 1) H u + 9 (n - 1) c`,

where `n` is the number of points, suppose that

* the sum of `Z` over the six permutations of its arguments vanishes (the identity);
* `∑ j k, M (a i j, a i k, a j k) ≥ 0` for every `i` (the kernels are positive definite);
* `G ≥ 0` at the triples `(a i j, a i k, a j k)` (sums of squares with nonnegative weights);
* `M (1, 1, 1) = x0`.

Then `n (n - 1) c ≤ ∑_{i ≠ j} H (a i j)` (`three_point_sum`).

The sum of `M` over all triples splits into the triples of distinct indices, the triples with two
equal indices, which give the three terms `M (u, u, 1)`, `M (u, 1, u)`, `M (1, u, u)`, and the
triples with three equal indices (`sum3_split`). The sum of a function over the triples of distinct
indices does not change if its arguments are permuted (`sum3_six`).
-/

@[expose] public section

namespace CAP.ThreePoint

open Finset

section triples

variable {ι : Type*}

/-- The three indices are distinct. -/
def Distinct3 (i j k : ι) : Prop := i ≠ j ∧ i ≠ k ∧ j ≠ k

instance [DecidableEq ι] (i j k : ι) : Decidable (Distinct3 i j k) :=
  inferInstanceAs (Decidable (i ≠ j ∧ i ≠ k ∧ j ≠ k))

theorem distinct3_swap12 (i j k : ι) : Distinct3 j i k ↔ Distinct3 i j k :=
  ⟨fun ⟨h1, h2, h3⟩ => ⟨h1.symm, h3, h2⟩, fun ⟨h1, h2, h3⟩ => ⟨h1.symm, h3, h2⟩⟩

theorem distinct3_swap23 (i j k : ι) : Distinct3 i k j ↔ Distinct3 i j k :=
  ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3.symm⟩, fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3.symm⟩⟩

section sums

variable [Fintype ι]

/-- The sum over all triples of indices. -/
def sum3 (F : ι → ι → ι → ℝ) : ℝ := ∑ i, ∑ j, ∑ k, F i j k

theorem sum3_congr {F G : ι → ι → ι → ℝ} (h : ∀ i j k, F i j k = G i j k) : sum3 F = sum3 G :=
  sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => h i j k

theorem sum3_add (F G : ι → ι → ι → ℝ) : sum3 (fun i j k => F i j k + G i j k) = sum3 F + sum3 G := by
  simp only [sum3, sum_add_distrib]

theorem sum3_smul (c : ℝ) (F : ι → ι → ι → ℝ) : sum3 (fun i j k => c * F i j k) = c * sum3 F := by
  simp only [sum3, mul_sum]

theorem sum3_nonneg {F : ι → ι → ι → ℝ} (h : ∀ i j k, 0 ≤ F i j k) : 0 ≤ sum3 F :=
  sum_nonneg fun i _ => sum_nonneg fun j _ => sum_nonneg fun k _ => h i j k

theorem sum3_swap12 (F : ι → ι → ι → ℝ) : sum3 (fun i j k => F j i k) = sum3 F := by
  unfold sum3
  exact sum_comm

theorem sum3_swap23 (F : ι → ι → ι → ℝ) : sum3 (fun i j k => F i k j) = sum3 F := by
  unfold sum3
  exact sum_congr rfl fun _ _ => sum_comm

theorem sum3_perm231 (F : ι → ι → ι → ℝ) : sum3 (fun i j k => F j k i) = sum3 F :=
  (sum3_swap12 (fun i j k => F i k j)).trans (sum3_swap23 F)

theorem sum3_perm312 (F : ι → ι → ι → ℝ) : sum3 (fun i j k => F k i j) = sum3 F :=
  (sum3_swap23 (fun i j k => F j i k)).trans (sum3_swap12 F)

theorem sum3_perm321 (F : ι → ι → ι → ℝ) : sum3 (fun i j k => F k j i) = sum3 F :=
  (sum3_swap23 (fun i j k => F j k i)).trans (sum3_perm231 F)

end sums

/-! ## The triples with equal indices -/

theorem split_pointwise [DecidableEq ι] (F : ι → ι → ι → ℝ) (i j k : ι) :
    F i j k = (if Distinct3 i j k then F i j k else 0)
      + (if j = k then (if i ≠ j then F i j k else 0) else 0)
      + (if i = j then (if i ≠ k then F i j k else 0) else 0)
      + (if i = k then (if i ≠ j then F i j k else 0) else 0)
      + (if j = k then (if i = j then F i j k else 0) else 0) := by
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : i = k
    · subst h2
      simp [Distinct3]
    · simp [Distinct3, h2]
  · by_cases h2 : i = k
    · subst h2
      have h3 : ¬ j = i := fun h => h1 h.symm
      simp [Distinct3, h1, h3]
    · by_cases h3 : j = k
      · subst h3
        simp [Distinct3, h1]
      · simp [Distinct3, h1, h2, h3]

variable [Fintype ι] [DecidableEq ι]

/-- The sum over all triples: distinct indices, two equal indices (three cases), three equal
indices. -/
theorem sum3_split (F : ι → ι → ι → ℝ) :
    sum3 F = sum3 (fun i j k => if Distinct3 i j k then F i j k else 0)
      + (∑ i, ∑ j, if i ≠ j then F i j j else 0) + (∑ i, ∑ k, if i ≠ k then F i i k else 0)
      + (∑ i, ∑ j, if i ≠ j then F i j i else 0) + ∑ i, F i i i := by
  have e2 : (∑ i, ∑ j, ∑ k, if j = k then (if i ≠ j then F i j k else 0) else 0)
      = ∑ i, ∑ j, if i ≠ j then F i j j else 0 := by
    simp only [sum_ite_eq, mem_univ, if_true]
  have e3 : (∑ i, ∑ j, ∑ k, if i = j then (if i ≠ k then F i j k else 0) else 0)
      = ∑ i, ∑ k, if i ≠ k then F i i k else 0 := by
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comm]
    simp only [sum_ite_eq, mem_univ, if_true]
  have e4 : (∑ i, ∑ j, ∑ k, if i = k then (if i ≠ j then F i j k else 0) else 0)
      = ∑ i, ∑ j, if i ≠ j then F i j i else 0 := by
    simp only [sum_ite_eq, mem_univ, if_true]
  have e5 : (∑ i, ∑ j, ∑ k, if j = k then (if i = j then F i j k else 0) else 0) = ∑ i, F i i i := by
    simp only [sum_ite_eq, mem_univ, if_true]
  rw [← e2, ← e3, ← e4, ← e5]
  unfold sum3
  simp only [← sum_add_distrib]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => split_pointwise F i j k

/-! ## Functions of two indices -/

theorem card_ne_ne {i j : ι} (h : i ≠ j) :
    ((univ.filter fun k => i ≠ k ∧ j ≠ k).card : ℝ) = (Fintype.card ι : ℝ) - 2 := by
  have e : (univ.filter fun k => i ≠ k ∧ j ≠ k) = (univ.erase i).erase j := by
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h2 h.symm, fun h => h1 h.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h2 h.symm, fun h => h1 h.symm⟩
  have hj : j ∈ univ.erase i := mem_erase.mpr ⟨h.symm, mem_univ j⟩
  have h2 : 2 ≤ Fintype.card ι := Fintype.one_lt_card_iff.mpr ⟨i, j, h⟩
  have h3 : Fintype.card ι - 1 - 1 = Fintype.card ι - 2 := by omega
  rw [e, card_erase_of_mem hj, card_erase_of_mem (mem_univ i), card_univ, h3, Nat.cast_sub h2]
  norm_num

/-- A function of the first two indices, summed over the triples of distinct indices. -/
theorem sum3_pairs (g : ι → ι → ℝ) :
    sum3 (fun i j k => if Distinct3 i j k then g i j else 0)
      = ((Fintype.card ι : ℝ) - 2) * ∑ i, ∑ j, if i ≠ j then g i j else 0 := by
  unfold sum3
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  by_cases h : i = j
  · subst h
    simp [Distinct3]
  · rw [if_pos h]
    have e : ∀ k, (if Distinct3 i j k then g i j else 0) = if (i ≠ k ∧ j ≠ k) then g i j else 0 := fun k =>
      if_congr ⟨fun ⟨_, h2, h3⟩ => ⟨h2, h3⟩, fun ⟨h2, h3⟩ => ⟨h, h2, h3⟩⟩ rfl rfl
    rw [sum_congr rfl fun k _ => e k, ← sum_filter, sum_const, nsmul_eq_mul, card_ne_ne h]

/-- The number of pairs of distinct indices. -/
theorem sum_ne_one :
    (∑ i : ι, ∑ j : ι, if i ≠ j then (1 : ℝ) else 0) = (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) := by
  have h : ∀ i : ι, (∑ j : ι, if i ≠ j then (1 : ℝ) else 0) = (Fintype.card ι : ℝ) - 1 := by
    intro i
    have h1 : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, filter_ne, card_erase_of_mem (mem_univ i), card_univ,
      Nat.cast_sub h1, Nat.cast_one]
  rw [sum_congr rfl fun i _ => h i, sum_const, card_univ, nsmul_eq_mul]

/-! ## The permutations of the arguments -/

/-- The values of a function at the triples `(a i j, a i k, a j k)` with distinct indices. -/
def onT (a : ι → ι → ℝ) (Z : ℝ → ℝ → ℝ → ℝ) (i j k : ι) : ℝ :=
  if Distinct3 i j k then Z (a i j) (a i k) (a j k) else 0

/-- If the sum of `Z` over the six permutations of its arguments vanishes, then the sum of `Z` over
the triples of distinct indices vanishes. -/
theorem sum3_six (a : ι → ι → ℝ) (ha : ∀ i j, a i j = a j i) (Z : ℝ → ℝ → ℝ → ℝ)
    (hid : ∀ u v t, Z u v t + Z u t v + Z v u t + Z v t u + Z t u v + Z t v u = 0) :
    sum3 (onT a Z) = 0 := by
  have e2 : sum3 (fun i j k => if Distinct3 i j k then Z (a i j) (a j k) (a i k) else 0) = sum3 (onT a Z) :=
    (sum3_congr fun i j k => (show _ = onT a Z j i k from
      if_congr (distinct3_swap12 i j k).symm (by rw [ha j i]) rfl)).trans (sum3_swap12 (onT a Z))
  have e3 : sum3 (fun i j k => if Distinct3 i j k then Z (a i k) (a i j) (a j k) else 0) = sum3 (onT a Z) :=
    (sum3_congr fun i j k => (show _ = onT a Z i k j from
      if_congr (distinct3_swap23 i j k).symm (by rw [ha k j]) rfl)).trans (sum3_swap23 (onT a Z))
  have e4 : sum3 (fun i j k => if Distinct3 i j k then Z (a i k) (a j k) (a i j) else 0) = sum3 (onT a Z) :=
    (sum3_congr fun i j k => (show _ = onT a Z k i j from
      if_congr ((distinct3_swap12 i k j).trans (distinct3_swap23 i j k)).symm (by rw [ha k i, ha k j]) rfl)).trans
      (sum3_perm312 (onT a Z))
  have e5 : sum3 (fun i j k => if Distinct3 i j k then Z (a j k) (a i j) (a i k) else 0) = sum3 (onT a Z) :=
    (sum3_congr fun i j k => (show _ = onT a Z j k i from
      if_congr ((distinct3_swap23 j i k).trans (distinct3_swap12 i j k)).symm (by rw [ha j i, ha k i]) rfl)).trans
      (sum3_perm231 (onT a Z))
  have e6 : sum3 (fun i j k => if Distinct3 i j k then Z (a j k) (a i k) (a i j) else 0) = sum3 (onT a Z) :=
    (sum3_congr fun i j k => (show _ = onT a Z k j i from
      if_congr ((distinct3_swap12 j k i).trans ((distinct3_swap23 j i k).trans (distinct3_swap12 i j k))).symm
        (by rw [ha k j, ha k i, ha j i]) rfl)).trans (sum3_perm321 (onT a Z))
  have hz : sum3 (onT a Z)
      + sum3 (fun i j k => if Distinct3 i j k then Z (a i j) (a j k) (a i k) else 0)
      + sum3 (fun i j k => if Distinct3 i j k then Z (a i k) (a i j) (a j k) else 0)
      + sum3 (fun i j k => if Distinct3 i j k then Z (a i k) (a j k) (a i j) else 0)
      + sum3 (fun i j k => if Distinct3 i j k then Z (a j k) (a i j) (a i k) else 0)
      + sum3 (fun i j k => if Distinct3 i j k then Z (a j k) (a i k) (a i j) else 0) = 0 := by
    rw [← sum3_add, ← sum3_add, ← sum3_add, ← sum3_add, ← sum3_add]
    unfold sum3
    refine sum_eq_zero fun i _ => sum_eq_zero fun j _ => sum_eq_zero fun k _ => ?_
    by_cases h : Distinct3 i j k
    · simp only [onT, if_pos h]
      exact hid _ _ _
    · simp only [onT, if_neg h, add_zero]
  rw [e2, e3, e4, e5, e6] at hz
  linarith

/-! ## The bound -/

/-- The function `Z` of the identity, for real functions in the places of the polynomials. -/
def Zf (n : ℝ) (M G : ℝ → ℝ → ℝ → ℝ) (H : ℝ → ℝ) (x0 c : ℝ) (u v t : ℝ) : ℝ :=
  (n - 1) * (9 * (n - 2) * M u v t + G u v t) + 9 * (n - 1) * (M u u 1 + M u 1 u + M 1 u u) + 9 * x0
    - 9 * (n - 1) * H u + 9 * (n - 1) * c

/-- **The three-point bound, without the sphere.** See the head of this file. -/
theorem three_point_sum (a : ι → ι → ℝ) (ha : ∀ i j, a i j = a j i) (ha1 : ∀ i, a i i = 1)
    (M G : ℝ → ℝ → ℝ → ℝ) (H : ℝ → ℝ) (x0 c : ℝ) (hn : 3 ≤ Fintype.card ι)
    (hid : ∀ u v t, Zf (Fintype.card ι) M G H x0 c u v t + Zf (Fintype.card ι) M G H x0 c u t v
      + Zf (Fintype.card ι) M G H x0 c v u t + Zf (Fintype.card ι) M G H x0 c v t u
      + Zf (Fintype.card ι) M G H x0 c t u v + Zf (Fintype.card ι) M G H x0 c t v u = 0)
    (hM : ∀ i, 0 ≤ ∑ j, ∑ k, M (a i j) (a i k) (a j k))
    (hG : ∀ i j k, 0 ≤ G (a i j) (a i k) (a j k))
    (hx0 : M 1 1 1 = x0) :
    (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * c ≤ ∑ i, ∑ j, if i ≠ j then H (a i j) else 0 := by
  have hn3 : (3 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hn
  have h0 := sum3_six a ha (Zf (Fintype.card ι) M G H x0 c) hid
  -- the sum of `Z` over the triples of distinct indices, part by part
  have hp : ∀ i j k, onT a (Zf (Fintype.card ι) M G H x0 c) i j k
      = 9 * ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * onT a M i j k
        + ((Fintype.card ι : ℝ) - 1) * onT a G i j k
        + 9 * ((Fintype.card ι : ℝ) - 1) * (if Distinct3 i j k then M (a i j) (a i j) 1 else 0)
        + 9 * ((Fintype.card ι : ℝ) - 1) * (if Distinct3 i j k then M (a i j) 1 (a i j) else 0)
        + 9 * ((Fintype.card ι : ℝ) - 1) * (if Distinct3 i j k then M 1 (a i j) (a i j) else 0)
        + 9 * x0 * (if Distinct3 i j k then (1 : ℝ) else 0)
        + (-(9 * ((Fintype.card ι : ℝ) - 1))) * (if Distinct3 i j k then H (a i j) else 0)
        + 9 * ((Fintype.card ι : ℝ) - 1) * c * (if Distinct3 i j k then (1 : ℝ) else 0) := by
    intro i j k
    unfold onT Zf
    split_ifs <;> ring
  have hexp := sum3_congr hp
  rw [h0, sum3_add, sum3_add, sum3_add, sum3_add, sum3_add, sum3_add, sum3_add, sum3_smul, sum3_smul, sum3_smul,
    sum3_smul, sum3_smul, sum3_smul, sum3_smul, sum3_smul, sum3_pairs, sum3_pairs, sum3_pairs, sum3_pairs,
    sum3_pairs, sum_ne_one] at hexp
  -- the sum of `M` over all triples
  have hsplit := sum3_split (fun i j k => M (a i j) (a i k) (a j k))
  simp only [ha1] at hsplit
  have e2 : (∑ i, ∑ j, if i ≠ j then M (a i j) 1 (a j i) else 0)
      = ∑ i, ∑ j, if i ≠ j then M (a i j) 1 (a i j) else 0 :=
    sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [ha j i]
  rw [e2, hx0, sum_const, card_univ, nsmul_eq_mul] at hsplit
  have hall : 0 ≤ sum3 (fun i j k => M (a i j) (a i k) (a j k)) := sum_nonneg fun i _ => hM i
  have hSG : 0 ≤ sum3 (onT a G) := sum3_nonneg fun i j k => by
    unfold onT
    split_ifs
    · exact hG i j k
    · exact le_refl 0
  have hSM : sum3 (fun i j k => if Distinct3 i j k then M (a i j) (a i k) (a j k) else 0) = sum3 (onT a M) := rfl
  rw [hSM] at hsplit
  have h1 : 0 < (Fintype.card ι : ℝ) - 1 := by linarith
  have h2 : 0 < (Fintype.card ι : ℝ) - 2 := by linarith
  have hpos : 0 < 9 * ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) :=
    mul_pos (mul_pos (by norm_num) h1) h2
  have key : 9 * ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2)
      * ((∑ i, ∑ j, if i ≠ j then H (a i j) else 0) - (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * c)
      = 9 * ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * sum3 (fun i j k => M (a i j) (a i k) (a j k))
        + ((Fintype.card ι : ℝ) - 1) * sum3 (onT a G) := by
    linear_combination hexp - 9 * ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * hsplit
  have hrhs : 0 ≤ 9 * ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2)
      * ((∑ i, ∑ j, if i ≠ j then H (a i j) else 0) - (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * c) := by
    rw [key]
    exact add_nonneg (mul_nonneg hpos.le hall) (mul_nonneg h1.le hSG)
  have := (mul_nonneg_iff_of_pos_left hpos).mp hrhs
  linarith

end triples

/-- The sum of a symmetric function over the pairs of distinct indices is twice its sum over the
pairs `i < j`. -/
theorem sum_ne_eq_two_mul_sum_lt {n : ℕ} (g : Fin n → Fin n → ℝ) (hg : ∀ i j, g i j = g j i) :
    (∑ i, ∑ j, if i ≠ j then g i j else 0) = 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), g i j := by
  have hp : ∀ i j : Fin n, (if i ≠ j then g i j else 0)
      = (if i < j then g i j else 0) + (if j < i then g j i else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · rw [if_pos h.ne, if_pos h, if_neg h.asymm, add_zero]
    · subst h
      simp
    · rw [if_pos h.ne', if_neg h.asymm, if_pos h, zero_add, hg i j]
  have e : (∑ i : Fin n, ∑ j : Fin n, if j < i then g j i else 0)
      = ∑ i : Fin n, ∑ j : Fin n, if i < j then g i j else 0 := sum_comm
  rw [sum_congr rfl fun i _ => sum_congr rfl fun j _ => hp i j]
  simp only [sum_add_distrib]
  rw [e]
  simp only [sum_filter]
  ring

end CAP.ThreePoint

module

public import CAP.Schema.ThreePoint.Triples

/-!
# T7, the energy identity: sums over triples of points

**Lemma** (`triple_identity`). Let `M i j k` and `p i j k` be real numbers for all triples of indices of a finite
set, and let `g i j` be real numbers with

  `3 * ∑_{k ≠ i, j} p i j k + 12 * (M i j j + M i i j + M i j i) = g i j`   for `i ≠ j`.

Then the sum over the triples of distinct indices of

  `p i j k + p i k j + p j k i - 2 * (M i j k + M i k j + M j i k + M j k i + M k i j + M k j i)`

plus `12 * ∑ i j k, M i j k` equals `∑_{i ≠ j} g i j + 12 * ∑ i, M i i i`.

In the application `M i j k` is the value of the kernel rooted at the point `i` at the points `j`, `k`, the number
`p i j k` is the share that the pair `i`, `j` gives to the third point `k`, and the first sum is the sum of the
slacks over the ordered triples. No property of the points is used here.
-/

@[expose] public section

namespace N14.Energy

open Finset CAP.ThreePoint

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sum over the triples of distinct indices. -/
def dsum (F : ι → ι → ι → ℝ) : ℝ := sum3 (fun i j k => if Distinct3 i j k then F i j k else 0)

theorem dsum_add (F G : ι → ι → ι → ℝ) : dsum (fun i j k => F i j k + G i j k) = dsum F + dsum G := by
  unfold dsum
  rw [← sum3_add]
  exact sum3_congr fun i j k => by split_ifs <;> simp

theorem dsum_smul (c : ℝ) (F : ι → ι → ι → ℝ) : dsum (fun i j k => c * F i j k) = c * dsum F := by
  unfold dsum
  rw [← sum3_smul]
  exact sum3_congr fun i j k => by split_ifs <;> simp

theorem dsum_swap23 (F : ι → ι → ι → ℝ) : dsum (fun i j k => F i k j) = dsum F :=
  (sum3_congr fun i j k => (show (if Distinct3 i j k then F i k j else 0)
      = (fun i j k => if Distinct3 i j k then F i j k else 0) i k j from
    if_congr (distinct3_swap23 i j k).symm rfl rfl)).trans
    (sum3_swap23 (fun i j k => if Distinct3 i j k then F i j k else 0))

theorem dsum_swap12 (F : ι → ι → ι → ℝ) : dsum (fun i j k => F j i k) = dsum F :=
  (sum3_congr fun i j k => (show (if Distinct3 i j k then F j i k else 0)
      = (fun i j k => if Distinct3 i j k then F i j k else 0) j i k from
    if_congr (distinct3_swap12 i j k).symm rfl rfl)).trans
    (sum3_swap12 (fun i j k => if Distinct3 i j k then F i j k else 0))

theorem dsum_perm231 (F : ι → ι → ι → ℝ) : dsum (fun i j k => F j k i) = dsum F :=
  (dsum_swap12 (fun i j k => F i k j)).trans (dsum_swap23 F)

theorem dsum_perm312 (F : ι → ι → ι → ℝ) : dsum (fun i j k => F k i j) = dsum F :=
  (dsum_swap23 (fun i j k => F j i k)).trans (dsum_swap12 F)

theorem dsum_perm321 (F : ι → ι → ι → ℝ) : dsum (fun i j k => F k j i) = dsum F :=
  (dsum_swap23 (fun i j k => F j k i)).trans (dsum_perm231 F)

/-- The sum over the triples of distinct indices, with the sum over the third index inside. -/
theorem dsum_pairs (p : ι → ι → ι → ℝ) :
    dsum p = ∑ i, ∑ j, if i ≠ j then ∑ k, (if i ≠ k ∧ j ≠ k then p i j k else 0) else 0 := by
  unfold dsum sum3
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  by_cases h : i = j
  · subst h
    rw [if_neg (fun h => h rfl)]
    exact sum_eq_zero fun k _ => if_neg fun hd => hd.1 rfl
  · rw [if_pos h]
    exact sum_congr rfl fun k _ =>
      if_congr ⟨fun ⟨_, h2, h3⟩ => ⟨h2, h3⟩, fun ⟨h2, h3⟩ => ⟨h, h2, h3⟩⟩ rfl rfl

/-- **The identity of the sums over triples.** See the head of this file. -/
theorem triple_identity (M p : ι → ι → ι → ℝ) (g : ι → ι → ℝ)
    (h2 : ∀ i j, i ≠ j → 3 * (∑ k, if i ≠ k ∧ j ≠ k then p i j k else 0)
        + 12 * (M i j j + M i i j + M i j i) = g i j) :
    dsum (fun i j k => p i j k + p i k j + p j k i
        + (-2) * (M i j k + M i k j + M j i k + M j k i + M k i j + M k j i))
      + 12 * sum3 M = (∑ i, ∑ j, if i ≠ j then g i j else 0) + 12 * ∑ i, M i i i := by
  -- the sum of the slacks
  have e1 : dsum (fun i j k => p i j k + p i k j + p j k i
        + (-2) * (M i j k + M i k j + M j i k + M j k i + M k i j + M k j i))
      = 3 * dsum p + (-12) * dsum M := by
    rw [dsum_add (fun i j k => p i j k + p i k j + p j k i)
        (fun i j k => (-2) * (M i j k + M i k j + M j i k + M j k i + M k i j + M k j i)),
      dsum_add (fun i j k => p i j k + p i k j) (fun i j k => p j k i),
      dsum_add (fun i j k => p i j k) (fun i j k => p i k j),
      dsum_smul (-2) (fun i j k => M i j k + M i k j + M j i k + M j k i + M k i j + M k j i),
      dsum_add (fun i j k => M i j k + M i k j + M j i k + M j k i + M k i j) (fun i j k => M k j i),
      dsum_add (fun i j k => M i j k + M i k j + M j i k + M j k i) (fun i j k => M k i j),
      dsum_add (fun i j k => M i j k + M i k j + M j i k) (fun i j k => M j k i),
      dsum_add (fun i j k => M i j k + M i k j) (fun i j k => M j i k),
      dsum_add (fun i j k => M i j k) (fun i j k => M i k j),
      dsum_swap23 p, dsum_perm231 p, dsum_swap23 M, dsum_swap12 M, dsum_perm231 M, dsum_perm312 M,
      dsum_perm321 M]
    ring
  -- the pairs
  have e2 : 3 * dsum p + 12 * ((∑ i, ∑ j, if i ≠ j then M i j j else 0) + (∑ i, ∑ k, if i ≠ k then M i i k else 0)
      + ∑ i, ∑ j, if i ≠ j then M i j i else 0) = ∑ i, ∑ j, if i ≠ j then g i j else 0 := by
    rw [dsum_pairs, ← sum_add_distrib, ← sum_add_distrib, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib, ← sum_add_distrib, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    by_cases h : i = j
    · subst h
      simp
    · rw [if_pos h, if_pos h, if_pos h, if_pos h, if_pos h, ← h2 i j h]
  have e3 := sum3_split M
  have e4 : dsum M = sum3 (fun i j k => if Distinct3 i j k then M i j k else 0) := rfl
  rw [e1, ← e2, e4]
  linarith

end N14.Energy

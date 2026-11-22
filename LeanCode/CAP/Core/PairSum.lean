module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Real.Basic

/-!
# Sums over the pairs `i < j`

`sum_fin_pairs`: a sum over the pairs `i < j` of `Fin n` is a sum over the pairs `i < j` of natural numbers
below `n`.
-/

@[expose] public section

namespace CAP

open Finset

/-- A sum over the pairs `i < j` of `Fin n`, as a sum over natural numbers. -/
theorem sum_fin_pairs (n : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ i : Fin n, ∑ j ∈ univ.filter (fun j : Fin n => i < j), g i j = ∑ j ∈ range n, ∑ i ∈ range j, g i j := by
  have h1 : ∀ i : Fin n, ∑ j ∈ univ.filter (fun j : Fin n => i < j), g i j
      = ∑ j ∈ range n, if (i : ℕ) < j then g i j else 0 := by
    intro i
    rw [Finset.sum_filter]
    exact Fin.sum_univ_eq_sum_range (fun j => if (i : ℕ) < j then g i j else 0) n
  calc ∑ i : Fin n, ∑ j ∈ univ.filter (fun j : Fin n => i < j), g i j
      = ∑ i : Fin n, ∑ j ∈ range n, if (i : ℕ) < j then g i j else 0 := Finset.sum_congr rfl fun i _ => h1 i
    _ = ∑ i ∈ range n, ∑ j ∈ range n, if i < j then g i j else 0 :=
      Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range n, if i < j then g i j else 0) n
    _ = ∑ j ∈ range n, ∑ i ∈ range n, if i < j then g i j else 0 := Finset.sum_comm
    _ = ∑ j ∈ range n, ∑ i ∈ range j, g i j := Finset.sum_congr rfl fun j hj => by
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      have := Finset.mem_range.1 hj
      omega

end CAP

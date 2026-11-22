module

public import N14.Candidate
public import N14.Energy.Untyped

/-!
# The theorem for 14 points: configurations in coordinates and in Euclidean space

The statement (`N14/Statement.lean`) uses coordinates: a configuration is a function `x : Fin N → Fin 3 → ℝ`,
its energy is `energy x`, and its points lie on the sphere if `OnSphere x`. The theorems of the certificates
(`N14/Energy/`) use points of `EuclideanSpace ℝ (Fin 3)` with their norm, inner product and distance. This
file relates the two forms.

* `pt x i`: the point of Euclidean space with the coordinates `x i`;
* `dot x i j`: the inner product `∑ k, x i k * x j k`; `ip_pt`: it is the inner product of `pt x i`, `pt x j`;
* `onSphere_iff`, `injective_pt`, `energy_eq`: the hypotheses and the energy in the two forms;
* `pcS`, `ipc`, `dot_X14`: the inner product of two points of `X14 h`, for both orders of the points;
* `exists_min_pair`: a pair of distinct points with the smallest inner product.
-/

@[expose] public section

namespace N14

open Finset N14.Energy

/-- The points of Euclidean space with the coordinates of a configuration. -/
noncomputable def pt {N : ℕ} (x : Fin N → Fin 3 → ℝ) (i : Fin N) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (x i)

/-- The inner product of two points of a configuration. -/
def dot {N : ℕ} (x : Fin N → Fin 3 → ℝ) (i j : Fin N) : ℝ := ∑ k, x i k * x j k

theorem dot_comm {N : ℕ} (x : Fin N → Fin 3 → ℝ) (i j : Fin N) : dot x i j = dot x j i := by
  unfold dot
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem ip_pt {N : ℕ} (x : Fin N → Fin 3 → ℝ) (i j : Fin N) : ip (pt x) i j = dot x i j := by
  unfold ip pt dot
  simp [PiLp.inner_apply, mul_comm]

theorem norm_pt_sq {N : ℕ} (x : Fin N → Fin 3 → ℝ) (i : Fin N) : ‖pt x i‖ ^ 2 = ∑ k, x i k ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem norm_pt_sub_sq {N : ℕ} (x : Fin N → Fin 3 → ℝ) (i j : Fin N) :
    ‖pt x i - pt x j‖ ^ 2 = ∑ k, (x i k - x j k) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem norm_eq_one_iff_sq {E : Type*} [SeminormedAddCommGroup E] (v : E) : ‖v‖ = 1 ↔ ‖v‖ ^ 2 = 1 := by
  constructor
  · intro h
    rw [h]
    norm_num
  · intro h
    have h0 := norm_nonneg v
    nlinarith [sq_nonneg (‖v‖ - 1)]

theorem onSphere_iff {N : ℕ} (x : Fin N → Fin 3 → ℝ) : OnSphere x ↔ ∀ i, ‖pt x i‖ = 1 := by
  unfold OnSphere
  refine forall_congr' fun i => ?_
  rw [norm_eq_one_iff_sq, norm_pt_sq]

theorem injective_pt {N : ℕ} (x : Fin N → Fin 3 → ℝ) : Function.Injective (pt x) ↔ Function.Injective x := by
  constructor
  · intro h i j hij
    exact h (by unfold pt; rw [hij])
  · intro h i j hij
    exact h (WithLp.toLp_injective 2 hij)

/-- The energy of the statement is the energy of the theorems of the certificates. -/
theorem energy_eq {N : ℕ} (x : Fin N → Fin 3 → ℝ) :
    energy x = ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / dist (pt x i) (pt x j) := by
  unfold energy
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [dist_eq_norm, ← norm_pt_sub_sq, Real.sqrt_sq (norm_nonneg _)]

/-! ## The inner products of the family -/

/-- The class of a pair of distinct points, for both orders. -/
def pcS (a b : ℕ) : ℕ := if a < b then pc a b else pc b a

theorem pcS_comm (a b : ℕ) (hab : a ≠ b) : pcS a b = pcS b a := by
  unfold pcS
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg (by omega), if_pos h]

/-- The inner product of two points of `X14 h`. -/
noncomputable def ipc (h : ℝ) (a b : Fin 14) : ℝ := ipVal h (pcS a.val b.val)

theorem ipc_comm (h : ℝ) (a b : Fin 14) (hab : a ≠ b) : ipc h a b = ipc h b a := by
  unfold ipc
  rw [pcS_comm a.val b.val (fun e => hab (Fin.ext e))]

/-- **The inner products of the family**, for two distinct points in any order. -/
theorem dot_X14 (h : ℝ) (hh : h ^ 2 ≤ 1) (a b : Fin 14) (hab : a ≠ b) : dot (X14 h) a b = ipc h a b := by
  have hne : a.val ≠ b.val := fun e => hab (Fin.ext e)
  unfold ipc pcS
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · rw [if_pos hlt]
    exact inner_X14N h hh a.val b.val hlt b.isLt
  · rw [if_neg (by omega), dot_comm]
    exact inner_X14N h hh b.val a.val hlt a.isLt

/-! ## A minimal pair -/

/-- A configuration of at least two points has a pair of distinct points with the smallest inner product. -/
theorem exists_min_pair {N : ℕ} (hN : 2 ≤ N) (x : Fin N → Fin 3 → ℝ) :
    ∃ p q : Fin N, p ≠ q ∧ ∀ i j, i ≠ j → dot x p q ≤ dot x i j := by
  classical
  set S : Finset (Fin N × Fin N) := univ.filter (fun t => t.1 ≠ t.2) with hS
  have hne : S.Nonempty := by
    refine ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩
    simp [hS, Fin.ext_iff]
  obtain ⟨t, ht, hmin⟩ := S.exists_min_image (fun t => dot x t.1 t.2) hne
  refine ⟨t.1, t.2, (Finset.mem_filter.mp ht).2, fun i j hij => ?_⟩
  exact hmin (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)

end N14

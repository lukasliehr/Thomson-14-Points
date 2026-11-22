module

public import N14.Basic
public import N32.Gram

/-!
# The theorem for 14 points, analytic part: orthogonal maps, relabellings, frames (row A1)

* `dot_mulVec`, `sqdist_mulVec`, `energy_mulVec`: an orthogonal map preserves inner products, distances and the
  energy;
* `pairsum_comp_perm`, `energy_comp_perm`: a sum of a symmetric function over the pairs `i < j`, and with it the
  energy, does not depend on the labelling of the points;
* `energy_of_congr`: the energy of the image of a configuration under an orthogonal map and a relabelling;
* `exists_frame`: for two unit vectors `P`, `v` that are not parallel there is an orthogonal map that takes `P`
  to `(0, 0, 1)` and `v` to `(√(1 - z²), 0, z)`, where `z` is their inner product. It is obtained from
  `N32.congr_of_gram` for the triples `P, v, P × v` and their images.
-/

@[expose] public section

namespace N14

open Finset Matrix

/-! ## Orthogonal maps -/

/-- An orthogonal map preserves the inner product. -/
theorem dot_mulVec (U : Matrix (Fin 3) (Fin 3) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (v w : Fin 3 → ℝ) : ∑ c, U.mulVec v c * U.mulVec w c = ∑ c, v c * w c := by
  have h1 : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hU
  have h2 : dotProduct (U.mulVec v) (U.mulVec w) = dotProduct v w := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  exact h2

/-- An orthogonal map preserves squared distances. -/
theorem sqdist_mulVec (U : Matrix (Fin 3) (Fin 3) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (v w : Fin 3 → ℝ) : ∑ k, (U.mulVec v k - U.mulVec w k) ^ 2 = ∑ k, (v k - w k) ^ 2 := by
  have h := dot_mulVec U hU (v - w) (v - w)
  rw [Matrix.mulVec_sub] at h
  have e1 : ∀ k, (U.mulVec v k - U.mulVec w k) ^ 2
      = (U.mulVec v - U.mulVec w) k * (U.mulVec v - U.mulVec w) k := fun k => by
    rw [Pi.sub_apply]
    ring
  have e2 : ∀ k, (v k - w k) ^ 2 = (v - w) k * (v - w) k := fun k => by
    rw [Pi.sub_apply]
    ring
  rw [Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_congr rfl fun k _ => e2 k]
  exact h

theorem dot_mulVec_config {N : ℕ} (U : Matrix (Fin 3) (Fin 3) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (x : Fin N → Fin 3 → ℝ) (i j : Fin N) : dot (fun i => U.mulVec (x i)) i j = dot x i j :=
  dot_mulVec U hU (x i) (x j)

theorem onSphere_iff_dot {N : ℕ} (x : Fin N → Fin 3 → ℝ) : OnSphere x ↔ ∀ i, dot x i i = 1 := by
  unfold OnSphere dot
  refine forall_congr' fun i => ?_
  have e : ∑ k, x i k ^ 2 = ∑ k, x i k * x i k := Finset.sum_congr rfl fun k _ => by ring
  rw [e]

theorem onSphere_mulVec {N : ℕ} (U : Matrix (Fin 3) (Fin 3) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (x : Fin N → Fin 3 → ℝ) (hx : OnSphere x) : OnSphere (fun i => U.mulVec (x i)) := by
  rw [onSphere_iff_dot] at hx ⊢
  intro i
  rw [dot_mulVec_config U hU x i i]
  exact hx i

/-- An orthogonal map preserves the energy. -/
theorem energy_mulVec {N : ℕ} (U : Matrix (Fin 3) (Fin 3) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (x : Fin N → Fin 3 → ℝ) : energy (fun i => U.mulVec (x i)) = energy x := by
  unfold energy
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show 1 / Real.sqrt (∑ k, (U.mulVec (x i) k - U.mulVec (x j) k) ^ 2) = _
  rw [sqdist_mulVec U hU]

/-! ## Relabellings -/

/-- A symmetric function of two labels that vanishes on the diagonal: the sum over all ordered pairs is twice
the sum over the pairs `i < j`. -/
theorem sum_all_eq {N : ℕ} (F : Fin N → Fin N → ℝ) (hsym : ∀ i j, F i j = F j i) (hd : ∀ i, F i i = 0) :
    ∑ i, ∑ j, F i j = 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F i j := by
  have split : ∀ i : Fin N, ∑ j, F i j
      = ∑ j ∈ univ.filter (fun j => i < j), F i j + ∑ j ∈ univ.filter (fun j => j < i), F i j := by
    intro i
    have h1 := Finset.sum_filter_add_sum_filter_not (univ : Finset (Fin N)) (fun j => i < j) (fun j => F i j)
    have hset : univ.filter (fun j => ¬ i < j) = insert i (univ.filter (fun j => j < i)) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_insert, not_lt]
      constructor
      · intro h
        rcases lt_or_eq_of_le h with h | h
        · exact Or.inr h
        · exact Or.inl h
      · rintro (h | h)
        · exact le_of_eq h
        · exact le_of_lt h
    have h2 : ∑ j ∈ univ.filter (fun j => ¬ i < j), F i j = ∑ j ∈ univ.filter (fun j => j < i), F i j := by
      rw [hset, Finset.sum_insert (by simp), hd, zero_add]
    rw [← h1, h2]
  have swap : ∑ i, ∑ j ∈ univ.filter (fun j => j < i), F i j
      = ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F i j := by
    rw [Finset.sum_comm' (s' := fun j => univ.filter (fun i => j < i)) (t' := univ)]
    · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hsym b a
    · intro a b
      simp
  rw [Finset.sum_congr rfl fun i _ => split i, Finset.sum_add_distrib, swap]
  ring

/-- **A sum of a symmetric function over the pairs `i < j` does not depend on the labelling.** -/
theorem pairsum_comp_perm {N : ℕ} (F : Fin N → Fin N → ℝ) (hsym : ∀ i j, F i j = F j i) (hd : ∀ i, F i i = 0)
    (σ : Equiv.Perm (Fin N)) :
    ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F (σ i) (σ j) = ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F i j := by
  have h1 := sum_all_eq F hsym hd
  have h2 := sum_all_eq (fun i j => F (σ i) (σ j)) (fun i j => hsym _ _) (fun i => hd _)
  have h3 : ∑ i, ∑ j, F (σ i) (σ j) = ∑ i, ∑ j, F i j :=
    calc ∑ i, ∑ j, F (σ i) (σ j)
        = ∑ i, ∑ j, F (σ i) j := Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ (fun j => F (σ i) j)
      _ = ∑ i, ∑ j, F i j := Equiv.sum_comp σ (fun i => ∑ j, F i j)
  linarith

/-- **The energy does not depend on the labelling of the points.** -/
theorem energy_comp_perm {N : ℕ} (x : Fin N → Fin 3 → ℝ) (σ : Equiv.Perm (Fin N)) :
    energy (fun i => x (σ i)) = energy x := by
  unfold energy
  exact pairsum_comp_perm (fun i j => 1 / Real.sqrt (∑ k, (x i k - x j k) ^ 2))
    (fun i j => by
      have e : ∑ k, (x i k - x j k) ^ 2 = ∑ k, (x j k - x i k) ^ 2 :=
        Finset.sum_congr rfl fun k _ => by ring
      rw [e])
    (fun i => by simp) σ

/-- The energy of the image of a configuration under an orthogonal map and a relabelling. -/
theorem energy_of_congr {N : ℕ} (x y : Fin N → Fin 3 → ℝ) (U : Matrix (Fin 3) (Fin 3) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (σ : Equiv.Perm (Fin N)) (h : ∀ i, y i = U.mulVec (x (σ i))) :
    energy y = energy x := by
  have e : y = fun i => U.mulVec ((fun i => x (σ i)) i) := funext h
  rw [e, energy_mulVec U hU, energy_comp_perm]

/-! ## A frame -/

/-- The cross product of two vectors of `ℝ³`. -/
def cross (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

/-- Two triples of vectors of `ℝ³` with the same inner products, the first with an invertible Gram matrix,
differ by an orthogonal map. -/
theorem congr_triple (x y : Fin 3 → Fin 3 → ℝ) (h : ∀ i j, ∑ c, y i c * y j c = ∑ c, x i c * x j c)
    (hd : (N32.gram3 x).det ≠ 0) :
    ∃ U ∈ Matrix.orthogonalGroup (Fin 3) ℝ, ∀ i, U.mulVec (x i) = y i := by
  obtain ⟨U, hU, hy⟩ := N32.congr_of_gram x y h id hd
  exact ⟨U, hU, fun i => (hy i).symm⟩

/-- **A frame.** For unit vectors `P`, `v` with inner product `z`, `z² < 1`, there is an orthogonal map that
takes `P` to `(0, 0, 1)` and `v` to `(√(1 - z²), 0, z)`. -/
theorem exists_frame (P v : Fin 3 → ℝ) (hP : ∑ c, P c ^ 2 = 1) (hv : ∑ c, v c ^ 2 = 1) (z : ℝ)
    (hz : ∑ c, P c * v c = z) (hz1 : z ^ 2 < 1) :
    ∃ U ∈ Matrix.orthogonalGroup (Fin 3) ℝ, U.mulVec P = ![0, 0, 1]
      ∧ U.mulVec v = ![√(1 - z ^ 2), 0, z] := by
  have hρ : √(1 - z ^ 2) ^ 2 = 1 - z ^ 2 := Real.sq_sqrt (by linarith)
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = √(1 - z ^ 2) := ⟨_, rfl⟩
  rw [← hρdef] at hρ ⊢
  have hP' : P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2 = 1 := by rw [← hP, Fin.sum_univ_three]
  have hv' : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by rw [← hv, Fin.sum_univ_three]
  have hz' : P 0 * v 0 + P 1 * v 1 + P 2 * v 2 = z := by rw [← hz, Fin.sum_univ_three]
  -- the Gram matrix of `P, v, P × v`
  have g00 : ∑ c, P c * P c = 1 := by rw [Fin.sum_univ_three]; linear_combination hP'
  have g01 : ∑ c, P c * v c = z := hz
  have g10 : ∑ c, v c * P c = z := by rw [Fin.sum_univ_three]; linear_combination hz'
  have g11 : ∑ c, v c * v c = 1 := by rw [Fin.sum_univ_three]; linear_combination hv'
  have g02 : ∑ c, P c * cross P v c = 0 := by
    rw [Fin.sum_univ_three]
    simp only [cross, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    ring
  have g20 : ∑ c, cross P v c * P c = 0 := by
    rw [← g02]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  have g12 : ∑ c, v c * cross P v c = 0 := by
    rw [Fin.sum_univ_three]
    simp only [cross, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    ring
  have g21 : ∑ c, cross P v c * v c = 0 := by
    rw [← g12]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  have g22 : ∑ c, cross P v c * cross P v c = ρ ^ 2 := by
    rw [Fin.sum_univ_three]
    simp only [cross, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    linear_combination (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) * hP' + hv' - (P 0 * v 0 + P 1 * v 1 + P 2 * v 2 + z) * hz'
      - hρ
  -- the two triples
  obtain ⟨x, hx⟩ : ∃ x : Fin 3 → Fin 3 → ℝ, x = ![P, v, cross P v] := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin 3 → Fin 3 → ℝ, y = ![![0, 0, 1], ![ρ, 0, z], ![0, ρ, 0]] := ⟨_, rfl⟩
  have hx0 : x 0 = P := by rw [hx]; rfl
  have hx1 : x 1 = v := by rw [hx]; rfl
  have hx2 : x 2 = cross P v := by rw [hx]; rfl
  have hy0 : y 0 = ![0, 0, 1] := by rw [hy]; rfl
  have hy1 : y 1 = ![ρ, 0, z] := by rw [hy]; rfl
  have hy2 : y 2 = ![0, ρ, 0] := by rw [hy]; rfl
  have hg : ∀ i j, ∑ c, y i c * y j c = ∑ c, x i c * x j c := by
    intro i j
    fin_cases i <;> fin_cases j
    · show ∑ c, y 0 c * y 0 c = ∑ c, x 0 c * x 0 c
      rw [hx0, hy0, g00, Fin.sum_univ_three]
      simp
    · show ∑ c, y 0 c * y 1 c = ∑ c, x 0 c * x 1 c
      rw [hx0, hx1, hy0, hy1, g01, Fin.sum_univ_three]
      simp
    · show ∑ c, y 0 c * y 2 c = ∑ c, x 0 c * x 2 c
      rw [hx0, hx2, hy0, hy2, g02, Fin.sum_univ_three]
      simp
    · show ∑ c, y 1 c * y 0 c = ∑ c, x 1 c * x 0 c
      rw [hx0, hx1, hy0, hy1, g10, Fin.sum_univ_three]
      simp
    · show ∑ c, y 1 c * y 1 c = ∑ c, x 1 c * x 1 c
      rw [hx1, hy1, g11, Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
      linear_combination hρ
    · show ∑ c, y 1 c * y 2 c = ∑ c, x 1 c * x 2 c
      rw [hx1, hx2, hy1, hy2, g12, Fin.sum_univ_three]
      simp
    · show ∑ c, y 2 c * y 0 c = ∑ c, x 2 c * x 0 c
      rw [hx0, hx2, hy0, hy2, g20, Fin.sum_univ_three]
      simp
    · show ∑ c, y 2 c * y 1 c = ∑ c, x 2 c * x 1 c
      rw [hx1, hx2, hy1, hy2, g21, Fin.sum_univ_three]
      simp
    · show ∑ c, y 2 c * y 2 c = ∑ c, x 2 c * x 2 c
      rw [hx2, hy2, g22, Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
      ring
  have hdet : (N32.gram3 x).det = (1 - z ^ 2) * ρ ^ 2 := by
    rw [Matrix.det_fin_three]
    simp only [N32.gram3, Matrix.of_apply, hx0, hx1, hx2, g00, g01, g02, g10, g11, g12, g20, g21, g22]
    ring
  have hd : (N32.gram3 x).det ≠ 0 := by
    rw [hdet, hρ]
    have : (0 : ℝ) < 1 - z ^ 2 := by linarith
    positivity
  obtain ⟨U, hU, hUx⟩ := congr_triple x y hg hd
  refine ⟨U, hU, ?_, ?_⟩
  · have := hUx 0
    rw [hx0, hy0] at this
    exact this
  · have := hUx 1
    rw [hx1, hy1] at this
    exact this

end N14

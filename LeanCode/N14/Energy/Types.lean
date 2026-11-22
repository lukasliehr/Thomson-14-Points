module

public import N14.Energy.Schema

/-!
# T7, configurations with two types of points: counting

Two points `p ≠ q` of a configuration have the type `0`, all others the type `1` (`tau`).

* `sum_tau`: a function of the type, summed over the points.
* `sum_ne_ne`: a sum over the third points of a pair.
* `sum_tau_pairs`: a function of the two types, summed over the ordered pairs of distinct points.
* `typed_pairs`: the sum over the ordered pairs of distinct points of a function `G (τ i) (τ j) (s i j)` of the
  types and of a symmetric quantity `s`, if `G` is a multiple of a function `φ` plus a constant for equal types,
  and if `G 0 1 + G 1 0` is twice this multiple plus a constant.
* `slackOf_swap12`, `slackOf_swap23`: the slack of a triple (`slackOf`) does not depend on the order of the
  triple, if the share of a pair does not depend on the order of the pair.
* `ge_of_sorted12`, `ge_of_sorted23`: a lower bound for a function that is symmetric in two of its arguments
  follows from the bound for these two arguments in increasing order.
-/

@[expose] public section

namespace N14.Energy

open CAP CAP.ThreePoint N14.Ident Finset

variable {ι : Type*} [DecidableEq ι]

/-- The types of the points: the two points `p`, `q` have the type `0`, all others the type `1`. -/
def tau (p q : ι) (i : ι) : ℕ := if i = p ∨ i = q then 0 else 1

theorem tau_cases (p q i : ι) : tau p q i = 0 ∨ tau p q i = 1 := by
  unfold tau
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem tau_zero {p q i : ι} (h : tau p q i = 0) : i = p ∨ i = q := by
  by_contra h'
  rw [tau, if_neg h'] at h
  exact absurd h (by norm_num)

theorem tau_one {p q i : ι} (h : tau p q i = 1) : i ≠ p ∧ i ≠ q := by
  by_contra h'
  have h2 : i = p ∨ i = q := by
    by_contra h3
    exact h' (not_or.mp h3)
  rw [tau, if_pos h2] at h
  exact absurd h (by norm_num)

theorem tau_left (p q : ι) : tau p q p = 0 := if_pos (Or.inl rfl)

theorem tau_right (p q : ι) : tau p q q = 0 := if_pos (Or.inr rfl)

theorem tau_other {p q i : ι} (hp : i ≠ p) (hq : i ≠ q) : tau p q i = 1 := if_neg (not_or.mpr ⟨hp, hq⟩)

omit [DecidableEq ι] in
/-- Three distinct points are not all among two points. -/
theorem not_three_of_two {p q i j k : ι} (hi : i = p ∨ i = q) (hj : j = p ∨ j = q) (hk : k = p ∨ k = q)
    (hd : Distinct3 i j k) : False := by
  obtain ⟨h1, h2, h3⟩ := hd
  rcases hi with hi | hi <;> rcases hj with hj | hj <;> rcases hk with hk | hk
  · exact h1 (hi.trans hj.symm)
  · exact h1 (hi.trans hj.symm)
  · exact h2 (hi.trans hk.symm)
  · exact h3 (hj.trans hk.symm)
  · exact h3 (hj.trans hk.symm)
  · exact h2 (hi.trans hk.symm)
  · exact h1 (hi.trans hj.symm)
  · exact h1 (hi.trans hj.symm)

variable [Fintype ι]

/-- A function of the type, summed over the points. -/
theorem sum_tau (p q : ι) (hpq : p ≠ q) (h : ℕ → ℝ) :
    ∑ i, h (tau p q i) = 2 * h 0 + ((Fintype.card ι : ℝ) - 2) * h 1 := by
  have e : ∀ i, h (tau p q i)
      = h 1 + ((if i = p then h 0 - h 1 else 0) + (if i = q then h 0 - h 1 else 0)) := by
    intro i
    unfold tau
    by_cases h1 : i = p
    · have h2 : ¬ i = q := fun h2 => hpq (h1.symm.trans h2)
      rw [if_pos (Or.inl h1), if_pos h1, if_neg h2]
      ring
    · by_cases h2 : i = q
      · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2]
        ring
      · rw [if_neg (not_or.mpr ⟨h1, h2⟩), if_neg h1, if_neg h2]
        ring
  have hp : (∑ i, if i = p then h 0 - h 1 else 0) = h 0 - h 1 := by simp
  have hq : (∑ i, if i = q then h 0 - h 1 else 0) = h 0 - h 1 := by simp
  rw [sum_congr rfl fun i _ => e i, sum_add_distrib, sum_add_distrib, hp, hq, sum_const, card_univ, nsmul_eq_mul]
  ring

/-- A sum over the third points of a pair. -/
theorem sum_ne_ne {i j : ι} (hij : i ≠ j) (f : ι → ℝ) :
    (∑ k, if i ≠ k ∧ j ≠ k then f k else 0) = (∑ k, f k) - f i - f j := by
  have e : ∀ k, (if i ≠ k ∧ j ≠ k then f k else 0)
      = f k - (if k = i then f i else 0) - (if k = j then f j else 0) := by
    intro k
    by_cases h1 : k = i
    · have h2 : ¬ k = j := fun h2 => hij (h1.symm.trans h2)
      rw [if_neg (fun h => h.1 h1.symm), if_pos h1, if_neg h2, h1]
      ring
    · by_cases h2 : k = j
      · rw [if_neg (fun h => h.2 h2.symm), if_neg h1, if_pos h2, h2]
        ring
      · rw [if_pos ⟨fun h => h1 h.symm, fun h => h2 h.symm⟩, if_neg h1, if_neg h2]
        ring
  have hp : (∑ k, if k = i then f i else 0) = f i := by simp
  have hq : (∑ k, if k = j then f j else 0) = f j := by simp
  rw [sum_congr rfl fun k _ => e k, sum_sub_distrib, sum_sub_distrib, hp, hq]

/-- A function of the two types, summed over the ordered pairs of distinct points. -/
theorem sum_tau_pairs (p q : ι) (hpq : p ≠ q) (F : ℕ → ℕ → ℝ) :
    (∑ i, ∑ j, if i ≠ j then F (tau p q i) (tau p q j) else 0)
      = 2 * F 0 0 + 2 * ((Fintype.card ι : ℝ) - 2) * (F 0 1 + F 1 0)
        + ((Fintype.card ι : ℝ) - 2) * ((Fintype.card ι : ℝ) - 3) * F 1 1 := by
  have e : ∀ i, (∑ j, if i ≠ j then F (tau p q i) (tau p q j) else 0)
      = 2 * F (tau p q i) 0 + ((Fintype.card ι : ℝ) - 2) * F (tau p q i) 1 - F (tau p q i) (tau p q i) := by
    intro i
    have e1 : ∀ j, (if i ≠ j then F (tau p q i) (tau p q j) else 0)
        = F (tau p q i) (tau p q j) - (if j = i then F (tau p q i) (tau p q i) else 0) := by
      intro j
      by_cases h : j = i
      · rw [if_neg (fun h' => h' h.symm), if_pos h, h]
        ring
      · rw [if_pos (fun h' => h h'.symm), if_neg h]
        ring
    have hp : (∑ j, if j = i then F (tau p q i) (tau p q i) else 0) = F (tau p q i) (tau p q i) := by simp
    have ht := sum_tau p q hpq (fun b => F (tau p q i) b)
    rw [sum_congr rfl fun j _ => e1 j, sum_sub_distrib, hp, ht]
  have h := sum_tau p q hpq (fun a => 2 * F a 0 + ((Fintype.card ι : ℝ) - 2) * F a 1 - F a a)
  rw [sum_congr rfl fun i _ => e i, h]
  ring

/-- A linear combination of two functions, summed over the ordered pairs of distinct points. -/
theorem sum_pairs_lin (a b : ℝ) (f g : ι → ι → ℝ) :
    (∑ i, ∑ j, if i ≠ j then a * f i j + b * g i j else 0)
      = a * (∑ i, ∑ j, if i ≠ j then f i j else 0) + b * (∑ i, ∑ j, if i ≠ j then g i j else 0) := by
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  split_ifs
  · rfl
  · ring

/-- The constant of a pair of points with the types `a`, `b`: `κ01` is the constant of the two orders of a pair
with different types together. -/
noncomputable def kap (κ00 κ01 κ11 : ℝ) (a b : ℕ) : ℝ := if a = b then (if a = 0 then κ00 else κ11) else κ01 / 2

theorem kap_00 (κ00 κ01 κ11 : ℝ) : kap κ00 κ01 κ11 0 0 = κ00 := by simp [kap]

theorem kap_01 (κ00 κ01 κ11 : ℝ) : kap κ00 κ01 κ11 0 1 = κ01 / 2 := by simp [kap]

theorem kap_10 (κ00 κ01 κ11 : ℝ) : kap κ00 κ01 κ11 1 0 = κ01 / 2 := by simp [kap]

theorem kap_11 (κ00 κ01 κ11 : ℝ) : kap κ00 κ01 κ11 1 1 = κ11 := by simp [kap]

/-- **The sum over the pairs of a function of the two types.** -/
theorem typed_pairs (p q : ι) (hpq : p ≠ q) (s : ι → ι → ℝ) (hs : ∀ i j, s i j = s j i) (G : ℕ → ℕ → ℝ → ℝ)
    (c : ℝ) (φ : ℝ → ℝ) (κ00 κ01 κ11 : ℝ) (h00 : ∀ y, G 0 0 y = c * φ y + κ00)
    (h11 : ∀ y, G 1 1 y = c * φ y + κ11) (h01 : ∀ y, G 0 1 y + G 1 0 y = 2 * c * φ y + κ01) :
    (∑ i, ∑ j, if i ≠ j then G (tau p q i) (tau p q j) (s i j) else 0)
      = c * (∑ i, ∑ j, if i ≠ j then φ (s i j) else 0) + 2 * κ00 + 2 * ((Fintype.card ι : ℝ) - 2) * κ01
        + ((Fintype.card ι : ℝ) - 2) * ((Fintype.card ι : ℝ) - 3) * κ11 := by
  -- the two orders of a pair
  have hsw : (∑ i, ∑ j, if i ≠ j then G (tau p q i) (tau p q j) (s i j) else 0)
      = ∑ i, ∑ j, if i ≠ j then G (tau p q j) (tau p q i) (s i j) else 0 := by
    rw [sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    by_cases h : i = j
    · rw [if_neg (fun h' => h' h.symm), if_neg (fun h' => h' h)]
    · rw [if_pos (fun h' => h h'.symm), if_pos h, hs]
  have hpt : ∀ i j, G (tau p q i) (tau p q j) (s i j) + G (tau p q j) (tau p q i) (s i j)
      = 2 * c * φ (s i j) + 2 * kap κ00 κ01 κ11 (tau p q i) (tau p q j) := by
    intro i j
    rcases tau_cases p q i with hi | hi <;> rcases tau_cases p q j with hj | hj <;> rw [hi, hj]
    · rw [h00, kap_00]
      ring
    · rw [h01, kap_01]
      ring
    · rw [add_comm, h01, kap_10]
      ring
    · rw [h11, kap_11]
      ring
  have h2 : (∑ i, ∑ j, if i ≠ j then G (tau p q i) (tau p q j) (s i j) else 0)
        + (∑ i, ∑ j, if i ≠ j then G (tau p q j) (tau p q i) (s i j) else 0)
      = 2 * c * (∑ i, ∑ j, if i ≠ j then φ (s i j) else 0)
        + 2 * (∑ i, ∑ j, if i ≠ j then kap κ00 κ01 κ11 (tau p q i) (tau p q j) else 0) := by
    rw [← sum_pairs_lin, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    split_ifs
    · exact hpt i j
    · ring
  have h4 := sum_tau_pairs p q hpq (kap κ00 κ01 κ11)
  rw [kap_00, kap_01, kap_10, kap_11] at h4
  rw [← hsw] at h2
  linarith

/-! ## The order of a triple -/

omit [Fintype ι] [DecidableEq ι] in
/-- The slack of a triple does not depend on the order of its first two points. -/
theorem slackOf_swap12 (P : Params) (blocks : ℕ → List Blk) (cK : ℝ) (ψ : ℕ → ℕ → ℕ → ℝ → ℝ)
    (hψ : ∀ a b c s, ψ a b c s = ψ b a c s) (τ : ι → ℕ) (x : ι → EuclideanSpace ℝ (Fin 3)) (i j k : ι) :
    slackOf P blocks cK ψ τ x i j k = slackOf P blocks cK ψ τ x j i k := by
  have hsym : ip x j i = ip x i j := real_inner_comm _ _
  unfold slackOf
  rw [hψ (τ j) (τ i) (τ k), hsym]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The slack of a triple does not depend on the order of its last two points. -/
theorem slackOf_swap23 (P : Params) (blocks : ℕ → List Blk) (cK : ℝ) (ψ : ℕ → ℕ → ℕ → ℝ → ℝ)
    (hψ : ∀ a b c s, ψ a b c s = ψ b a c s) (τ : ι → ℕ) (x : ι → EuclideanSpace ℝ (Fin 3)) (i j k : ι) :
    slackOf P blocks cK ψ τ x i j k = slackOf P blocks cK ψ τ x i k j := by
  have hsym : ip x k j = ip x j k := real_inner_comm _ _
  unfold slackOf
  rw [hψ (τ k) (τ j) (τ i), hsym]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- A lower bound for a function that is symmetric in its last two arguments follows from the bound for these
arguments in increasing order, under a condition with the same symmetry. -/
theorem ge_of_sorted23 (f : ℝ → ℝ → ℝ → ℝ) (h23 : ∀ u v t, f u v t = f u t v) (S : ℝ → ℝ → ℝ → Prop)
    (hS : ∀ u v t, S u v t → S u t v) (θ : ℝ) (h : ∀ u v t, v ≤ t → S u v t → θ ≤ f u v t) (u v t : ℝ)
    (hS' : S u v t) : θ ≤ f u v t := by
  rcases le_total v t with hvt | hvt
  · exact h u v t hvt hS'
  · rw [h23]
    exact h u t v hvt (hS _ _ _ hS')

omit [Fintype ι] [DecidableEq ι] in
/-- The same for the first two arguments. -/
theorem ge_of_sorted12 (f : ℝ → ℝ → ℝ → ℝ) (h12 : ∀ u v t, f u v t = f v u t) (S : ℝ → ℝ → ℝ → Prop)
    (hS : ∀ u v t, S u v t → S v u t) (θ : ℝ) (h : ∀ u v t, u ≤ v → S u v t → θ ≤ f u v t) (u v t : ℝ)
    (hS' : S u v t) : θ ≤ f u v t := by
  rcases le_total u v with huv | huv
  · exact h u v t huv hS'
  · rw [h12]
    exact h v u t huv (hS _ _ _ hS')

end N14.Energy

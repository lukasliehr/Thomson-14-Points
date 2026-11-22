module

public import N14.Local.Poly

/-!
# Statement 7 of T7, the assembly: the three tests of positive definiteness

The centres of the claims are natural numbers in the slots of packed numbers; the checkers of
`N14/Local/Kernel.lean` scatter them into the slots of global monomials and test matrices that are formed from
the sums. This file proves what the tests mean for sums over the terms.

* `hess_form`: the terms of degree 2 of all pairs, with the monomials `M2 D k = D_(k / 26) D_(k % 26)`:
  `193 · 2^47 |D|² ≤ 2000 (P - N)`.
* `cub_form`: the terms of degree 3 by rows: `(∑_a D_a (P_a - N_a))² ≤ A3 |D|² ∑_k M_k²` (Cauchy–Schwarz and the
  matrix `A3 - T Tᵗ`).
* `quart_form`: for a pair, `24 |quartic form of the centres| ≤ A (x₀² + x₁² + x₂² + x₃²)²`.
-/

@[expose] public section

namespace N14.Local

open CAP Finset N14.Jet

/-! ## Sums over a product of two ranges and over the upper triangle -/

theorem sum_range_mul (n m : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ range (n * m), f k = ∑ a ∈ range n, ∑ b ∈ range m, f (m * a + b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm n m]

/-- A double sum over a square as a sum over the upper triangle. -/
theorem sum_upper (n : ℕ) (h : ℕ → ℕ → ℝ) :
    ∑ i ∈ range n, ∑ j ∈ range n, h i j
      = ∑ i ∈ range n, ∑ j ∈ range n, if i ≤ j then (if i = j then h i i else h i j + h j i) else 0 := by
  have e1 : ∀ i j : ℕ, h i j
      = (if i ≤ j then (if i = j then h i i else h i j) else 0) + (if j < i then h i j else 0) := by
    intro i j
    by_cases hij : i ≤ j
    · rw [if_pos hij, if_neg (not_lt.mpr hij), add_zero]
      by_cases he : i = j
      · rw [if_pos he, he]
      · rw [if_neg he]
    · rw [if_neg hij, if_pos (not_le.mp hij), zero_add]
  have e2 : ∑ i ∈ range n, ∑ j ∈ range n, (if j < i then h i j else 0)
      = ∑ i ∈ range n, ∑ j ∈ range n, (if i < j then h j i else 0) := Finset.sum_comm
  calc ∑ i ∈ range n, ∑ j ∈ range n, h i j
      = ∑ i ∈ range n, ∑ j ∈ range n,
          ((if i ≤ j then (if i = j then h i i else h i j) else 0) + (if j < i then h i j else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e1 i j
    _ = (∑ i ∈ range n, ∑ j ∈ range n, (if i ≤ j then (if i = j then h i i else h i j) else 0))
        + ∑ i ∈ range n, ∑ j ∈ range n, (if i < j then h j i else 0) := by
        rw [← e2, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
    _ = ∑ i ∈ range n, ∑ j ∈ range n,
          if i ≤ j then (if i = j then h i i else h i j + h j i) else 0 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hij : i ≤ j
        · by_cases he : i = j
          · rw [if_pos hij, if_pos he, if_neg (by omega), if_pos hij, if_pos he, add_zero]
          · rw [if_pos hij, if_neg he, if_pos (by omega), if_pos hij, if_neg he]
        · rw [if_neg hij, if_neg (by omega), if_neg hij, add_zero]

/-! ## The global monomials of degree 2 -/

/-- A point in the gauge coordinates: a function that vanishes from the index 25 on. -/
def Supp25 (D : ℕ → ℝ) : Prop := ∀ k, 25 ≤ k → D k = 0

/-- The monomial of the slot `k = 26 a + b`: `D_a D_b`. -/
noncomputable def M2 (D : ℕ → ℝ) (k : ℕ) : ℝ := D (k / 26) * D (k % 26)

theorem cond_ble {α : Type} (x y : ℕ) (p q : α) : cond (Nat.ble x y) p q = if x ≤ y then p else q := by
  by_cases h : x ≤ y
  · rw [if_pos h, Nat.ble_eq.mpr h]
    rfl
  · rw [if_neg h]
    have hb : Nat.ble x y = false := by
      cases hb : Nat.ble x y
      · rfl
      · exact absurd (Nat.ble_eq.mp hb) h
    rw [hb]
    rfl

theorem cl_eq (a : ℕ) : cl a = if a ≤ 25 then a else 25 := cond_ble a 25 a 25

theorem cl_le (a : ℕ) : cl a ≤ 25 := by
  rw [cl_eq]
  split_ifs <;> omega

theorem D_cl {D : ℕ → ℝ} (hD : Supp25 D) (a : ℕ) : D (cl a) = D a := by
  rw [cl_eq]
  split_ifs with h
  · rfl
  · rw [hD 25 (le_refl _), hD a (by omega)]

theorem key2_eq (a b : ℕ) :
    key2 a b = if cl a ≤ cl b then 26 * cl a + cl b else 26 * cl b + cl a := cond_ble _ _ _ _

theorem key2_prop (a b : ℕ) : key2 a b < 676 ∧ key2 a b / 26 ≤ key2 a b % 26 := by
  have ha := cl_le a
  have hb := cl_le b
  rw [key2_eq]
  split_ifs with h <;> omega

theorem M2_key2 {D : ℕ → ℝ} (hD : Supp25 D) (a b : ℕ) : M2 D (key2 a b) = D a * D b := by
  have ha := cl_le a
  have hb := cl_le b
  unfold M2
  rw [key2_eq]
  split_ifs with h
  · rw [show (26 * cl a + cl b) / 26 = cl a by omega, show (26 * cl a + cl b) % 26 = cl b by omega,
      D_cl hD, D_cl hD]
  · rw [show (26 * cl b + cl a) / 26 = cl b by omega, show (26 * cl b + cl a) % 26 = cl a by omega,
      D_cl hD, D_cl hD, mul_comm]

theorem rec_map {α β : Type} (f : α → β) (l : List α) :
    List.rec (motive := fun _ => List β) [] (fun t _ ih => f t :: ih) l = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (f a :: ·) ih

theorem terms2_eq (w c : ℕ) (g : List ℕ) :
    terms2 w c g = slots2.map (fun t => (slot w c t.1, key2 (lgetD 25 g t.2.1) (lgetD 25 g t.2.2))) := by
  show List.rec (motive := fun _ => List (ℕ × ℕ)) []
    (fun t _ ih => (slot w c t.1, key2 (lgetD 25 g t.2.1) (lgetD 25 g t.2.2)) :: ih) slots2 = _
  exact rec_map (fun t : ℕ × ℕ × ℕ => (slot w c t.1, key2 (lgetD 25 g t.2.1) (lgetD 25 g t.2.2))) slots2

theorem terms2_keys (w c : ℕ) (g : List ℕ) : ∀ t ∈ terms2 w c g, t.2 < 676 ∧ t.2 / 26 ≤ t.2 % 26 := by
  intro t ht
  rw [terms2_eq] at ht
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp ht
  exact key2_prop _ _

/-- **The terms of degree 2 of a pair** and the monomials of its local variables. -/
theorem terms2_sum (w c : ℕ) (g : List ℕ) (D : ℕ → ℝ) (hD : Supp25 D) :
    ((terms2 w c g).map (fun t => (t.1 : ℝ) * M2 D t.2)).sum
      = (slots2.map (fun t => (slot w c t.1 : ℝ) * (D (lgetD 25 g t.2.1) * D (lgetD 25 g t.2.2)))).sum := by
  rw [terms2_eq, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  show (slot w c t.1 : ℝ) * M2 D (key2 (lgetD 25 g t.2.1) (lgetD 25 g t.2.2)) = _
  rw [M2_key2 hD]

/-- A sum over terms of degree 2 with sorted keys as a sum over the upper triangle of the 25 coordinates. -/
theorem quad_terms (l : List (ℕ × ℕ)) (hl : ∀ t ∈ l, t.2 < 676 ∧ t.2 / 26 ≤ t.2 % 26) (D : ℕ → ℝ)
    (hD : Supp25 D) :
    (l.map (fun t => (t.1 : ℝ) * M2 D t.2)).sum
      = ∑ i ∈ range 25, ∑ j ∈ range 25, if i ≤ j then (fiber l (26 * i + j) : ℝ) * (D i * D j) else 0 := by
  rw [← fiber_sum 676 l (fun t ht => (hl t ht).1) (M2 D), show (676 : ℕ) = 26 * 26 from rfl,
    sum_range_mul 26 26]
  have e : ∀ a ∈ range 26, ∑ b ∈ range 26, (fiber l (26 * a + b) : ℝ) * M2 D (26 * a + b)
      = ∑ b ∈ range 25, if a ≤ b then (fiber l (26 * a + b) : ℝ) * (D a * D b) else 0 := by
    intro a _
    rw [Finset.sum_range_succ]
    have h25 : (fiber l (26 * a + 25) : ℝ) * M2 D (26 * a + 25) = 0 := by
      unfold M2
      rw [show (26 * a + 25) % 26 = 25 by omega, hD 25 (le_refl _), mul_zero, mul_zero]
    rw [h25, add_zero]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb' := mem_range.mp hb
    have hM : M2 D (26 * a + b) = D a * D b := by
      unfold M2
      rw [show (26 * a + b) / 26 = a by omega, show (26 * a + b) % 26 = b by omega]
    by_cases hab : a ≤ b
    · rw [if_pos hab, hM]
    · have hz : fiber l (26 * a + b) = 0 := by
        refine fiber_eq_zero l _ fun t ht hk => ?_
        have h2 := (hl t ht).2
        rw [hk] at h2
        omega
      rw [if_neg hab, hz, Nat.cast_zero, zero_mul]
  rw [Finset.sum_congr rfl e, Finset.sum_range_succ]
  have e25 : ∑ b ∈ range 25, (if 25 ≤ b then (fiber l (26 * 25 + b) : ℝ) * (D 25 * D b) else 0) = 0 :=
    Finset.sum_eq_zero fun b hb => if_neg (by have := mem_range.mp hb; omega)
  rw [e25, add_zero]

/-! ## The Hessian -/

/-- **The test of the Hessian.** -/
theorem hess_form (lP lN : List (ℕ × ℕ)) (hP : ∀ t ∈ lP, t.2 < 676 ∧ t.2 / 26 ≤ t.2 % 26)
    (hN : ∀ t ∈ lN, t.2 < 676 ∧ t.2 / 26 ≤ t.2 % 26) (tP : tot lP < 2 ^ 64) (tN : tot lN < 2 ^ 64)
    (H : HessD) (hn : H.Pp.n = 25) (hSP : H.SP = scat lP) (hSN : H.SN = scat lN)
    (hchk : CAP.PSD.check H.Pp H.rows H.cols = true)
    (hlink : triAll H.Pp.w 25 H.rows (hEntry H.Pp.a H.SP H.SN) = true) (D : ℕ → ℝ) (hD : Supp25 D) :
    (27162335252578304 : ℝ) * ∑ k ∈ range 25, D k ^ 2
      ≤ 2000 * ((lP.map (fun t => (t.1 : ℝ) * M2 D t.2)).sum
        - (lN.map (fun t => (t.1 : ℝ) * M2 D t.2)).sum) := by
  have hq := gram_quad H.Pp H.rows H.cols hchk D
  rw [hn] at hq
  rw [quad_terms lP hP D hD, quad_terms lN hN D hD]
  -- the entries of the matrix
  have hE : ∀ i j, i ≤ j → j < 25 → (CAP.PSD.dataEntry H.Pp H.rows i j : ℝ)
      = 2000 * (fiber lP (26 * i + j) : ℝ) - 2000 * (fiber lN (26 * i + j) : ℝ)
        - (if i = j then (27162335252578304 : ℝ) else 0) := by
    intro i j hij hj
    have ht := triAll_sound H.Pp.w 25 H.rows _ hlink i (j - i) (by omega) (by omega)
    have ht' : Nat.beq
        (triEnt H.Pp.w 25 H.rows i (j - i) + 2000 * slot 64 H.SN (27 * i + (j - i))
          + cond (Nat.beq (j - i) 0) 27162335252578304 0)
        (1 <<< (H.Pp.a - 1) + 2000 * slot 64 H.SP (27 * i + (j - i))) = true := ht
    have h1 := Nat.eq_of_beq_eq_true ht'
    rw [show 27 * i + (j - i) = 26 * i + j by omega, hSP, hSN,
      slot_scat 676 lP (fun t ht => (hP t ht).1) tP _ (by omega),
      slot_scat 676 lN (fun t ht => (hN t ht).1) tN _ (by omega), cond_beq, Nat.one_shiftLeft] at h1
    have e3 : (CAP.PSD.dataEntry H.Pp H.rows i j : ℝ)
        = (triEnt H.Pp.w 25 H.rows i (j - i) : ℝ) - (2 : ℝ) ^ (H.Pp.a - 1) := by
      unfold CAP.PSD.dataEntry
      rw [hn]
      push_cast
      ring
    by_cases he : i = j
    · rw [if_pos (by omega)] at h1
      have h2 : (triEnt H.Pp.w 25 H.rows i (j - i) : ℝ) + 2000 * (fiber lN (26 * i + j) : ℝ)
          + 27162335252578304 = (2 : ℝ) ^ (H.Pp.a - 1) + 2000 * (fiber lP (26 * i + j) : ℝ) := by
        exact_mod_cast h1
      rw [e3, if_pos he]
      linarith
    · rw [if_neg (by omega)] at h1
      have h2 : (triEnt H.Pp.w 25 H.rows i (j - i) : ℝ) + 2000 * (fiber lN (26 * i + j) : ℝ) + 0
          = (2 : ℝ) ^ (H.Pp.a - 1) + 2000 * (fiber lP (26 * i + j) : ℝ) := by
        exact_mod_cast h1
      rw [e3, if_neg he]
      linarith
  -- the quadratic form of the matrix
  have e : ∑ i ∈ range 25, ∑ j ∈ range 25,
        (if i ≤ j then (CAP.PSD.dataEntry H.Pp H.rows i j : ℝ) * (D i * D j) else 0)
      = 2000 * (∑ i ∈ range 25, ∑ j ∈ range 25,
          if i ≤ j then (fiber lP (26 * i + j) : ℝ) * (D i * D j) else 0)
        - 2000 * (∑ i ∈ range 25, ∑ j ∈ range 25,
          if i ≤ j then (fiber lN (26 * i + j) : ℝ) * (D i * D j) else 0)
        - 27162335252578304 * ∑ k ∈ range 25, D k ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hdiag : (27162335252578304 : ℝ) * D i ^ 2
        = ∑ j ∈ range 25, if i = j then (27162335252578304 : ℝ) * D i ^ 2 else 0 := by
      rw [Finset.sum_ite_eq (range 25) i (fun _ => (27162335252578304 : ℝ) * D i ^ 2), if_pos hi]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, hdiag, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hij : i ≤ j
    · rw [if_pos hij, if_pos hij, if_pos hij, hE i j hij (mem_range.mp hj)]
      by_cases he : i = j
      · rw [if_pos he, if_pos he, he]
        ring
      · rw [if_neg he, if_neg he]
        ring
    · rw [if_neg hij, if_neg hij, if_neg hij, if_neg (by omega)]
      ring
  rw [e] at hq
  linarith

/-! ## The cubic form -/

theorem dotK_eq (X Y : ℕ) : dotK X Y = ∑ k ∈ range 676, slot 64 X k * slot 64 Y k := by
  unfold dotK
  generalize 676 = n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

theorem dot_scat (l m : List (ℕ × ℕ)) (hl : ∀ t ∈ l, t.2 < 676) (hm : ∀ t ∈ m, t.2 < 676)
    (tl : tot l < 2 ^ 64) (tm : tot m < 2 ^ 64) :
    (dotK (scat l) (scat m) : ℝ) = ∑ k ∈ range 676, (fiber l k : ℝ) * (fiber m k : ℝ) := by
  rw [dotK_eq]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [slot_scat 676 l hl tl k (mem_range.mp hk), slot_scat 676 m hm tm k (mem_range.mp hk)]

/-- **The test of the cubic form**: the terms of the row `a` are the terms whose first index is `a`. -/
theorem cub_form (lP lN : ℕ → List (ℕ × ℕ)) (hP : ∀ a, a < 25 → ∀ t ∈ lP a, t.2 < 676)
    (hN : ∀ a, a < 25 → ∀ t ∈ lN a, t.2 < 676) (tP : ∀ a, a < 25 → tot (lP a) < 2 ^ 64)
    (tN : ∀ a, a < 25 → tot (lN a) < 2 ^ 64) (C : CubD) (hn : C.Pp.n = 25)
    (hTP : ∀ a, a < 25 → lgetD 0 C.TP a = scat (lP a)) (hTN : ∀ a, a < 25 → lgetD 0 C.TN a = scat (lN a))
    (hchk : CAP.PSD.check C.Pp C.rows C.cols = true)
    (hlink : triAll C.Pp.w 25 C.rows (cEntry C.Pp.a C.A3 C.TP C.TN) = true) (D : ℕ → ℝ) (M : ℕ → ℝ) :
    (∑ a ∈ range 25, D a * (((lP a).map (fun t => (t.1 : ℝ) * M t.2)).sum
        - ((lN a).map (fun t => (t.1 : ℝ) * M t.2)).sum)) ^ 2
      ≤ (C.A3 : ℝ) * (∑ a ∈ range 25, D a ^ 2) * ∑ k ∈ range 676, M k ^ 2 := by
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℕ → ℝ, ∀ a k, T a k = (fiber (lP a) k : ℝ) - (fiber (lN a) k : ℝ) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℕ → ℝ, ∀ i j, G i j = ∑ k ∈ range 676, T i k * T j k := ⟨_, fun _ _ => rfl⟩
  have hGs : ∀ i j, G i j = G j i := fun i j => by
    rw [hG, hG]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  -- the form as a sum over the slots
  have h1 : ∀ a ∈ range 25, D a * (((lP a).map (fun t => (t.1 : ℝ) * M t.2)).sum
      - ((lN a).map (fun t => (t.1 : ℝ) * M t.2)).sum) = ∑ k ∈ range 676, D a * T a k * M k := by
    intro a ha
    have ha' := mem_range.mp ha
    rw [← fiber_sum 676 (lP a) (hP a ha') M, ← fiber_sum 676 (lN a) (hN a ha') M, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hT]
    ring
  have h2 : ∀ k ∈ range 676, ∑ a ∈ range 25, D a * T a k * M k = (∑ a ∈ range 25, D a * T a k) * M k :=
    fun k _ => (Finset.sum_mul _ _ _).symm
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_congr rfl h2]
  refine le_trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _) ?_
  refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun k _ => sq_nonneg _)
  -- the Gram matrix
  have h3 : ∑ k ∈ range 676, (∑ a ∈ range 25, D a * T a k) ^ 2
      = ∑ i ∈ range 25, ∑ j ∈ range 25, G i j * (D i * D j) := by
    have e : ∀ k ∈ range 676, (∑ a ∈ range 25, D a * T a k) ^ 2
        = ∑ i ∈ range 25, ∑ j ∈ range 25, T i k * T j k * (D i * D j) := by
      intro k _
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hG, Finset.sum_mul]
  rw [h3, sum_upper 25 (fun i j => G i j * (D i * D j))]
  -- the entries of the matrix
  have hq := gram_quad C.Pp C.rows C.cols hchk D
  rw [hn] at hq
  have hE : ∀ i j, i ≤ j → j < 25 → (CAP.PSD.dataEntry C.Pp C.rows i j : ℝ)
      = if i = j then (C.A3 : ℝ) - G i i else -(2 * G i j) := by
    intro i j hij hj
    have hi : i < 25 := by omega
    have ht := triAll_sound C.Pp.w 25 C.rows _ hlink i (j - i) hi (by omega)
    have e3 : (CAP.PSD.dataEntry C.Pp C.rows i j : ℝ)
        = (triEnt C.Pp.w 25 C.rows i (j - i) : ℝ) - (2 : ℝ) ^ (C.Pp.a - 1) := by
      unfold CAP.PSD.dataEntry
      rw [hn]
      push_cast
      ring
    have eG : G i j = (∑ k ∈ range 676, (fiber (lP i) k : ℝ) * (fiber (lP j) k : ℝ))
        + (∑ k ∈ range 676, (fiber (lN i) k : ℝ) * (fiber (lN j) k : ℝ))
        - ((∑ k ∈ range 676, (fiber (lP i) k : ℝ) * (fiber (lN j) k : ℝ))
          + ∑ k ∈ range 676, (fiber (lN i) k : ℝ) * (fiber (lP j) k : ℝ)) := by
      rw [hG, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hT, hT]
      ring
    have ht2 : (if j - i = 0 then
          Nat.beq (triEnt C.Pp.w 25 C.rows i (j - i)
              + (dotK (lgetD 0 C.TP i) (lgetD 0 C.TP i) + dotK (lgetD 0 C.TN i) (lgetD 0 C.TN i)))
            (1 <<< (C.Pp.a - 1) + C.A3
              + (dotK (lgetD 0 C.TP i) (lgetD 0 C.TN i) + dotK (lgetD 0 C.TN i) (lgetD 0 C.TP i)))
        else
          Nat.beq (triEnt C.Pp.w 25 C.rows i (j - i)
              + 2 * (dotK (lgetD 0 C.TP i) (lgetD 0 C.TP (i + (j - i)))
                + dotK (lgetD 0 C.TN i) (lgetD 0 C.TN (i + (j - i)))))
            (1 <<< (C.Pp.a - 1)
              + 2 * (dotK (lgetD 0 C.TP i) (lgetD 0 C.TN (i + (j - i)))
                + dotK (lgetD 0 C.TN i) (lgetD 0 C.TP (i + (j - i)))))) = true := by
      rw [← cond_beq]
      exact ht
    by_cases he : i = j
    · subst he
      rw [if_pos (Nat.sub_self i)] at ht2
      have h1 := Nat.eq_of_beq_eq_true ht2
      rw [Nat.one_shiftLeft, hTP i hi, hTN i hi] at h1
      have h2 : (triEnt C.Pp.w 25 C.rows i (i - i) : ℝ)
            + ((dotK (scat (lP i)) (scat (lP i)) : ℝ) + (dotK (scat (lN i)) (scat (lN i)) : ℝ))
          = (2 : ℝ) ^ (C.Pp.a - 1) + (C.A3 : ℝ)
            + ((dotK (scat (lP i)) (scat (lN i)) : ℝ) + (dotK (scat (lN i)) (scat (lP i)) : ℝ)) := by
        exact_mod_cast h1
      rw [dot_scat _ _ (hP i hi) (hP i hi) (tP i hi) (tP i hi),
        dot_scat _ _ (hN i hi) (hN i hi) (tN i hi) (tN i hi),
        dot_scat _ _ (hP i hi) (hN i hi) (tP i hi) (tN i hi),
        dot_scat _ _ (hN i hi) (hP i hi) (tN i hi) (tP i hi)] at h2
      rw [e3, if_pos rfl, eG]
      linarith
    · rw [if_neg (by omega), show i + (j - i) = j by omega] at ht2
      have h1 := Nat.eq_of_beq_eq_true ht2
      rw [Nat.one_shiftLeft, hTP i hi, hTN i hi, hTP j hj, hTN j hj] at h1
      have h2 : (triEnt C.Pp.w 25 C.rows i (j - i) : ℝ)
            + 2 * ((dotK (scat (lP i)) (scat (lP j)) : ℝ) + (dotK (scat (lN i)) (scat (lN j)) : ℝ))
          = (2 : ℝ) ^ (C.Pp.a - 1)
            + 2 * ((dotK (scat (lP i)) (scat (lN j)) : ℝ) + (dotK (scat (lN i)) (scat (lP j)) : ℝ)) := by
        exact_mod_cast h1
      rw [dot_scat _ _ (hP i hi) (hP j hj) (tP i hi) (tP j hj),
        dot_scat _ _ (hN i hi) (hN j hj) (tN i hi) (tN j hj),
        dot_scat _ _ (hP i hi) (hN j hj) (tP i hi) (tN j hj),
        dot_scat _ _ (hN i hi) (hP j hj) (tN i hi) (tP j hj)] at h2
      rw [e3, if_neg he, eG]
      linarith
  -- the quadratic form of the matrix
  have e : ∑ i ∈ range 25, ∑ j ∈ range 25,
        (if i ≤ j then (CAP.PSD.dataEntry C.Pp C.rows i j : ℝ) * (D i * D j) else 0)
      = (C.A3 : ℝ) * (∑ k ∈ range 25, D k ^ 2)
        - ∑ i ∈ range 25, ∑ j ∈ range 25,
          if i ≤ j then (if i = j then G i i * (D i * D i) else G i j * (D i * D j) + G j i * (D j * D i))
          else 0 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hdiag : (C.A3 : ℝ) * D i ^ 2 = ∑ j ∈ range 25, if i = j then (C.A3 : ℝ) * D i ^ 2 else 0 := by
      rw [Finset.sum_ite_eq (range 25) i (fun _ => (C.A3 : ℝ) * D i ^ 2), if_pos hi]
    rw [hdiag, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hij : i ≤ j
    · rw [if_pos hij, if_pos hij, hE i j hij (mem_range.mp hj)]
      by_cases he : i = j
      · rw [if_pos he, if_pos he, if_pos he, he]
        ring
      · rw [if_neg he, if_neg he, if_neg he, hGs j i]
        ring
    · rw [if_neg hij, if_neg hij, if_neg (by omega)]
      ring
  rw [e] at hq
  linarith

/-! ## The quartic form of a pair -/

/-- The monomial of the slot `K = 64 a + 16 b + 4 c + d`: `x_a x_b x_c x_d`. -/
noncomputable def M4 (xs : ℕ → ℝ) (K : ℕ) : ℝ := xs (K / 64) * xs (K / 16 % 4) * xs (K / 4 % 4) * xs (K % 4)

theorem M4_k4 (xs : ℕ → ℝ) (a b c d : ℕ) (_ha : a < 4) (hb : b < 4) (hc : c < 4) (hd : d < 4) :
    M4 xs (k4 a b c d) = xs a * xs b * xs c * xs d := by
  have e : k4 a b c d = 64 * a + 16 * b + 4 * c + d := rfl
  unfold M4
  rw [e, show (64 * a + 16 * b + 4 * c + d) / 64 = a by omega,
    show (64 * a + 16 * b + 4 * c + d) / 16 % 4 = b by omega,
    show (64 * a + 16 * b + 4 * c + d) / 4 % 4 = c by omega,
    show (64 * a + 16 * b + 4 * c + d) % 4 = d by omega]

theorem k4_lt (a b c d : ℕ) (ha : a < 4) (hb : b < 4) (hc : c < 4) (hd : d < 4) : k4 a b c d < 256 := by
  show 64 * a + 16 * b + 4 * c + d < 256
  omega

theorem tm4_sum (xs : ℕ → ℝ) (v a b c d : ℕ) (ha : a < 4) (hb : b < 4) (hc : c < 4) (hd : d < 4)
    (l : List (ℕ × ℕ)) :
    ((tm4 v a b c d l).map (fun t => (t.1 : ℝ) * M4 xs t.2)).sum
      = 24 * ((v : ℝ) * (xs a * xs b * xs c * xs d)) + (l.map (fun t => (t.1 : ℝ) * M4 xs t.2)).sum := by
  unfold tm4
  simp only [List.map_cons, List.sum_cons]
  rw [M4_k4 xs a b c d ha hb hc hd,
    M4_k4 xs a b d c ha hb hd hc,
    M4_k4 xs a c b d ha hc hb hd,
    M4_k4 xs a c d b ha hc hd hb,
    M4_k4 xs a d b c ha hd hb hc,
    M4_k4 xs a d c b ha hd hc hb,
    M4_k4 xs b a c d hb ha hc hd,
    M4_k4 xs b a d c hb ha hd hc,
    M4_k4 xs b c a d hb hc ha hd,
    M4_k4 xs b c d a hb hc hd ha,
    M4_k4 xs b d a c hb hd ha hc,
    M4_k4 xs b d c a hb hd hc ha,
    M4_k4 xs c a b d hc ha hb hd,
    M4_k4 xs c a d b hc ha hd hb,
    M4_k4 xs c b a d hc hb ha hd,
    M4_k4 xs c b d a hc hb hd ha,
    M4_k4 xs c d a b hc hd ha hb,
    M4_k4 xs c d b a hc hd hb ha,
    M4_k4 xs d a b c hd ha hb hc,
    M4_k4 xs d a c b hd ha hc hb,
    M4_k4 xs d b a c hd hb ha hc,
    M4_k4 xs d b c a hd hb hc ha,
    M4_k4 xs d c a b hd hc ha hb,
    M4_k4 xs d c b a hd hc hb ha]
  ring

theorem tm4_keys (v a b c d : ℕ) (ha : a < 4) (hb : b < 4) (hc : c < 4) (hd : d < 4) (l : List (ℕ × ℕ))
    (t : ℕ × ℕ) (ht : t ∈ tm4 v a b c d l) : t.2 < 256 ∨ t ∈ l := by
  unfold tm4 at ht
  simp only [List.mem_cons] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  all_goals first
    | exact Or.inl (k4_lt _ _ _ _ (by assumption) (by assumption) (by assumption) (by assumption))
    | exact Or.inr h

/-- The terms of degree 4 for a list of slots. -/
theorem terms4_gen (w c : ℕ) (xs : ℕ → ℝ) (L : List (ℕ × ℕ × ℕ × ℕ × ℕ))
    (hL : ∀ t ∈ L, t.2.1 < 4 ∧ t.2.2.1 < 4 ∧ t.2.2.2.1 < 4 ∧ t.2.2.2.2 < 4) :
    (((List.rec (motive := fun _ => List (ℕ × ℕ)) []
        (fun t _ ih => tm4 (slot w c t.1) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 ih) L).map
          (fun t => (t.1 : ℝ) * M4 xs t.2)).sum
      = 24 * (L.map (fun t => (slot w c t.1 : ℝ) * (xs t.2.1 * xs t.2.2.1 * xs t.2.2.2.1 * xs t.2.2.2.2))).sum)
    ∧ ∀ t ∈ (List.rec (motive := fun _ => List (ℕ × ℕ)) []
        (fun t _ ih => tm4 (slot w c t.1) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 ih) L), t.2 < 256 := by
  induction L with
  | nil =>
    refine ⟨?_, fun t ht => absurd ht List.not_mem_nil⟩
    show (0 : ℝ) = 24 * 0
    ring
  | cons u L ih =>
    obtain ⟨h1, h2, h3, h4⟩ := hL u (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨ihs, ihk⟩ := ih fun t ht => hL t (List.mem_cons.mpr (Or.inr ht))
    constructor
    · show ((tm4 (slot w c u.1) u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 _).map (fun t => (t.1 : ℝ) * M4 xs t.2)).sum
        = _
      rw [tm4_sum xs _ _ _ _ _ h1 h2 h3 h4, ihs, List.map_cons, List.sum_cons]
      ring
    · intro t ht
      rcases tm4_keys _ _ _ _ _ h1 h2 h3 h4 _ t ht with h | h
      · exact h
      · exact ihk t h

theorem terms4_sum (w c : ℕ) (xs : ℕ → ℝ) :
    ((terms4 w c).map (fun t => (t.1 : ℝ) * M4 xs t.2)).sum
      = 24 * (slots4.map (fun t => (slot w c t.1 : ℝ)
          * (xs t.2.1 * xs t.2.2.1 * xs t.2.2.2.1 * xs t.2.2.2.2))).sum :=
  (terms4_gen w c xs slots4 slots4_lt).1

theorem terms4_keys (w c : ℕ) : ∀ t ∈ terms4 w c, t.2 < 256 :=
  (terms4_gen w c (fun _ => 0) slots4 slots4_lt).2

/-- One of the two tests of the quartic form of a pair. -/
theorem quart_half (w cP cN A MP MN : ℕ) (P : CAP.PSD.Params) (rows cols : ℕ) (hn : P.n = 16)
    (hMP : MP = scat (terms4 w cP)) (hMN : MN = scat (terms4 w cN)) (tP : tot (terms4 w cP) < 2 ^ 64)
    (tN : tot (terms4 w cN) < 2 ^ 64) (hchk : CAP.PSD.check P rows cols = true)
    (hlink : triAll P.w 16 rows (qEntry P.a A MP MN true) = true) (xs : ℕ → ℝ) :
    0 ≤ (A : ℝ) * (xs 0 ^ 2 + xs 1 ^ 2 + xs 2 ^ 2 + xs 3 ^ 2) ^ 2 + 24 * cform w cP cN 4 (lx xs) := by
  obtain ⟨hpar, _⟩ := CAP.PSD.rowOk_of_check P rows cols hchk
  have ha : 1 ≤ P.a := (CAP.PSD.ok_of_paramsOk P hpar).ha
  obtain ⟨m, hm⟩ : ∃ m : ℕ → ℝ, ∀ K, m K = (fiber (terms4 w cP) K : ℝ) - (fiber (terms4 w cN) K : ℝ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℕ → ℝ, ∀ k, v k = xs (k / 4) * xs (k % 4) := ⟨_, fun _ => rfl⟩
  have hq := gram_quad P rows cols hchk v
  rw [hn] at hq
  -- the entries of the matrix
  have hE : ∀ k l, k ≤ l → l < 16 → 2 * (CAP.PSD.dataEntry P rows k l : ℝ)
      = if k = l then (A : ℝ) + m (16 * k + k) else m (16 * k + l) + m (16 * l + k) := by
    intro k l hkl hl
    have ht := triAll_sound P.w 16 rows _ hlink k (l - k) (by omega) (by omega)
    have e3 : (CAP.PSD.dataEntry P rows k l : ℝ) = (triEnt P.w 16 rows k (l - k) : ℝ) - (2 : ℝ) ^ (P.a - 1) := by
      unfold CAP.PSD.dataEntry
      rw [hn]
      push_cast
      ring
    have e2 : (2 : ℝ) ^ P.a = 2 * (2 : ℝ) ^ (P.a - 1) := by
      obtain ⟨b, hb⟩ : ∃ b, P.a = b + 1 := ⟨P.a - 1, by omega⟩
      rw [hb, Nat.add_sub_cancel, pow_succ]
      ring
    have ht2 : (if l - k = 0 then
          Nat.beq (2 * triEnt P.w 16 rows k (l - k) + slot 64 MN (17 * k))
            (1 <<< P.a + A + slot 64 MP (17 * k))
        else
          Nat.beq (2 * triEnt P.w 16 rows k (l - k) + slot 64 MN (17 * k + (l - k))
              + slot 64 MN (17 * k + 16 * (l - k)))
            (1 <<< P.a + slot 64 MP (17 * k + (l - k)) + slot 64 MP (17 * k + 16 * (l - k)))) = true := by
      rw [← cond_beq]
      exact ht
    by_cases he : k = l
    · rw [if_pos (by omega)] at ht2
      have h1 := Nat.eq_of_beq_eq_true ht2
      rw [Nat.one_shiftLeft, hMP, hMN, show 17 * k = 16 * k + k by omega,
        slot_scat 256 _ (terms4_keys w cP) tP _ (by omega),
        slot_scat 256 _ (terms4_keys w cN) tN _ (by omega)] at h1
      have h2 : 2 * (triEnt P.w 16 rows k (l - k) : ℝ) + (fiber (terms4 w cN) (16 * k + k) : ℝ)
          = (2 : ℝ) ^ P.a + (A : ℝ) + (fiber (terms4 w cP) (16 * k + k) : ℝ) := by
        exact_mod_cast h1
      rw [e3, if_pos he, hm]
      linarith
    · rw [if_neg (by omega)] at ht2
      have h1 := Nat.eq_of_beq_eq_true ht2
      rw [Nat.one_shiftLeft, hMP, hMN, show 17 * k + (l - k) = 16 * k + l by omega,
        show 17 * k + 16 * (l - k) = 16 * l + k by omega,
        slot_scat 256 _ (terms4_keys w cP) tP _ (by omega),
        slot_scat 256 _ (terms4_keys w cP) tP _ (by omega),
        slot_scat 256 _ (terms4_keys w cN) tN _ (by omega),
        slot_scat 256 _ (terms4_keys w cN) tN _ (by omega)] at h1
      have h2 : 2 * (triEnt P.w 16 rows k (l - k) : ℝ) + (fiber (terms4 w cN) (16 * k + l) : ℝ)
            + (fiber (terms4 w cN) (16 * l + k) : ℝ)
          = (2 : ℝ) ^ P.a + (fiber (terms4 w cP) (16 * k + l) : ℝ)
            + (fiber (terms4 w cP) (16 * l + k) : ℝ) := by
        exact_mod_cast h1
      rw [e3, if_neg he, hm, hm]
      linarith
  -- twice the quadratic form of the matrix
  have e : 2 * ∑ k ∈ range 16, ∑ l ∈ range 16,
        (if k ≤ l then (CAP.PSD.dataEntry P rows k l : ℝ) * (v k * v l) else 0)
      = (A : ℝ) * (∑ k ∈ range 16, v k ^ 2)
        + ∑ k ∈ range 16, ∑ l ∈ range 16,
          if k ≤ l then (if k = l then m (16 * k + k) * (v k * v k)
            else m (16 * k + l) * (v k * v l) + m (16 * l + k) * (v l * v k)) else 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hdiag : (A : ℝ) * v k ^ 2 = ∑ l ∈ range 16, if k = l then (A : ℝ) * v k ^ 2 else 0 := by
      rw [Finset.sum_ite_eq (range 16) k (fun _ => (A : ℝ) * v k ^ 2), if_pos hk]
    rw [Finset.mul_sum, hdiag, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    by_cases hkl : k ≤ l
    · have h2 := hE k l hkl (mem_range.mp hl)
      rw [if_pos hkl, if_pos hkl]
      by_cases he : k = l
      · subst he
        rw [if_pos rfl] at h2
        rw [if_pos rfl, if_pos rfl]
        linear_combination (v k * v k) * h2
      · rw [if_neg he] at h2
        rw [if_neg he, if_neg he]
        linear_combination (v k * v l) * h2
    · rw [if_neg hkl, if_neg hkl, if_neg (by omega)]
      ring
  -- the sum of the squares of the products
  have hv2 : ∑ k ∈ range 16, v k ^ 2 = (xs 0 ^ 2 + xs 1 ^ 2 + xs 2 ^ 2 + xs 3 ^ 2) ^ 2 := by
    rw [show (16 : ℕ) = 4 * 4 from rfl, sum_range_mul 4 4]
    have e4 : ∀ a ∈ range 4, ∑ b ∈ range 4, v (4 * a + b) ^ 2
        = xs a ^ 2 * (xs 0 ^ 2 + xs 1 ^ 2 + xs 2 ^ 2 + xs 3 ^ 2) := by
      intro a _
      have e5 : ∀ b ∈ range 4, v (4 * a + b) ^ 2 = xs a ^ 2 * xs b ^ 2 := by
        intro b hb
        have hb' := mem_range.mp hb
        rw [hv, show (4 * a + b) / 4 = a by omega, show (4 * a + b) % 4 = b by omega]
        ring
      rw [Finset.sum_congr rfl e5, ← Finset.mul_sum]
      congr 1
      simp [Finset.sum_range_succ]
    rw [Finset.sum_congr rfl e4, ← Finset.sum_mul]
    have e6 : ∑ a ∈ range 4, xs a ^ 2 = xs 0 ^ 2 + xs 1 ^ 2 + xs 2 ^ 2 + xs 3 ^ 2 := by
      simp [Finset.sum_range_succ]
    rw [e6]
    ring
  -- the form of the centres
  have hc : ∑ k ∈ range 16, ∑ l ∈ range 16, m (16 * k + l) * (v k * v l) = 24 * cform w cP cN 4 (lx xs) := by
    have e7 : ∀ k ∈ range 16, ∑ l ∈ range 16, m (16 * k + l) * (v k * v l)
        = ∑ l ∈ range 16, m (16 * k + l) * M4 xs (16 * k + l) := by
      intro k hk
      refine Finset.sum_congr rfl fun l hl => ?_
      have hk' := mem_range.mp hk
      have hl' := mem_range.mp hl
      rw [hv, hv]
      unfold M4
      rw [show (16 * k + l) / 64 = k / 4 by omega, show (16 * k + l) / 16 % 4 = k % 4 by omega,
        show (16 * k + l) / 4 % 4 = l / 4 by omega, show (16 * k + l) % 4 = l % 4 by omega]
      ring
    rw [Finset.sum_congr rfl e7, ← sum_range_mul 16 16 (fun K => m K * M4 xs K)]
    have e8 : ∀ K ∈ range (16 * 16), m K * M4 xs K
        = (fiber (terms4 w cP) K : ℝ) * M4 xs K - (fiber (terms4 w cN) K : ℝ) * M4 xs K := by
      intro K _
      rw [hm]
      ring
    rw [Finset.sum_congr rfl e8, Finset.sum_sub_distrib, show (16 : ℕ) * 16 = 256 from rfl,
      fiber_sum 256 _ (terms4_keys w cP) (M4 xs), fiber_sum 256 _ (terms4_keys w cN) (M4 xs),
      terms4_sum, terms4_sum, cform_s4, ← mul_sub]
    congr 1
    induction slots4 with
    | nil => simp
    | cons u L ih =>
      rw [List.map_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, List.sum_cons, ← ih]
      ring
  rw [sum_upper 16 (fun k l => m (16 * k + l) * (v k * v l))] at hc
  rw [hv2, hc] at e
  linarith

/-- **The test of the quartic form of a pair.** -/
theorem quart_form (w : ℕ) (d : PairD) (h : quartOk w d = true) (xs : ℕ → ℝ) :
    24 * |cform w d.cP d.cN 4 (lx xs)| ≤ (d.A : ℝ) * (xs 0 ^ 2 + xs 1 ^ 2 + xs 2 ^ 2 + xs 3 ^ 2) ^ 2 := by
  have h' : (Nat.beq d.qp.n 16 && Nat.beq d.qm.n 16
      && Nat.beq d.MP (scat (terms4 w d.cP)) && Nat.beq d.MN (scat (terms4 w d.cN))
      && Nat.blt (tot (terms4 w d.cP)) (Nat.shiftLeft 1 64) && Nat.blt (tot (terms4 w d.cN)) (Nat.shiftLeft 1 64)
      && CAP.PSD.check d.qp d.rowsP d.colsP && CAP.PSD.check d.qm d.rowsM d.colsM
      && triAll d.qp.w 16 d.rowsP (qEntry d.qp.a d.A d.MP d.MN true)
      && triAll d.qm.w 16 d.rowsM (qEntry d.qm.a d.A d.MP d.MN false)) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨n1, n2⟩, m1⟩, m2⟩, t1⟩, t2⟩, c1⟩, c2⟩, l1⟩, l2⟩ := h'
  have hn1 := Nat.eq_of_beq_eq_true n1
  have hn2 := Nat.eq_of_beq_eq_true n2
  have hm1 := Nat.eq_of_beq_eq_true m1
  have hm2 := Nat.eq_of_beq_eq_true m2
  have ht1 : tot (terms4 w d.cP) < 2 ^ 64 := by
    have := Nat.blt_eq.mp t1
    rwa [show Nat.shiftLeft 1 64 = 2 ^ 64 from Nat.one_shiftLeft 64] at this
  have ht2 : tot (terms4 w d.cN) < 2 ^ 64 := by
    have := Nat.blt_eq.mp t2
    rwa [show Nat.shiftLeft 1 64 = 2 ^ 64 from Nat.one_shiftLeft 64] at this
  have hp := quart_half w d.cP d.cN d.A d.MP d.MN d.qp d.rowsP d.colsP hn1 hm1 hm2 ht1 ht2 c1 l1 xs
  have hm := quart_half w d.cN d.cP d.A d.MN d.MP d.qm d.rowsM d.colsM hn2 hm2 hm1 ht2 ht1 c2 l2 xs
  have hneg : cform w d.cN d.cP 4 (lx xs) = -cform w d.cP d.cN 4 (lx xs) := by
    unfold cform
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs
    · ring
    · ring
  rw [hneg] at hm
  have habs : |cform w d.cP d.cN 4 (lx xs)| = max (cform w d.cP d.cN 4 (lx xs)) (-cform w d.cP d.cN 4 (lx xs)) :=
    rfl
  rcases abs_cases (cform w d.cP d.cN 4 (lx xs)) with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [h1]
    linarith
  · rw [h1]
    linarith

end N14.Local

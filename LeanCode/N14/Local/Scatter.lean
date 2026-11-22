module

public import N14.Local.Kernel
public import CAP.Core.PackedLemmas
public import CAP.Core.Triangular
public import CAP.PSD.Sound
public import CAP.Schema.ThreePoint.Kernels

/-!
# Statement 7 of T7, the assembly: scattered terms and the upper triangle of a matrix of E2

* `fiber l k`: the sum of the values of the terms of `l` with the key `k`. `slot_scat`: slot `k` of `scat l` is
  `fiber l k`, if the sum of all values is below `2^64` and all keys are below `n`. `fiber_sum`: a sum over the
  terms is the sum over the keys of the fibers.
* `cat f ps`: the terms of all pairs; `scatL_eq`, `totL_eq`.
* `triAll_sound`: the test of `triAll` holds for every entry of the upper triangle.
* `gram_quad`: the quadratic form of a matrix that the checker of E2 accepts is nonnegative, written with the
  stored upper triangle.
-/

@[expose] public section

namespace N14.Local

open CAP Finset

/-! ## Scattered terms -/

/-- The sum of the values of the terms with the key `k`. -/
def fiber (l : List (ℕ × ℕ)) (k : ℕ) : ℕ := (l.map (fun t => if t.2 = k then t.1 else 0)).sum

theorem scat_cons (t : ℕ × ℕ) (l : List (ℕ × ℕ)) : scat (t :: l) = scat l + t.1 * 2 ^ (64 * t.2) := by
  show scat l + t.1 <<< (64 * t.2) = _
  rw [Nat.shiftLeft_eq]

theorem tot_cons (t : ℕ × ℕ) (l : List (ℕ × ℕ)) : tot (t :: l) = tot l + t.1 := rfl

theorem fiber_nil (k : ℕ) : fiber [] k = 0 := rfl

theorem fiber_cons (t : ℕ × ℕ) (l : List (ℕ × ℕ)) (k : ℕ) :
    fiber (t :: l) k = (if t.2 = k then t.1 else 0) + fiber l k := by
  unfold fiber
  rw [List.map_cons, List.sum_cons]

theorem fiber_le_tot (l : List (ℕ × ℕ)) (k : ℕ) : fiber l k ≤ tot l := by
  induction l with
  | nil => exact le_refl 0
  | cons t l ih =>
    rw [fiber_cons, tot_cons]
    split_ifs <;> omega

/-- A fiber without a term vanishes. -/
theorem fiber_eq_zero (l : List (ℕ × ℕ)) (k : ℕ) (h : ∀ t ∈ l, t.2 ≠ k) : fiber l k = 0 := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    rw [fiber_cons, if_neg (h t (List.mem_cons.mpr (Or.inl rfl))),
      ih (fun s hs => h s (List.mem_cons.mpr (Or.inr hs)))]

theorem packSum_single (W n a v : ℕ) (ha : a < n) :
    packSum W n (fun k => if a = k then v else 0) = v * 2 ^ (W * a) := by
  unfold packSum
  rw [Finset.sum_eq_single a]
  · show (if a = a then v else 0) * 2 ^ (W * a) = v * 2 ^ (W * a)
    rw [if_pos rfl]
  · intro b _ hb
    show (if a = b then v else 0) * 2 ^ (W * b) = 0
    rw [if_neg (Ne.symm hb), zero_mul]
  · intro h
    exact absurd (mem_range.mpr ha) h

theorem scat_eq (n : ℕ) (l : List (ℕ × ℕ)) (hl : ∀ t ∈ l, t.2 < n) : scat l = packSum 64 n (fiber l) := by
  induction l with
  | nil =>
    show 0 = packSum 64 n (fun k => fiber [] k)
    unfold packSum
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    show fiber [] k * 2 ^ (64 * k) = 0
    rw [fiber_nil, zero_mul]
  | cons t l ih =>
    rw [scat_cons, ih (fun s hs => hl s (List.mem_cons.mpr (Or.inr hs))),
      ← packSum_single 64 n t.2 t.1 (hl t (List.mem_cons.mpr (Or.inl rfl))), ← packSum_add]
    exact packSum_congr 64 n fun k _ => by rw [fiber_cons, add_comm]

/-- **A slot of the scattered terms.** -/
theorem slot_scat (n : ℕ) (l : List (ℕ × ℕ)) (hl : ∀ t ∈ l, t.2 < n) (ht : tot l < 2 ^ 64) (k : ℕ)
    (hk : k < n) : slot 64 (scat l) k = fiber l k := by
  rw [scat_eq n l hl]
  exact slot_packSum 64 n _ (fun j _ => lt_of_le_of_lt (fiber_le_tot l j) ht) k hk

/-- **A sum over the terms** is the sum over the keys of the fibers. -/
theorem fiber_sum (n : ℕ) (l : List (ℕ × ℕ)) (hl : ∀ t ∈ l, t.2 < n) (M : ℕ → ℝ) :
    ∑ k ∈ range n, (fiber l k : ℝ) * M k = (l.map (fun t => (t.1 : ℝ) * M t.2)).sum := by
  induction l with
  | nil =>
    show ∑ k ∈ range n, (fiber [] k : ℝ) * M k = 0
    exact Finset.sum_eq_zero fun k _ => by rw [fiber_nil, Nat.cast_zero, zero_mul]
  | cons t l ih =>
    rw [List.map_cons, List.sum_cons, ← ih (fun s hs => hl s (List.mem_cons.mpr (Or.inr hs)))]
    have e : ∀ k, (fiber (t :: l) k : ℝ) * M k
        = (if t.2 = k then (t.1 : ℝ) * M k else 0) + (fiber l k : ℝ) * M k := by
      intro k
      rw [fiber_cons]
      push_cast
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun k _ => e k, Finset.sum_add_distrib,
      Finset.sum_ite_eq (range n) t.2 (fun k => (t.1 : ℝ) * M k),
      if_pos (mem_range.mpr (hl t (List.mem_cons.mpr (Or.inl rfl))))]

theorem scat_append (l m : List (ℕ × ℕ)) : scat (l ++ m) = scat l + scat m := by
  induction l with
  | nil =>
    show scat m = 0 + scat m
    rw [zero_add]
  | cons t l ih =>
    rw [List.cons_append, scat_cons, scat_cons, ih]
    ring

theorem tot_append (l m : List (ℕ × ℕ)) : tot (l ++ m) = tot l + tot m := by
  induction l with
  | nil =>
    show tot m = 0 + tot m
    rw [zero_add]
  | cons t l ih =>
    rw [List.cons_append, tot_cons, tot_cons, ih]
    ring

/-- The terms of all pairs. -/
def cat (f : PairD → List (ℕ × ℕ)) : List PairD → List (ℕ × ℕ)
  | [] => []
  | d :: ps => cat f ps ++ f d

theorem scatL_eq (f : PairD → List (ℕ × ℕ)) (ps : List PairD) : scatL f ps = scat (cat f ps) := by
  induction ps with
  | nil => rfl
  | cons d ps ih =>
    show scatL f ps + scat (f d) = scat (cat f ps ++ f d)
    rw [scat_append, ih]

theorem totL_eq (f : PairD → List (ℕ × ℕ)) (ps : List PairD) : totL f ps = tot (cat f ps) := by
  induction ps with
  | nil => rfl
  | cons d ps ih =>
    show totL f ps + tot (f d) = tot (cat f ps ++ f d)
    rw [tot_append, ih]

theorem mem_cat {f : PairD → List (ℕ × ℕ)} {ps : List PairD} {t : ℕ × ℕ} (h : t ∈ cat f ps) :
    ∃ d ∈ ps, t ∈ f d := by
  induction ps with
  | nil => exact absurd h List.not_mem_nil
  | cons d ps ih =>
    rcases List.mem_append.mp h with h1 | h1
    · obtain ⟨d', hd', ht⟩ := ih h1
      exact ⟨d', List.mem_cons.mpr (Or.inr hd'), ht⟩
    · exact ⟨d, List.mem_cons.mpr (Or.inl rfl), h1⟩

/-- A sum over the terms of all pairs is the sum over the pairs. -/
theorem sum_cat (f : PairD → List (ℕ × ℕ)) (ps : List PairD) (g : ℕ × ℕ → ℝ) :
    ((cat f ps).map g).sum = (ps.map (fun d => ((f d).map g).sum)).sum := by
  induction ps with
  | nil => rfl
  | cons d ps ih =>
    show ((cat f ps ++ f d).map g).sum = _
    rw [List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]
    ring

/-! ## The upper triangle -/

/-- The test of the row `i`, which begins at the slot `off`. -/
noncomputable def triRowT (w rows : ℕ) (t : ℕ → ℕ → ℕ → Bool) (i off : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun s ihs => ihs && t i s (slot w rows (off + s)))

/-- The tests of the rows from `i` on. -/
noncomputable def triGo (w n rows : ℕ) (t : ℕ → ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih i off => triRowT w rows t i off (n - i) && ih (i + 1) (off + (n - i)))

theorem triAll_eq (w n rows : ℕ) (t : ℕ → ℕ → ℕ → Bool) : triAll w n rows t = triGo w n rows t n 0 0 := rfl

theorem triRowT_sound (w rows : ℕ) (t : ℕ → ℕ → ℕ → Bool) (i off m : ℕ)
    (h : triRowT w rows t i off m = true) (s : ℕ) (hs : s < m) : t i s (slot w rows (off + s)) = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    have h' : (triRowT w rows t i off m && t i m (slot w rows (off + m))) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with h1 | h1
    · exact ih h'.1 h1
    · rw [h1]
      exact h'.2

theorem triGo_sound (w n rows : ℕ) (t : ℕ → ℕ → ℕ → Bool) (fuel : ℕ) :
    ∀ i0, triGo w n rows t fuel i0 (triOff n i0) = true → ∀ i, i0 ≤ i → i < i0 + fuel → ∀ s, s < n - i →
      t i s (slot w rows (triOff n i + s)) = true := by
  induction fuel with
  | zero =>
    intro i0 _ i h1 h2
    omega
  | succ fuel ih =>
    intro i0 h i h1 h2 s hs
    have h' : (triRowT w rows t i0 (triOff n i0) (n - i0)
        && triGo w n rows t fuel (i0 + 1) (triOff n i0 + (n - i0))) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.eq_or_lt_of_le h1 with h3 | h3
    · subst h3
      exact triRowT_sound w rows t i0 _ _ h'.1 s hs
    · have h4 := h'.2
      rw [← triOff_succ] at h4
      exact ih (i0 + 1) h4 i h3 (by omega) s hs

/-- **The test of `triAll` holds for every entry of the upper triangle.** -/
theorem triAll_sound (w n rows : ℕ) (t : ℕ → ℕ → ℕ → Bool) (h : triAll w n rows t = true) (i s : ℕ)
    (hi : i < n) (hs : s < n - i) : t i s (triEnt w n rows i s) = true := by
  rw [triAll_eq] at h
  have h0 : triGo w n rows t n 0 (triOff n 0) = true := by
    rw [triOff_zero]
    exact h
  exact triGo_sound w n rows t n 0 h0 i (Nat.zero_le i) (by omega) s hs

/-! ## The quadratic form of a matrix of E2 -/

/-- **A matrix that the checker of E2 accepts**: its quadratic form, written with the stored upper triangle, is
nonnegative. The form of the matrix `gram` is twice this sum. -/
theorem gram_quad (P : CAP.PSD.Params) (rows cols : ℕ) (h : CAP.PSD.check P rows cols = true) (v : ℕ → ℝ) :
    0 ≤ ∑ i ∈ range P.n, ∑ j ∈ range P.n,
      if i ≤ j then (CAP.PSD.dataEntry P rows i j : ℝ) * (v i * v j) else 0 := by
  have hpd := CAP.PSD.check_sound P rows cols h
  have h2 := CAP.ThreePoint.posDef_quad_nonneg _ hpd (fun i => v i.val)
  have e : ∑ i : Fin P.n, ∑ j : Fin P.n,
        v i.val * ((CAP.PSD.gram P rows).map (Int.cast : ℤ → ℝ)) i j * v j.val
      = ∑ i ∈ range P.n, ∑ j ∈ range P.n,
        ((if i ≤ j then (CAP.PSD.dataEntry P rows i j : ℝ) * (v i * v j) else 0)
          + (if j ≤ i then (CAP.PSD.dataEntry P rows j i : ℝ) * (v j * v i) else 0)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range P.n,
      ((if i ≤ j then (CAP.PSD.dataEntry P rows i j : ℝ) * (v i * v j) else 0)
        + (if j ≤ i then (CAP.PSD.dataEntry P rows j i : ℝ) * (v j * v i) else 0))) P.n]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun j =>
      ((if i.val ≤ j then (CAP.PSD.dataEntry P rows i.val j : ℝ) * (v i.val * v j) else 0)
        + (if j ≤ i.val then (CAP.PSD.dataEntry P rows j i.val : ℝ) * (v j * v i.val) else 0))) P.n]
    refine Finset.sum_congr rfl fun j _ => ?_
    show v i.val * ((CAP.PSD.gram P rows i j : ℤ) : ℝ) * v j.val = _
    unfold CAP.PSD.gram
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have h' : (i : ℕ) < j := hlt
      rw [if_neg hlt.ne, if_pos hlt, if_pos h'.le, if_neg (not_le.mpr h')]
      ring
    · subst heq
      rw [if_pos rfl, if_pos (le_refl _)]
      push_cast
      ring
    · have h' : (j : ℕ) < i := hgt
      rw [if_neg hgt.ne', if_neg (not_lt.mpr hgt.le), if_neg (not_le.mpr h'), if_pos h'.le]
      ring
  rw [e] at h2
  have e2 : ∑ i ∈ range P.n, ∑ j ∈ range P.n,
        ((if i ≤ j then (CAP.PSD.dataEntry P rows i j : ℝ) * (v i * v j) else 0)
          + (if j ≤ i then (CAP.PSD.dataEntry P rows j i : ℝ) * (v j * v i) else 0))
      = (∑ i ∈ range P.n, ∑ j ∈ range P.n,
          if i ≤ j then (CAP.PSD.dataEntry P rows i j : ℝ) * (v i * v j) else 0)
        + ∑ i ∈ range P.n, ∑ j ∈ range P.n,
          if i ≤ j then (CAP.PSD.dataEntry P rows i j : ℝ) * (v i * v j) else 0 := by
    have e3 : ∀ i ∈ range P.n, ∑ j ∈ range P.n,
          ((if i ≤ j then (CAP.PSD.dataEntry P rows i j : ℝ) * (v i * v j) else 0)
            + (if j ≤ i then (CAP.PSD.dataEntry P rows j i : ℝ) * (v j * v i) else 0))
        = (∑ j ∈ range P.n, if i ≤ j then (CAP.PSD.dataEntry P rows i j : ℝ) * (v i * v j) else 0)
          + ∑ j ∈ range P.n, if j ≤ i then (CAP.PSD.dataEntry P rows j i : ℝ) * (v j * v i) else 0 :=
      fun i _ => Finset.sum_add_distrib
    rw [Finset.sum_congr rfl e3, Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_comm
  rw [e2] at h2
  linarith

end N14.Local

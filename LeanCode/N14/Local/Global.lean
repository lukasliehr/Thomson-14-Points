module

public import N14.Local.Gauge

/-!
# Statement 7 of T7: the expansion of the energy in the gauge coordinates

**Theorem** (`local7`). Let the checker of every pair accept (`pairAll`) and let the tests of the three forms
accept (`formsOk`). Then there are a linear form `L`, a quadratic form `Q` and a cubic form `C` of the 25 gauge
coordinates (homogeneous functions of degree 1, 2, 3) such that for every displacement `D` of the coordinates
of the candidate

* `0.0482 |D|² ≤ Q(D)` and `|C(D)| ≤ 5.04 |D|³`, and
* `|E(p* + D) - E(p*) - L(D) - Q(D) - C(D)| ≤ 147 |D|⁴` if `|D_k| ≤ 1/125` for all `k`.

Here `E(p)` is the energy of the configuration with the gauge coordinates `p`, and `E(p*)` is the energy of the
candidate. This is the computational content of Proposition 9.1 of the source; that `L` vanishes (the candidate
is a critical point) is not part of it.

The proof: the polynomial of the jet of a pair (`N14.Jet.pairOk_sound`) is split into its parts of degree
0, …, 5; the parts of degree 1, 2, 3 of all pairs are `L`, `Q`, `C`; the parts of degree 4 and 5 and the rest
of order six are bounded for every pair (`pair_stmt`) and summed over the rows (`rows_bound`); the centres of
the parts of degree 2 and 3 are the forms of `hess_form` and `cub_form` (`hess_bound`, `cub_bound`).
-/

@[expose] public section

namespace N14.Local

open CAP Finset N14.Jet Real

/-! ## Sums over lists -/

theorem abs_list_sum_le {α : Type} (l : List α) (f g : α → ℝ) (h : ∀ d ∈ l, |f d| ≤ g d) :
    |(l.map f).sum| ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    exact le_trans (abs_add_le _ _) (add_le_add (h a (List.mem_cons.mpr (Or.inl rfl)))
      (ih fun d hd => h d (List.mem_cons.mpr (Or.inr hd))))

theorem list_sum_le {α : Type} (l : List α) (f g : α → ℝ) (h : ∀ d ∈ l, f d ≤ g d) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    exact add_le_add (h a (List.mem_cons.mpr (Or.inl rfl))) (ih fun d hd => h d (List.mem_cons.mpr (Or.inr hd)))

theorem list_sum_congr {α : Type} (l : List α) (f g : α → ℝ) (h : ∀ d ∈ l, f d = g d) :
    (l.map f).sum = (l.map g).sum :=
  congrArg List.sum (List.map_congr_left h)

theorem list_sum_sub {α : Type} (l : List α) (f g : α → ℝ) :
    (l.map (fun d => f d - g d)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
    ring

theorem list_sum_mul_left {α : Type} (l : List α) (c : ℝ) (f : α → ℝ) :
    (l.map (fun d => c * f d)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
    ring

theorem list_sum_div {α : Type} (l : List α) (c : ℝ) (f : α → ℝ) :
    (l.map (fun d => f d / c)).sum = (l.map f).sum / c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
    ring

/-- A sum over a finite set of sums over a list. -/
theorem sum_list_comm {α : Type} (s : Finset ℕ) (l : List α) (f : ℕ → α → ℝ) :
    ∑ a ∈ s, (l.map (f a)).sum = (l.map (fun t => ∑ a ∈ s, f a t)).sum := by
  induction l with
  | nil => simp
  | cons u l ih =>
    rw [List.map_cons, List.sum_cons, ← ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [List.map_cons, List.sum_cons]

/-- The tests of a recursion over the numbers below `N`. -/
theorem rec_all (p : ℕ → Bool) (N : ℕ)
    (h : Nat.rec (motive := fun _ => Bool) true (fun n ih => ih && p n) N = true) : ∀ n, n < N → p n = true := by
  induction N with
  | zero =>
    intro n hn
    omega
  | succ N ih =>
    have h' : (Nat.rec (motive := fun _ => Bool) true (fun n ih => ih && p n) N && p N) = true := h
    rw [Bool.and_eq_true] at h'
    intro n hn
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h1 | h1
    · exact ih h'.1 n h1
    · rw [h1]
      exact h'.2

/-! ## The coordinates of a pair -/

/-- The local variables of a pair for a displacement `D` of the gauge coordinates. -/
noncomputable def xd (d : PairD) (D : ℕ → ℝ) : ℕ → ℝ := fun v => D (lgetD 25 (gl d.i d.j) v)

/-- The sum of the squares of the 25 coordinates. -/
noncomputable def nsq (D : ℕ → ℝ) : ℝ := ∑ k ∈ range 25, D k ^ 2

/-- The sum of the squares of the coordinates of the point `n`. -/
noncomputable def Bn (D : ℕ → ℝ) (n : ℕ) : ℝ := ((own n).map (fun k => D k ^ 2)).sum

theorem nsq_nonneg (D : ℕ → ℝ) : 0 ≤ nsq D := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem abs_le_sqrt_nsq (D : ℕ → ℝ) (hD : Supp25 D) (k : ℕ) : |D k| ≤ √(nsq D) := by
  by_cases hk : k < 25
  · refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun k => D k ^ 2) (fun _ _ => sq_nonneg _) (mem_range.mpr hk)
  · rw [hD k (by omega), abs_zero]
    exact Real.sqrt_nonneg _

theorem n2_list (g : List ℕ) (hg : g.length ≤ 4) (D : ℕ → ℝ) (h25 : D 25 = 0) :
    D (lgetD 25 g 0) ^ 2 + D (lgetD 25 g 1) ^ 2 + D (lgetD 25 g 2) ^ 2 + D (lgetD 25 g 3) ^ 2
      = (g.map (fun k => D k ^ 2)).sum := by
  match g, hg with
  | [], _ =>
    show D 25 ^ 2 + D 25 ^ 2 + D 25 ^ 2 + D 25 ^ 2 = 0
    rw [h25]
    ring
  | [a], _ =>
    show D a ^ 2 + D 25 ^ 2 + D 25 ^ 2 + D 25 ^ 2 = D a ^ 2 + 0
    rw [h25]
    ring
  | [a, b], _ =>
    show D a ^ 2 + D b ^ 2 + D 25 ^ 2 + D 25 ^ 2 = D a ^ 2 + (D b ^ 2 + 0)
    rw [h25]
    ring
  | [a, b, c], _ =>
    show D a ^ 2 + D b ^ 2 + D c ^ 2 + D 25 ^ 2 = D a ^ 2 + (D b ^ 2 + (D c ^ 2 + 0))
    rw [h25]
    ring
  | [a, b, c, d], _ =>
    show D a ^ 2 + D b ^ 2 + D c ^ 2 + D d ^ 2 = D a ^ 2 + (D b ^ 2 + (D c ^ 2 + (D d ^ 2 + 0)))
    ring
  | _ :: _ :: _ :: _ :: _ :: _, h =>
    simp only [List.length_cons] at h
    omega

theorem own_cases (n : ℕ) : own n = [] ∨ own n = [0, 1] ∨ own n = [2] ∨ own n = [2 * n - 3, 2 * n - 2] := by
  by_cases h3 : 3 ≤ n
  · exact Or.inr (Or.inr (Or.inr (own_ring n h3)))
  · have hc : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hc with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))

theorem own_len (n : ℕ) : (own n).length ≤ 2 := by
  rcases own_cases n with h | h | h | h <;> rw [h] <;> simp

/-- The squares of the local variables of a pair are the squares of the coordinates of its two points. -/
theorem n2_pair (i j : ℕ) (D : ℕ → ℝ) (h25 : D 25 = 0) :
    D (lgetD 25 (gl i j) 0) ^ 2 + D (lgetD 25 (gl i j) 1) ^ 2 + D (lgetD 25 (gl i j) 2) ^ 2
      + D (lgetD 25 (gl i j) 3) ^ 2 = Bn D i + Bn D j := by
  have hlen : (gl i j).length ≤ 4 := by
    show (own i ++ own j).length ≤ 4
    rw [List.length_append]
    have := own_len i
    have := own_len j
    omega
  rw [n2_list (gl i j) hlen D h25]
  show ((own i ++ own j).map (fun k => D k ^ 2)).sum = _
  rw [List.map_append, List.sum_append]
  rfl

theorem Bn_nonneg (D : ℕ → ℝ) (n : ℕ) : 0 ≤ Bn D n := by
  unfold Bn
  refine List.sum_nonneg fun x hx => ?_
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
  exact sq_nonneg _

theorem Bn_ring (D : ℕ → ℝ) (n : ℕ) (hn : 3 ≤ n) : Bn D n = D (2 * n - 3) ^ 2 + D (2 * n - 2) ^ 2 := by
  unfold Bn
  rw [own_ring n hn]
  show D (2 * n - 3) ^ 2 + (D (2 * n - 2) ^ 2 + 0) = _
  ring

/-- The coordinates of the 14 points are the 25 gauge coordinates. -/
theorem sum_Bn (D : ℕ → ℝ) : ∑ n ∈ range 14, Bn D n = nsq D := by
  have b0 : Bn D 0 = 0 := rfl
  have b1 : Bn D 1 = D 0 ^ 2 + (D 1 ^ 2 + 0) := rfl
  have b2 : Bn D 2 = D 2 ^ 2 + 0 := rfl
  unfold nsq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [b0, b1, b2, Bn_ring D 3 (by norm_num), Bn_ring D 4 (by norm_num), Bn_ring D 5 (by norm_num),
    Bn_ring D 6 (by norm_num), Bn_ring D 7 (by norm_num), Bn_ring D 8 (by norm_num), Bn_ring D 9 (by norm_num),
    Bn_ring D 10 (by norm_num), Bn_ring D 11 (by norm_num), Bn_ring D 12 (by norm_num),
    Bn_ring D 13 (by norm_num)]
  norm_num
  ring

/-! ## The statement of a pair -/

theorem max4_sq (a b c d S : ℝ) (ha : a ^ 2 ≤ S) (hb : b ^ 2 ≤ S) (hc : c ^ 2 ≤ S) (hd : d ^ 2 ≤ S) :
    (max (max a b) (max c d)) ^ 2 ≤ S := by
  rcases max_choice (max a b) (max c d) with h | h <;> rw [h]
  · rcases max_choice a b with h1 | h1 <;> rw [h1] <;> assumption
  · rcases max_choice c d with h1 | h1 <;> rw [h1] <;> assumption

/-- The statement of a pair: the parts of degree 2 and 3 of its polynomial against the forms of the centres,
and the bound for everything of degree at least 4. -/
structure PairS (par : Par) (d : PairD) (c : ℕ → ℝ) : Prop where
  supp : Supp c
  h2 : ∀ (xs : ℕ → ℝ) (m : ℝ), (∀ k : Fin 4, |lx xs k| ≤ m) →
    |2 ^ par.s * blk c 2 (lx xs) - cform par.w d.cP d.cN 2 (lx xs)| ≤ (rsum par.w d.cR 2 : ℝ) * m ^ 2
  h3 : ∀ (xs : ℕ → ℝ) (m : ℝ), (∀ k : Fin 4, |lx xs k| ≤ m) →
    |2 ^ par.s * blk c 3 (lx xs) - cform par.w d.cP d.cN 3 (lx xs)| ≤ (rsum par.w d.cR 3 : ℝ) * m ^ 3
  rem : ∀ xs : ℕ → ℝ, (∀ k, |xs k| ≤ 1 / 125) →
    |sem rho (pairExpW d.i d.j d.wit) (lx xs) - sem rho (pairExpW d.i d.j d.wit) (lx fun _ => 0)
        - blk c 1 (lx xs) - blk c 2 (lx xs) - blk c 3 (lx xs)|
      ≤ (sInt par.w d : ℝ) / (24 * 15625 * 2 ^ 48) * (xs 0 ^ 2 + xs 1 ^ 2 + xs 2 ^ 2 + xs 3 ^ 2) ^ 2

/-- **The statement of a pair whose checker accepts.** -/
theorem pair_stmt (par : Par) (hs : par.s = 48) (tab : List T3) (htab : TabOk par.s tab rho) (d : PairD)
    (h : pairAll par tab d = true) : ∃ c, PairS par d c := by
  have h' : (pairOk par tab (pairExpW d.i d.j d.wit) d.cP d.cN d.cR d.n5 d.K && quartOk par.w d) = true := h
  rw [Bool.and_eq_true] at h'
  obtain ⟨hp, hq⟩ := h'
  have hr : (1 / 125 : ℝ) ≤ rb := by
    unfold rb
    norm_num
  obtain ⟨c, κ, hC⟩ := pairOk_sound par (1 / 125) hr tab rho htab _ _ _ _ _ _ hp
  refine ⟨c, hC.rep.supp, fun xs m hx => blk_enc hC 2 (le_refl 2) (by norm_num) (lx xs) m hx,
    fun xs m hx => blk_enc hC 3 (by norm_num) (by norm_num) (lx xs) m hx, ?_⟩
  intro xs hxs
  obtain ⟨n2, hn2⟩ : ∃ n2 : ℝ, n2 = xs 0 ^ 2 + xs 1 ^ 2 + xs 2 ^ 2 + xs 3 ^ 2 := ⟨_, rfl⟩
  rw [← hn2]
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = max (max |xs 0| |xs 1|) (max |xs 2| |xs 3|) := ⟨_, rfl⟩
  have hxm : ∀ k : Fin 4, |lx xs k| ≤ m := by
    intro k
    rw [hm]
    fin_cases k
    · exact le_trans (le_max_left _ _) (le_max_left _ _)
    · exact le_trans (le_max_right _ _) (le_max_left _ _)
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hm0 : 0 ≤ m := le_trans (abs_nonneg _) (hxm 0)
  have hmr : m ≤ 1 / 125 := by
    rw [hm]
    exact max_le (max_le (hxs 0) (hxs 1)) (max_le (hxs 2) (hxs 3))
  have hm2 : m ^ 2 ≤ n2 := by
    rw [hm, hn2]
    refine max4_sq _ _ _ _ _ ?_ ?_ ?_ ?_
    · rw [sq_abs]
      nlinarith [sq_nonneg (xs 1), sq_nonneg (xs 2), sq_nonneg (xs 3)]
    · rw [sq_abs]
      nlinarith [sq_nonneg (xs 0), sq_nonneg (xs 2), sq_nonneg (xs 3)]
    · rw [sq_abs]
      nlinarith [sq_nonneg (xs 0), sq_nonneg (xs 1), sq_nonneg (xs 3)]
    · rw [sq_abs]
      nlinarith [sq_nonneg (xs 0), sq_nonneg (xs 1), sq_nonneg (xs 2)]
  have hn20 : 0 ≤ n2 := le_trans (sq_nonneg m) hm2
  have hm4 : m ^ 4 ≤ n2 ^ 2 := by
    calc m ^ 4 = (m ^ 2) ^ 2 := by ring
      _ ≤ n2 ^ 2 := pow_le_pow_left₀ (sq_nonneg m) hm2 2
  have hD : (0 : ℝ) < 2 ^ par.s := by positivity
  -- the value at the origin
  have a0 := hC.rep.bound (lx fun _ => 0) 0 (fun k => by
    show |(0 : ℝ)| ≤ 0
    rw [abs_zero]) (by norm_num)
  have e0 : sem rho (pairExpW d.i d.j d.wit) (lx fun _ => 0) = blk c 0 (lx xs) := by
    have h1 : sem rho (pairExpW d.i d.j d.wit) (lx fun _ => 0) - pev c (lx fun _ => 0) = 0 := by
      have h2 : |sem rho (pairExpW d.i d.j d.wit) (lx fun _ => 0) - pev c (lx fun _ => 0)| ≤ 0 := by
        refine le_trans a0 (le_of_eq ?_)
        ring
      exact abs_eq_zero.mp (le_antisymm h2 (abs_nonneg _))
    have h3 : pev c (lx fun _ => 0) = blk c 0 (lx xs) := pev_zero c hC.rep.supp (lx xs)
    linarith
  -- the three parts
  have a1 := hC.rep.bound (lx xs) m hxm hmr
  have a5 := blk_abs_le c hC.rep.supp 5 (lx xs) m hxm
  have a4 := blk_enc hC 4 (by norm_num) (le_refl 4) (lx xs) m hxm
  have q4 := quart_form par.w d hq xs
  rw [← hn2] at q4
  have e : sem rho (pairExpW d.i d.j d.wit) (lx xs) - sem rho (pairExpW d.i d.j d.wit) (lx fun _ => 0)
        - blk c 1 (lx xs) - blk c 2 (lx xs) - blk c 3 (lx xs)
      = (sem rho (pairExpW d.i d.j d.wit) (lx xs) - pev c (lx xs)) + blk c 4 (lx xs) + blk c 5 (lx xs) := by
    rw [e0, pev_split]
    ring
  rw [e]
  -- the numbers of the claim
  obtain ⟨Kr, hKr⟩ : ∃ Kr : ℝ, Kr = (d.K : ℝ) := ⟨_, rfl⟩
  obtain ⟨Nr, hNr⟩ : ∃ Nr : ℝ, Nr = (d.n5 : ℝ) := ⟨_, rfl⟩
  obtain ⟨Rr, hRr⟩ : ∃ Rr : ℝ, Rr = (rsum par.w d.cR 4 : ℝ) := ⟨_, rfl⟩
  obtain ⟨Ar, hAr⟩ : ∃ Ar : ℝ, Ar = (d.A : ℝ) := ⟨_, rfl⟩
  have hK := hC.kle
  have hN := hC.n5
  rw [← hKr] at hK
  rw [← hNr] at hN
  rw [← hRr] at a4
  rw [← hAr] at q4
  have hKr0 : 0 ≤ Kr := by
    rw [hKr]
    exact Nat.cast_nonneg _
  have hNr0 : 0 ≤ Nr := by
    rw [hNr]
    exact Nat.cast_nonneg _
  have hRr0 : 0 ≤ Rr := by
    rw [hRr]
    exact Nat.cast_nonneg _
  have hsig : (sInt par.w d : ℝ) / (24 * 15625 * 2 ^ 48)
      = (Ar / 24 + Rr + Nr / 125 + Kr / 15625) / 2 ^ par.s := by
    have es : sInt par.w d = d.A * 15625 + 24 * (rsumK par.w d.cR sl4 * 15625 + d.n5 * 125 + d.K) := rfl
    rw [es, hs, hAr, hRr, hNr, hKr, rsum_eq4]
    push_cast
    field_simp
    ring
  rw [hsig]
  -- the rest of order six
  have t1 : |sem rho (pairExpW d.i d.j d.wit) (lx xs) - pev c (lx xs)| ≤ Kr / 15625 / 2 ^ par.s * n2 ^ 2 := by
    have h1 : κ ≤ Kr / 2 ^ par.s := by
      rw [le_div_iff₀ hD]
      exact hK
    have h2 : m ^ 6 ≤ 1 / 15625 * n2 ^ 2 := by
      have h3 : m ^ 2 ≤ 1 / 15625 := by
        calc m ^ 2 ≤ (1 / 125) ^ 2 := pow_le_pow_left₀ hm0 hmr 2
          _ = 1 / 15625 := by norm_num
      calc m ^ 6 = m ^ 2 * m ^ 4 := by ring
        _ ≤ 1 / 15625 * n2 ^ 2 := mul_le_mul h3 hm4 (pow_nonneg hm0 4) (by norm_num)
    calc |sem rho (pairExpW d.i d.j d.wit) (lx xs) - pev c (lx xs)| ≤ κ * m ^ 6 := a1
      _ ≤ Kr / 2 ^ par.s * (1 / 15625 * n2 ^ 2) :=
          mul_le_mul h1 h2 (pow_nonneg hm0 6) (div_nonneg hKr0 hD.le)
      _ = Kr / 15625 / 2 ^ par.s * n2 ^ 2 := by ring
  -- the part of degree 5
  have t5 : |blk c 5 (lx xs)| ≤ Nr / 125 / 2 ^ par.s * n2 ^ 2 := by
    have h1 : nrm c 5 ≤ Nr / 2 ^ par.s := by
      rw [le_div_iff₀ hD]
      exact hN
    have h2 : m ^ 5 ≤ 1 / 125 * n2 ^ 2 := by
      calc m ^ 5 = m * m ^ 4 := by ring
        _ ≤ 1 / 125 * n2 ^ 2 := mul_le_mul hmr hm4 (pow_nonneg hm0 4) (by norm_num)
    calc |blk c 5 (lx xs)| ≤ nrm c 5 * m ^ 5 := a5
      _ ≤ Nr / 2 ^ par.s * (1 / 125 * n2 ^ 2) :=
          mul_le_mul h1 h2 (pow_nonneg hm0 5) (div_nonneg hNr0 hD.le)
      _ = Nr / 125 / 2 ^ par.s * n2 ^ 2 := by ring
  -- the part of degree 4
  have t4 : |blk c 4 (lx xs)| ≤ (Ar / 24 + Rr) / 2 ^ par.s * n2 ^ 2 := by
    have h1 : |2 ^ par.s * blk c 4 (lx xs)| ≤ Ar / 24 * n2 ^ 2 + Rr * n2 ^ 2 := by
      have h2 := abs_sub_abs_le_abs_sub (2 ^ par.s * blk c 4 (lx xs)) (cform par.w d.cP d.cN 4 (lx xs))
      have h3 : Rr * m ^ 4 ≤ Rr * n2 ^ 2 := mul_le_mul_of_nonneg_left hm4 hRr0
      linarith
    rw [abs_mul, abs_of_pos hD] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ hD]
    linarith
  calc |sem rho (pairExpW d.i d.j d.wit) (lx xs) - pev c (lx xs) + blk c 4 (lx xs) + blk c 5 (lx xs)|
      ≤ |sem rho (pairExpW d.i d.j d.wit) (lx xs) - pev c (lx xs)| + |blk c 4 (lx xs)| + |blk c 5 (lx xs)| :=
        abs_add_three _ _ _
    _ ≤ Kr / 15625 / 2 ^ par.s * n2 ^ 2 + (Ar / 24 + Rr) / 2 ^ par.s * n2 ^ 2
        + Nr / 125 / 2 ^ par.s * n2 ^ 2 := add_le_add (add_le_add t1 t4) t5
    _ = (Ar / 24 + Rr + Nr / 125 + Kr / 15625) / 2 ^ par.s * n2 ^ 2 := by ring

/-! ## The Hessian -/

theorem list_sum_mul_right {α : Type} (l : List α) (c : ℝ) (f : α → ℝ) :
    (l.map (fun d => f d * c)).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
    ring

/-- **The form of the centres of degree 2** of all pairs is bounded from below. -/
theorem hess_bound (w : ℕ) (pairs : List PairD) (H : HessD) (hH : hessOk w pairs H = true) (D : ℕ → ℝ)
    (hD : Supp25 D) :
    (27162335252578304 : ℝ) * nsq D
      ≤ 2000 * (pairs.map (fun d => cform w d.cP d.cN 2 (lx (xd d D)))).sum := by
  have h' : (Nat.beq H.Pp.n 25
      && Nat.beq H.SP (scatL (fun d => terms2 w d.cP (gl d.i d.j)) pairs)
      && Nat.beq H.SN (scatL (fun d => terms2 w d.cN (gl d.i d.j)) pairs)
      && Nat.blt (totL (fun d => terms2 w d.cP (gl d.i d.j)) pairs) (Nat.shiftLeft 1 64)
      && Nat.blt (totL (fun d => terms2 w d.cN (gl d.i d.j)) pairs) (Nat.shiftLeft 1 64)
      && CAP.PSD.check H.Pp H.rows H.cols
      && triAll H.Pp.w 25 H.rows (hEntry H.Pp.a H.SP H.SN)) = true := hH
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨⟨n1, s1⟩, s2⟩, t1⟩, t2⟩, c1⟩, l1⟩ := h'
  have hn := Nat.eq_of_beq_eq_true n1
  have hSP := Nat.eq_of_beq_eq_true s1
  have hSN := Nat.eq_of_beq_eq_true s2
  rw [scatL_eq] at hSP hSN
  have ht1 : tot (cat (fun d => terms2 w d.cP (gl d.i d.j)) pairs) < 2 ^ 64 := by
    have := Nat.blt_eq.mp t1
    rwa [totL_eq, show Nat.shiftLeft 1 64 = 2 ^ 64 from Nat.one_shiftLeft 64] at this
  have ht2 : tot (cat (fun d => terms2 w d.cN (gl d.i d.j)) pairs) < 2 ^ 64 := by
    have := Nat.blt_eq.mp t2
    rwa [totL_eq, show Nat.shiftLeft 1 64 = 2 ^ 64 from Nat.one_shiftLeft 64] at this
  have hkP : ∀ t ∈ cat (fun d => terms2 w d.cP (gl d.i d.j)) pairs, t.2 < 676 ∧ t.2 / 26 ≤ t.2 % 26 := by
    intro t ht
    obtain ⟨d, _, hd⟩ := mem_cat ht
    exact terms2_keys _ _ _ t hd
  have hkN : ∀ t ∈ cat (fun d => terms2 w d.cN (gl d.i d.j)) pairs, t.2 < 676 ∧ t.2 / 26 ≤ t.2 % 26 := by
    intro t ht
    obtain ⟨d, _, hd⟩ := mem_cat ht
    exact terms2_keys _ _ _ t hd
  have hf := hess_form _ _ hkP hkN ht1 ht2 H hn hSP hSN c1 l1 D hD
  rw [sum_cat, sum_cat, ← list_sum_sub] at hf
  have e : ∀ d ∈ pairs, ((terms2 w d.cP (gl d.i d.j)).map (fun t => (t.1 : ℝ) * M2 D t.2)).sum
        - ((terms2 w d.cN (gl d.i d.j)).map (fun t => (t.1 : ℝ) * M2 D t.2)).sum
      = cform w d.cP d.cN 2 (lx (xd d D)) := by
    intro d _
    rw [terms2_sum _ _ _ D hD, terms2_sum _ _ _ D hD, cform_s2, ← list_sum_sub]
    refine list_sum_congr _ _ _ fun t _ => ?_
    show _ = ((slot w d.cP t.1 : ℝ) - (slot w d.cN t.1 : ℝ))
      * (D (lgetD 25 (gl d.i d.j) t.2.1) * D (lgetD 25 (gl d.i d.j) t.2.2))
    ring
  rw [list_sum_congr _ _ _ e] at hf
  exact hf

/-! ## The cubic form -/

theorem p3_eq (a v x y z : ℕ) (l : List (ℕ × ℕ)) :
    p3 a v x y z l = if x = a then (v, 26 * y + z) :: l else l := cond_beq _ _ _ _

theorem p3_sum (D : ℕ → ℝ) (a v x y z : ℕ) (hz : z ≤ 25) (l : List (ℕ × ℕ)) :
    ((p3 a v x y z l).map (fun t => (t.1 : ℝ) * M2 D t.2)).sum
      = (if x = a then (v : ℝ) * (D y * D z) else 0) + (l.map (fun t => (t.1 : ℝ) * M2 D t.2)).sum := by
  rw [p3_eq]
  split_ifs with h
  · rw [List.map_cons, List.sum_cons]
    show (v : ℝ) * M2 D (26 * y + z) + _ = _
    unfold M2
    rw [show (26 * y + z) / 26 = y by omega, show (26 * y + z) % 26 = z by omega]
  · rw [zero_add]

theorem p3_keys (a v x y z : ℕ) (hy : y ≤ 25) (hz : z ≤ 25) (l : List (ℕ × ℕ)) (t : ℕ × ℕ)
    (ht : t ∈ p3 a v x y z l) : t.2 < 676 ∨ t ∈ l := by
  rw [p3_eq] at ht
  split_ifs at ht with h
  · rcases List.mem_cons.mp ht with h1 | h1
    · left
      rw [h1]
      show 26 * y + z < 676
      omega
    · exact Or.inr h1
  · exact Or.inr ht

theorem p3_tot (a v x y z : ℕ) (l : List (ℕ × ℕ)) : tot (p3 a v x y z l) ≤ tot l + v := by
  rw [p3_eq]
  split_ifs
  · exact le_of_eq (tot_cons _ _)
  · exact Nat.le_add_right _ _

theorem tm3_sum (D : ℕ → ℝ) (a v x y z : ℕ) (hx : x ≤ 25) (hy : y ≤ 25) (hz : z ≤ 25) (l : List (ℕ × ℕ)) :
    ((tm3 a v x y z l).map (fun t => (t.1 : ℝ) * M2 D t.2)).sum
      = (if x = a then (v : ℝ) * (D y * D z) else 0) + (if x = a then (v : ℝ) * (D z * D y) else 0)
        + (if y = a then (v : ℝ) * (D x * D z) else 0) + (if y = a then (v : ℝ) * (D z * D x) else 0)
        + (if z = a then (v : ℝ) * (D x * D y) else 0) + (if z = a then (v : ℝ) * (D y * D x) else 0)
        + (l.map (fun t => (t.1 : ℝ) * M2 D t.2)).sum := by
  unfold tm3
  rw [p3_sum D a v x y z hz, p3_sum D a v x z y hy, p3_sum D a v y x z hz, p3_sum D a v y z x hx,
    p3_sum D a v z x y hy, p3_sum D a v z y x hx]
  ring

theorem tm3_keys (a v x y z : ℕ) (hx : x ≤ 25) (hy : y ≤ 25) (hz : z ≤ 25) (l : List (ℕ × ℕ)) (t : ℕ × ℕ)
    (ht : t ∈ tm3 a v x y z l) : t.2 < 676 ∨ t ∈ l := by
  unfold tm3 at ht
  rcases p3_keys _ _ _ _ _ hy hz _ t ht with h | h
  · exact Or.inl h
  rcases p3_keys _ _ _ _ _ hz hy _ t h with h | h
  · exact Or.inl h
  rcases p3_keys _ _ _ _ _ hx hz _ t h with h | h
  · exact Or.inl h
  rcases p3_keys _ _ _ _ _ hz hx _ t h with h | h
  · exact Or.inl h
  rcases p3_keys _ _ _ _ _ hx hy _ t h with h | h
  · exact Or.inl h
  exact p3_keys _ _ _ _ _ hy hx _ t h

theorem tm3_tot (a v x y z : ℕ) (l : List (ℕ × ℕ)) : tot (tm3 a v x y z l) ≤ tot l + 6 * v := by
  unfold tm3
  have h1 := p3_tot a v z y x l
  have h2 := p3_tot a v z x y (p3 a v z y x l)
  have h3 := p3_tot a v y z x (p3 a v z x y (p3 a v z y x l))
  have h4 := p3_tot a v y x z (p3 a v y z x (p3 a v z x y (p3 a v z y x l)))
  have h5 := p3_tot a v x z y (p3 a v y x z (p3 a v y z x (p3 a v z x y (p3 a v z y x l))))
  have h6 := p3_tot a v x y z (p3 a v x z y (p3 a v y x z (p3 a v y z x (p3 a v z x y (p3 a v z y x l)))))
  omega

theorem sum_pick (D : ℕ → ℝ) (hD : Supp25 D) (x : ℕ) (hx : x ≤ 25) (W : ℝ) :
    ∑ a ∈ range 25, D a * (if x = a then W else 0) = D x * W := by
  have e : ∀ a ∈ range 25, D a * (if x = a then W else 0) = if x = a then D a * W else 0 := by
    intro a _
    split_ifs <;> ring
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq (range 25) x (fun a => D a * W)]
  by_cases h : x < 25
  · rw [if_pos (mem_range.mpr h)]
  · rw [if_neg (by rw [mem_range]; exact h), hD x (by omega), zero_mul]

/-- The terms of degree 3 by rows, for a list of slots: the sum, the keys and the total. -/
theorem terms3r_gen (w c : ℕ) (g : List ℕ) (D : ℕ → ℝ) (hD : Supp25 D) (L : List (ℕ × ℕ × ℕ × ℕ)) :
    (∑ a ∈ range 25, D a * ((List.rec (motive := fun _ => List (ℕ × ℕ)) []
        (fun t _ ih => tm3 a (slot w c t.1) (cl (lgetD 25 g t.2.1)) (cl (lgetD 25 g t.2.2.1))
          (cl (lgetD 25 g t.2.2.2)) ih) L).map (fun t => (t.1 : ℝ) * M2 D t.2)).sum
      = 6 * (L.map (fun t => (slot w c t.1 : ℝ)
          * (D (lgetD 25 g t.2.1) * D (lgetD 25 g t.2.2.1) * D (lgetD 25 g t.2.2.2)))).sum)
    ∧ ∀ a, (∀ t ∈ (List.rec (motive := fun _ => List (ℕ × ℕ)) []
        (fun t _ ih => tm3 a (slot w c t.1) (cl (lgetD 25 g t.2.1)) (cl (lgetD 25 g t.2.2.1))
          (cl (lgetD 25 g t.2.2.2)) ih) L), t.2 < 676)
      ∧ tot (List.rec (motive := fun _ => List (ℕ × ℕ)) []
        (fun t _ ih => tm3 a (slot w c t.1) (cl (lgetD 25 g t.2.1)) (cl (lgetD 25 g t.2.2.1))
          (cl (lgetD 25 g t.2.2.2)) ih) L) ≤ 6 * (L.map (fun t => slot w c t.1)).sum := by
  induction L with
  | nil =>
    refine ⟨?_, fun a => ⟨fun t ht => absurd ht List.not_mem_nil, le_refl 0⟩⟩
    show ∑ a ∈ range 25, D a * (0 : ℝ) = 6 * 0
    simp
  | cons u L ih =>
    obtain ⟨ihs, ihk⟩ := ih
    have hx := cl_le (lgetD 25 g u.2.1)
    have hy := cl_le (lgetD 25 g u.2.2.1)
    have hz := cl_le (lgetD 25 g u.2.2.2)
    constructor
    · have step : ∀ a ∈ range 25, D a * ((tm3 a (slot w c u.1) (cl (lgetD 25 g u.2.1))
            (cl (lgetD 25 g u.2.2.1)) (cl (lgetD 25 g u.2.2.2))
            (List.rec (motive := fun _ => List (ℕ × ℕ)) []
              (fun t _ ih => tm3 a (slot w c t.1) (cl (lgetD 25 g t.2.1)) (cl (lgetD 25 g t.2.2.1))
                (cl (lgetD 25 g t.2.2.2)) ih) L)).map (fun t => (t.1 : ℝ) * M2 D t.2)).sum
          = D a * (if cl (lgetD 25 g u.2.1) = a then (slot w c u.1 : ℝ)
                * (D (cl (lgetD 25 g u.2.2.1)) * D (cl (lgetD 25 g u.2.2.2))) else 0)
            + D a * (if cl (lgetD 25 g u.2.1) = a then (slot w c u.1 : ℝ)
                * (D (cl (lgetD 25 g u.2.2.2)) * D (cl (lgetD 25 g u.2.2.1))) else 0)
            + D a * (if cl (lgetD 25 g u.2.2.1) = a then (slot w c u.1 : ℝ)
                * (D (cl (lgetD 25 g u.2.1)) * D (cl (lgetD 25 g u.2.2.2))) else 0)
            + D a * (if cl (lgetD 25 g u.2.2.1) = a then (slot w c u.1 : ℝ)
                * (D (cl (lgetD 25 g u.2.2.2)) * D (cl (lgetD 25 g u.2.1))) else 0)
            + D a * (if cl (lgetD 25 g u.2.2.2) = a then (slot w c u.1 : ℝ)
                * (D (cl (lgetD 25 g u.2.1)) * D (cl (lgetD 25 g u.2.2.1))) else 0)
            + D a * (if cl (lgetD 25 g u.2.2.2) = a then (slot w c u.1 : ℝ)
                * (D (cl (lgetD 25 g u.2.2.1)) * D (cl (lgetD 25 g u.2.1))) else 0)
            + D a * ((List.rec (motive := fun _ => List (ℕ × ℕ)) []
              (fun t _ ih => tm3 a (slot w c t.1) (cl (lgetD 25 g t.2.1)) (cl (lgetD 25 g t.2.2.1))
                (cl (lgetD 25 g t.2.2.2)) ih) L).map (fun t => (t.1 : ℝ) * M2 D t.2)).sum := by
        intro a _
        rw [tm3_sum D a _ _ _ _ hx hy hz]
        ring
      refine Eq.trans (Finset.sum_congr rfl step) ?_
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, ihs, sum_pick D hD _ hx, sum_pick D hD _ hx,
        sum_pick D hD _ hy, sum_pick D hD _ hy, sum_pick D hD _ hz, sum_pick D hD _ hz, D_cl hD, D_cl hD,
        D_cl hD, List.map_cons, List.sum_cons]
      ring
    · intro a
      obtain ⟨ihk1, ihk2⟩ := ihk a
      constructor
      · intro t ht
        rcases tm3_keys _ _ _ _ _ hx hy hz _ t ht with h | h
        · exact h
        · exact ihk1 t h
      · have h1 := tm3_tot a (slot w c u.1) (cl (lgetD 25 g u.2.1)) (cl (lgetD 25 g u.2.2.1))
          (cl (lgetD 25 g u.2.2.2)) (List.rec (motive := fun _ => List (ℕ × ℕ)) []
            (fun t _ ih => tm3 a (slot w c t.1) (cl (lgetD 25 g t.2.1)) (cl (lgetD 25 g t.2.2.1))
              (cl (lgetD 25 g t.2.2.2)) ih) L)
        rw [List.map_cons, List.sum_cons]
        refine le_trans h1 ?_
        omega

theorem terms3r_sum (w c : ℕ) (g : List ℕ) (D : ℕ → ℝ) (hD : Supp25 D) :
    ∑ a ∈ range 25, D a * ((terms3r w c g a).map (fun t => (t.1 : ℝ) * M2 D t.2)).sum
      = 6 * (slots3.map (fun t => (slot w c t.1 : ℝ)
          * (D (lgetD 25 g t.2.1) * D (lgetD 25 g t.2.2.1) * D (lgetD 25 g t.2.2.2)))).sum :=
  (terms3r_gen w c g D hD slots3).1

theorem terms3r_keys (w c : ℕ) (g : List ℕ) (a : ℕ) : ∀ t ∈ terms3r w c g a, t.2 < 676 :=
  ((terms3r_gen w c g (fun _ => 0) (fun _ _ => rfl) slots3).2 a).1

theorem terms3r_tot (w c : ℕ) (g : List ℕ) (a : ℕ) : tot (terms3r w c g a) ≤ 6 * rsumK w c sl3 := by
  have h := ((terms3r_gen w c g (fun _ => 0) (fun _ _ => rfl) slots3).2 a).2
  rw [rsumK_eq, sl3_eq, List.map_map]
  exact h

theorem tot3_le (w : ℕ) (f : PairD → ℕ) (a : ℕ) (pairs : List PairD) :
    totL (fun d => terms3r w (f d) (gl d.i d.j) a) pairs ≤ 6 * tot3 w f pairs := by
  induction pairs with
  | nil => exact le_refl 0
  | cons d ps ih =>
    show totL (fun d => terms3r w (f d) (gl d.i d.j) a) ps + tot (terms3r w (f d) (gl d.i d.j) a)
      ≤ 6 * (tot3 w f ps + rsumK w (f d) sl3)
    have := terms3r_tot w (f d) (gl d.i d.j) a
    omega

theorem rec_all2 (p q : ℕ → Bool) (N : ℕ)
    (h : Nat.rec (motive := fun _ => Bool) true (fun n ih => ih && p n && q n) N = true) :
    ∀ n, n < N → p n = true ∧ q n = true := by
  induction N with
  | zero =>
    intro n hn
    omega
  | succ N ih =>
    have h' : (Nat.rec (motive := fun _ => Bool) true (fun n ih => ih && p n && q n) N && p N && q N) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h'
    intro n hn
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h1 | h1
    · exact ih h'.1.1 n h1
    · rw [h1]
      exact ⟨h'.1.2, h'.2⟩

/-- **The form of the centres of degree 3** of all pairs is bounded. -/
theorem cub_bound (w : ℕ) (pairs : List PairD) (C : CubD) (hC : cubOk w pairs C = true) (D : ℕ → ℝ)
    (hD : Supp25 D) :
    (6 * (pairs.map (fun d => cform w d.cP d.cN 3 (lx (xd d D)))).sum) ^ 2 ≤ (C.A3 : ℝ) * nsq D * nsq D ^ 2
      ∧ (1000000 : ℝ) * (C.A3 : ℝ) ≤ (30234 * 2 ^ 48) ^ 2 := by
  have h' : (Nat.beq C.Pp.n 25
      && Nat.ble (Nat.mul 1000000 C.A3) (Nat.pow (Nat.mul 30234 (Nat.shiftLeft 1 48)) 2)
      && Nat.blt (Nat.mul 6 (tot3 w (fun d => d.cP) pairs)) (Nat.shiftLeft 1 64)
      && Nat.blt (Nat.mul 6 (tot3 w (fun d => d.cN) pairs)) (Nat.shiftLeft 1 64)
      && cubRows w pairs C
      && CAP.PSD.check C.Pp C.rows C.cols
      && triAll C.Pp.w 25 C.rows (cEntry C.Pp.a C.A3 C.TP C.TN)) = true := hC
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨⟨n1, a1⟩, t1⟩, t2⟩, r1⟩, c1⟩, l1⟩ := h'
  have hn := Nat.eq_of_beq_eq_true n1
  have hrows := rec_all2 (fun a => Nat.beq (lgetD 0 C.TP a) (scatL (fun d => terms3r w d.cP (gl d.i d.j) a) pairs))
    (fun a => Nat.beq (lgetD 0 C.TN a) (scatL (fun d => terms3r w d.cN (gl d.i d.j) a) pairs)) 25 r1
  have hTP : ∀ a, a < 25 → lgetD 0 C.TP a = scat (cat (fun d => terms3r w d.cP (gl d.i d.j) a) pairs) := by
    intro a ha
    rw [← scatL_eq]
    exact Nat.eq_of_beq_eq_true (hrows a ha).1
  have hTN : ∀ a, a < 25 → lgetD 0 C.TN a = scat (cat (fun d => terms3r w d.cN (gl d.i d.j) a) pairs) := by
    intro a ha
    rw [← scatL_eq]
    exact Nat.eq_of_beq_eq_true (hrows a ha).2
  have hkP : ∀ a, a < 25 → ∀ t ∈ cat (fun d => terms3r w d.cP (gl d.i d.j) a) pairs, t.2 < 676 := by
    intro a _ t ht
    obtain ⟨d, _, hd⟩ := mem_cat ht
    exact terms3r_keys _ _ _ _ t hd
  have hkN : ∀ a, a < 25 → ∀ t ∈ cat (fun d => terms3r w d.cN (gl d.i d.j) a) pairs, t.2 < 676 := by
    intro a _ t ht
    obtain ⟨d, _, hd⟩ := mem_cat ht
    exact terms3r_keys _ _ _ _ t hd
  have htP : ∀ a, a < 25 → tot (cat (fun d => terms3r w d.cP (gl d.i d.j) a) pairs) < 2 ^ 64 := by
    intro a _
    have h1 := Nat.blt_eq.mp t1
    rw [show Nat.shiftLeft 1 64 = 2 ^ 64 from Nat.one_shiftLeft 64] at h1
    rw [← totL_eq]
    exact lt_of_le_of_lt (tot3_le w (fun d => d.cP) a pairs) h1
  have htN : ∀ a, a < 25 → tot (cat (fun d => terms3r w d.cN (gl d.i d.j) a) pairs) < 2 ^ 64 := by
    intro a _
    have h1 := Nat.blt_eq.mp t2
    rw [show Nat.shiftLeft 1 64 = 2 ^ 64 from Nat.one_shiftLeft 64] at h1
    rw [← totL_eq]
    exact lt_of_le_of_lt (tot3_le w (fun d => d.cN) a pairs) h1
  have hf := cub_form (fun a => cat (fun d => terms3r w d.cP (gl d.i d.j) a) pairs)
    (fun a => cat (fun d => terms3r w d.cN (gl d.i d.j) a) pairs) hkP hkN htP htN C hn hTP hTN c1 l1 D (M2 D)
  -- the squares of the monomials
  have e26 : ∑ a ∈ range 26, D a ^ 2 = nsq D := by
    rw [Finset.sum_range_succ, hD 25 (le_refl _)]
    unfold nsq
    ring
  have hM : ∑ k ∈ range 676, M2 D k ^ 2 = nsq D ^ 2 := by
    rw [show (676 : ℕ) = 26 * 26 from rfl, sum_range_mul 26 26]
    have e1 : ∀ a ∈ range 26, ∑ b ∈ range 26, M2 D (26 * a + b) ^ 2 = D a ^ 2 * nsq D := by
      intro a _
      rw [← e26, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      have hb' := mem_range.mp hb
      unfold M2
      rw [show (26 * a + b) / 26 = a by omega, show (26 * a + b) % 26 = b by omega]
      ring
    rw [Finset.sum_congr rfl e1, ← Finset.sum_mul, e26]
    ring
  -- the form of the centres
  have hS : ∑ a ∈ range 25, D a * (((cat (fun d => terms3r w d.cP (gl d.i d.j) a) pairs).map
          (fun t => (t.1 : ℝ) * M2 D t.2)).sum
        - ((cat (fun d => terms3r w d.cN (gl d.i d.j) a) pairs).map (fun t => (t.1 : ℝ) * M2 D t.2)).sum)
      = 6 * (pairs.map (fun d => cform w d.cP d.cN 3 (lx (xd d D)))).sum := by
    have e1 : ∀ a ∈ range 25, D a * (((cat (fun d => terms3r w d.cP (gl d.i d.j) a) pairs).map
          (fun t => (t.1 : ℝ) * M2 D t.2)).sum
        - ((cat (fun d => terms3r w d.cN (gl d.i d.j) a) pairs).map (fun t => (t.1 : ℝ) * M2 D t.2)).sum)
        = (pairs.map (fun d => D a * (((terms3r w d.cP (gl d.i d.j) a).map
              (fun t => (t.1 : ℝ) * M2 D t.2)).sum
            - ((terms3r w d.cN (gl d.i d.j) a).map (fun t => (t.1 : ℝ) * M2 D t.2)).sum))).sum := by
      intro a _
      rw [sum_cat, sum_cat, ← list_sum_sub, ← list_sum_mul_left]
    rw [Finset.sum_congr rfl e1, sum_list_comm, ← list_sum_mul_left]
    refine list_sum_congr _ _ _ fun d _ => ?_
    have e2 : ∀ a ∈ range 25, D a * (((terms3r w d.cP (gl d.i d.j) a).map
          (fun t => (t.1 : ℝ) * M2 D t.2)).sum
        - ((terms3r w d.cN (gl d.i d.j) a).map (fun t => (t.1 : ℝ) * M2 D t.2)).sum)
        = D a * ((terms3r w d.cP (gl d.i d.j) a).map (fun t => (t.1 : ℝ) * M2 D t.2)).sum
          - D a * ((terms3r w d.cN (gl d.i d.j) a).map (fun t => (t.1 : ℝ) * M2 D t.2)).sum :=
      fun a _ => mul_sub _ _ _
    rw [Finset.sum_congr rfl e2, Finset.sum_sub_distrib, terms3r_sum w d.cP _ D hD,
      terms3r_sum w d.cN _ D hD, cform_s3, ← mul_sub, ← list_sum_sub]
    refine congrArg (fun y : ℝ => 6 * y) ?_
    refine list_sum_congr _ _ _ fun t _ => ?_
    show _ = ((slot w d.cP t.1 : ℝ) - (slot w d.cN t.1 : ℝ))
      * (D (lgetD 25 (gl d.i d.j) t.2.1) * D (lgetD 25 (gl d.i d.j) t.2.2.1)
        * D (lgetD 25 (gl d.i d.j) t.2.2.2))
    ring
  rw [hS, hM] at hf
  refine ⟨hf, ?_⟩
  have h2 := Nat.ble_eq.mp a1
  have h3 : 1000000 * C.A3 ≤ (30234 * 2 ^ 48) ^ 2 := by
    rw [show Nat.shiftLeft 1 48 = 2 ^ 48 from Nat.one_shiftLeft 48] at h2
    exact h2
  exact_mod_cast h3

end N14.Local

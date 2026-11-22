module

public import N14.Local.Global

/-!
# Statement 7 of T7: the theorem

`local7`: the expansion of the energy in the gauge coordinates, from the checkers of the 91 pairs and of the
three forms. See `N14/Local/Global.lean` for the statement in words.

* `rows_bound`: the sum over the pairs of the bounds of the quartic remainders is at most `147 |D|⁴` (the test
  `rowsOk`: for every point, twice the sum over the pairs that contain it is at most 147).
* `energyG_pairs`: the energy in the gauge is the sum over the pairs of the functions of their expressions.
-/

@[expose] public section

namespace N14.Local

open CAP Finset N14.Jet Real

/-! ## The rows -/

theorem sum_sq_le_sq_sum (s : Finset ℕ) (b : ℕ → ℝ) (hb : ∀ n ∈ s, 0 ≤ b n) :
    ∑ n ∈ s, b n ^ 2 ≤ (∑ n ∈ s, b n) ^ 2 := by
  have h1 : ∀ n ∈ s, b n ^ 2 ≤ b n * ∑ m ∈ s, b m := fun n hn => by
    rw [sq]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hb hn) (hb n hn)
  calc ∑ n ∈ s, b n ^ 2 ≤ ∑ n ∈ s, b n * ∑ m ∈ s, b m := Finset.sum_le_sum h1
    _ = (∑ n ∈ s, b n) ^ 2 := by rw [← Finset.sum_mul, sq]

/-- A sum over the pairs of a function of the two points, as a sum over the points. -/
theorem row_regroup (l : List PairD) (hl : ∀ d ∈ l, d.i < d.j ∧ d.j < 14) (σ : PairD → ℝ) (b : ℕ → ℝ) :
    (l.map (fun d => σ d * (b d.i + b d.j))).sum
      = ∑ n ∈ range 14, b n * (l.map (fun d => if d.i = n ∨ d.j = n then σ d else 0)).sum := by
  induction l with
  | nil => simp
  | cons d l ih =>
    obtain ⟨h1, h2⟩ := hl d (List.mem_cons.mpr (Or.inl rfl))
    rw [List.map_cons, List.sum_cons, ih fun e he => hl e (List.mem_cons.mpr (Or.inr he))]
    have e : ∀ n ∈ range 14, b n * ((d :: l).map (fun d => if d.i = n ∨ d.j = n then σ d else 0)).sum
        = (if d.i = n then b n * σ d else 0) + (if d.j = n then b n * σ d else 0)
          + b n * (l.map (fun d => if d.i = n ∨ d.j = n then σ d else 0)).sum := by
      intro n _
      rw [List.map_cons, List.sum_cons]
      by_cases hi : d.i = n
      · rw [if_pos (Or.inl hi), if_pos hi, if_neg (by omega)]
        ring
      · by_cases hj : d.j = n
        · rw [if_pos (Or.inr hj), if_neg hi, if_pos hj]
          ring
        · rw [if_neg (fun h => h.elim hi hj), if_neg hi, if_neg hj]
          ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq (range 14) d.i (fun n => b n * σ d), Finset.sum_ite_eq (range 14) d.j (fun n => b n * σ d),
      if_pos (mem_range.mpr (by omega)), if_pos (mem_range.mpr h2)]
    ring

theorem rowInt_cast (w n : ℕ) (l : List PairD) :
    (rowInt w n l : ℝ) = (l.map (fun d => if d.i = n ∨ d.j = n then (sInt w d : ℝ) else 0)).sum := by
  induction l with
  | nil =>
    show ((0 : ℕ) : ℝ) = 0
    exact Nat.cast_zero
  | cons d l ih =>
    have e : rowInt w n (d :: l) = rowInt w n l + cond (Nat.beq d.i n || Nat.beq d.j n) (sInt w d) 0 := rfl
    rw [e, List.map_cons, List.sum_cons, Nat.cast_add, ih]
    have e2 : ((cond (Nat.beq d.i n || Nat.beq d.j n) (sInt w d) 0 : ℕ) : ℝ)
        = if d.i = n ∨ d.j = n then (sInt w d : ℝ) else 0 := by
      by_cases h : d.i = n ∨ d.j = n
      · have hb : (Nat.beq d.i n || Nat.beq d.j n) = true := by
          rw [Bool.or_eq_true]
          rcases h with h | h
          · exact Or.inl (by rw [h]; exact Nat.beq_refl n)
          · exact Or.inr (by rw [h]; exact Nat.beq_refl n)
        rw [if_pos h, hb]
        rfl
      · have hb : (Nat.beq d.i n || Nat.beq d.j n) = false := by
          rw [Bool.or_eq_false_iff]
          constructor
          · cases hb : Nat.beq d.i n
            · rfl
            · exact absurd (Or.inl (Nat.eq_of_beq_eq_true hb)) h
          · cases hb : Nat.beq d.j n
            · rfl
            · exact absurd (Or.inr (Nat.eq_of_beq_eq_true hb)) h
        rw [if_neg h, hb]
        exact Nat.cast_zero
    rw [e2]
    ring

theorem radL_cast (w : ℕ) (l : List ℕ) (pairs : List PairD) :
    (radL w l pairs : ℝ) = (pairs.map (fun d => (rsumK w d.cR l : ℝ))).sum := by
  induction pairs with
  | nil =>
    show ((0 : ℕ) : ℝ) = 0
    exact Nat.cast_zero
  | cons d ps ih =>
    have e : radL w l (d :: ps) = radL w l ps + rsumK w d.cR l := rfl
    rw [e, Nat.cast_add, ih, List.map_cons, List.sum_cons]
    ring

/-- **The quartic remainders of all pairs.** -/
theorem rows_bound (w : ℕ) (pairs : List PairD) (hR : rowsOk w pairs = true)
    (hlt : ∀ d ∈ pairs, d.i < d.j ∧ d.j < 14) (D : ℕ → ℝ) (hD : Supp25 D) :
    (pairs.map (fun d => (sInt w d : ℝ) / (24 * 15625 * 2 ^ 48)
        * (xd d D 0 ^ 2 + xd d D 1 ^ 2 + xd d D 2 ^ 2 + xd d D 3 ^ 2) ^ 2)).sum ≤ 147 * nsq D ^ 2 := by
  have hrow := rec_all
    (fun n => Nat.ble (Nat.mul 2 (rowInt w n pairs)) (Nat.mul 55125000 (Nat.shiftLeft 1 48))) 14 hR
  have h25 : D 25 = 0 := hD 25 (le_refl _)
  have hden : (0 : ℝ) < 24 * 15625 * 2 ^ 48 := by norm_num
  have e1 : ∀ d ∈ pairs, (sInt w d : ℝ) / (24 * 15625 * 2 ^ 48)
        * (xd d D 0 ^ 2 + xd d D 1 ^ 2 + xd d D 2 ^ 2 + xd d D 3 ^ 2) ^ 2
      ≤ (sInt w d : ℝ) / (24 * 15625 * 2 ^ 48) * (2 * Bn D d.i ^ 2 + 2 * Bn D d.j ^ 2) := by
    intro d _
    have hn2 : xd d D 0 ^ 2 + xd d D 1 ^ 2 + xd d D 2 ^ 2 + xd d D 3 ^ 2 = Bn D d.i + Bn D d.j :=
      n2_pair d.i d.j D h25
    rw [hn2]
    refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (Nat.cast_nonneg _) hden.le)
    nlinarith [sq_nonneg (Bn D d.i - Bn D d.j)]
  refine le_trans (list_sum_le _ _ _ e1) ?_
  rw [row_regroup pairs hlt (fun d => (sInt w d : ℝ) / (24 * 15625 * 2 ^ 48)) (fun n => 2 * Bn D n ^ 2)]
  have e2 : ∀ n ∈ range 14, 2 * Bn D n ^ 2 * (pairs.map (fun d =>
        if d.i = n ∨ d.j = n then (sInt w d : ℝ) / (24 * 15625 * 2 ^ 48) else 0)).sum
      ≤ 147 * Bn D n ^ 2 := by
    intro n hn
    have h1 := Nat.ble_eq.mp (hrow n (mem_range.mp hn))
    have h2 : 2 * rowInt w n pairs ≤ 55125000 * 2 ^ 48 := by
      rw [show Nat.shiftLeft 1 48 = 2 ^ 48 from Nat.one_shiftLeft 48] at h1
      exact h1
    have h3 : (2 : ℝ) * (rowInt w n pairs : ℝ) ≤ 55125000 * 2 ^ 48 := by exact_mod_cast h2
    have h4 : (pairs.map (fun d =>
          if d.i = n ∨ d.j = n then (sInt w d : ℝ) / (24 * 15625 * 2 ^ 48) else 0)).sum
        = (rowInt w n pairs : ℝ) / (24 * 15625 * 2 ^ 48) := by
      rw [rowInt_cast, ← list_sum_div]
      refine list_sum_congr _ _ _ fun d _ => ?_
      split_ifs
      · rfl
      · rw [zero_div]
    rw [h4]
    have h5 : (rowInt w n pairs : ℝ) / (24 * 15625 * 2 ^ 48) ≤ 147 / 2 := by
      rw [div_le_iff₀ hden]
      linarith
    calc 2 * Bn D n ^ 2 * ((rowInt w n pairs : ℝ) / (24 * 15625 * 2 ^ 48))
        ≤ 2 * Bn D n ^ 2 * (147 / 2) :=
          mul_le_mul_of_nonneg_left h5 (mul_nonneg (by norm_num) (sq_nonneg _))
      _ = 147 * Bn D n ^ 2 := by ring
  refine le_trans (Finset.sum_le_sum e2) ?_
  rw [← Finset.mul_sum, ← sum_Bn D]
  exact mul_le_mul_of_nonneg_left (sum_sq_le_sq_sum _ _ fun n _ => Bn_nonneg D n) (by norm_num)

/-! ## The energy in the gauge -/

/-- The energy of the configuration with the gauge coordinates `q`. -/
noncomputable def energyG (q : ℕ → ℝ) : ℝ := energy (fun n : Fin 14 => gaugeN q n.val)

/-- **The energy in the gauge** is the sum over the pairs of the functions of their expressions. -/
theorem energyG_pairs (pairs : List PairD) (hidx : pairs.map (fun d => (d.i, d.j)) = allPairs) (D : ℕ → ℝ)
    (hD : ∀ k, |D k| ≤ 1 / 125) (hh : |hStar| ≤ 1 / 2) :
    energyG (qOf D) = (pairs.map (fun d => sem rho (pairExpW d.i d.j d.wit) (lx (xd d D)))).sum := by
  unfold energyG
  rw [energy_pairs _ (gaugeN (qOf D)) (fun n => rfl), ← hidx, List.map_map]
  refine list_sum_congr _ _ _ fun d hd => ?_
  have hmem : (d.i, d.j) ∈ allPairs := by
    rw [← hidx]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  obtain ⟨h1, h2⟩ := allPairs_lt _ hmem
  exact (pair_link D hD hh d.i d.j h1 h2 d.wit).symm

/-- The candidate is the configuration with the gauge coordinates `pStarN`. -/
theorem energy_Xstar_gauge : energy Xstar = energyG (qOf fun _ => 0) := by
  unfold energyG
  refine congrArg (energy (N := 14)) (funext fun n => ?_)
  have e : qOf (fun _ => 0) = pStarN := funext fun k => by
    unfold qOf
    rw [zero_add]
  rw [e, gauge_star n.val n.isLt]
  rfl

/-! ## The theorem -/

/-- **Statement 7 of T7**, the computational content of Proposition 9.1 of the source: the expansion of the
energy in the 25 gauge coordinates around the candidate, with a linear form `L`, a quadratic form `Q` that is
bounded from below, a cubic form `C` that is bounded, and a remainder of order four on the box of radius
`1/125`. A displacement is a function `D : ℕ → ℝ` that vanishes from the index 25 on. -/
def Local7 : Prop :=
  ∃ (L Q C : (ℕ → ℝ) → ℝ),
    (∀ (t : ℝ) (D : ℕ → ℝ), L (fun k => t * D k) = t * L D) ∧
    (∀ (t : ℝ) (D : ℕ → ℝ), Q (fun k => t * D k) = t ^ 2 * Q D) ∧
    (∀ (t : ℝ) (D : ℕ → ℝ), C (fun k => t * D k) = t ^ 3 * C D) ∧
    (∀ D : ℕ → ℝ, Supp25 D → (241 / 5000 : ℝ) * nsq D ≤ Q D) ∧
    (∀ D : ℕ → ℝ, Supp25 D → |C D| ≤ (126 / 25 : ℝ) * (nsq D * √(nsq D))) ∧
    ∀ D : ℕ → ℝ, Supp25 D → (∀ k, |D k| ≤ 1 / 125) →
      |energyG (qOf D) - energy Xstar - L D - Q D - C D| ≤ 147 * nsq D ^ 2

/-- **The theorem of statement 7**, from the checkers of the pairs and of the three forms. -/
theorem local7 (par : Par) (hs : par.s = 48) (tab : List T3) (htab : TabOk par.s tab rho) (pairs : List PairD)
    (hidx : pairs.map (fun d => (d.i, d.j)) = allPairs) (hpairs : ∀ d ∈ pairs, pairAll par tab d = true)
    (H : HessD) (C : CubD) (hforms : formsOk par.w pairs H C = true) (hh : |hStar| ≤ 1 / 2) : Local7 := by
  have hlt : ∀ d ∈ pairs, d.i < d.j ∧ d.j < 14 := by
    intro d hd
    have hmem : (d.i, d.j) ∈ allPairs := by
      rw [← hidx]
      exact List.mem_map.mpr ⟨d, hd, rfl⟩
    exact allPairs_lt _ hmem
  have hex : ∀ d : PairD, ∃ c : ℕ → ℝ, d ∈ pairs → PairS par d c := by
    intro d
    by_cases hd : d ∈ pairs
    · obtain ⟨c, hc⟩ := pair_stmt par hs tab htab d (hpairs d hd)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨fun _ => 0, fun h => absurd h hd⟩
  choose cf hcf using hex
  have hf : (hessOk par.w pairs H && cubOk par.w pairs C && rowsOk par.w pairs && budgetOk par.w pairs)
      = true := hforms
  simp only [Bool.and_eq_true] at hf
  obtain ⟨⟨⟨hH, hC⟩, hR⟩, hB⟩ := hf
  have hB' : (Nat.ble (Nat.mul 20000 (radL par.w sl2 pairs)) (Nat.shiftLeft 1 48)
      && Nat.ble (Nat.mul 1000 (radL par.w sl3 pairs)) (Nat.shiftLeft 1 48)) = true := hB
  rw [Bool.and_eq_true] at hB'
  have h48 : (2 : ℝ) ^ par.s = 281474976710656 := by
    rw [hs]
    norm_num
  -- the budgets of the radii
  have hb2 : (20000 : ℝ) * (pairs.map (fun d => (rsum par.w d.cR 2 : ℝ))).sum ≤ 281474976710656 := by
    have h1 := Nat.ble_eq.mp hB'.1
    rw [show Nat.shiftLeft 1 48 = 2 ^ 48 from Nat.one_shiftLeft 48] at h1
    have h2 : (20000 : ℝ) * (radL par.w sl2 pairs : ℝ) ≤ 2 ^ 48 := by exact_mod_cast h1
    rw [radL_cast] at h2
    have e : (pairs.map (fun d => (rsum par.w d.cR 2 : ℝ))).sum
        = (pairs.map (fun d => (rsumK par.w d.cR sl2 : ℝ))).sum :=
      list_sum_congr _ _ _ fun d _ => by rw [rsum_eq2]
    rw [e]
    norm_num at h2
    linarith
  have hb3 : (1000 : ℝ) * (pairs.map (fun d => (rsum par.w d.cR 3 : ℝ))).sum ≤ 281474976710656 := by
    have h1 := Nat.ble_eq.mp hB'.2
    rw [show Nat.shiftLeft 1 48 = 2 ^ 48 from Nat.one_shiftLeft 48] at h1
    have h2 : (1000 : ℝ) * (radL par.w sl3 pairs : ℝ) ≤ 2 ^ 48 := by exact_mod_cast h1
    rw [radL_cast] at h2
    have e : (pairs.map (fun d => (rsum par.w d.cR 3 : ℝ))).sum
        = (pairs.map (fun d => (rsumK par.w d.cR sl3 : ℝ))).sum :=
      list_sum_congr _ _ _ fun d _ => by rw [rsum_eq3]
    rw [e]
    norm_num at h2
    linarith
  refine ⟨fun D => (pairs.map (fun d => blk (cf d) 1 (lx (xd d D)))).sum,
    fun D => (pairs.map (fun d => blk (cf d) 2 (lx (xd d D)))).sum,
    fun D => (pairs.map (fun d => blk (cf d) 3 (lx (xd d D)))).sum, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t D
    show (pairs.map (fun d => blk (cf d) 1 (lx (xd d fun k => t * D k)))).sum
      = t * (pairs.map (fun d => blk (cf d) 1 (lx (xd d D)))).sum
    rw [← list_sum_mul_left]
    refine list_sum_congr _ _ _ fun d hd => ?_
    have h1 := blk_smul (cf d) (hcf d hd).supp 1 t (lx (xd d D))
    rw [pow_one] at h1
    exact h1
  · intro t D
    show (pairs.map (fun d => blk (cf d) 2 (lx (xd d fun k => t * D k)))).sum
      = t ^ 2 * (pairs.map (fun d => blk (cf d) 2 (lx (xd d D)))).sum
    rw [← list_sum_mul_left]
    exact list_sum_congr _ _ _ fun d hd => blk_smul (cf d) (hcf d hd).supp 2 t (lx (xd d D))
  · intro t D
    show (pairs.map (fun d => blk (cf d) 3 (lx (xd d fun k => t * D k)))).sum
      = t ^ 3 * (pairs.map (fun d => blk (cf d) 3 (lx (xd d D)))).sum
    rw [← list_sum_mul_left]
    exact list_sum_congr _ _ _ fun d hd => blk_smul (cf d) (hcf d hd).supp 3 t (lx (xd d D))
  · -- the Hessian
    intro D hD
    show (241 / 5000 : ℝ) * nsq D ≤ (pairs.map (fun d => blk (cf d) 2 (lx (xd d D)))).sum
    have hbnd := hess_bound par.w pairs H hH D hD
    have hdiff : |(pairs.map (fun d => 2 ^ par.s * blk (cf d) 2 (lx (xd d D))
          - cform par.w d.cP d.cN 2 (lx (xd d D)))).sum|
        ≤ (pairs.map (fun d => (rsum par.w d.cR 2 : ℝ) * nsq D)).sum := by
      refine abs_list_sum_le _ _ _ fun d hd => ?_
      have h1 := (hcf d hd).h2 (xd d D) (√(nsq D)) (fun k => abs_le_sqrt_nsq D hD _)
      rwa [Real.sq_sqrt (nsq_nonneg D)] at h1
    rw [list_sum_sub, list_sum_mul_left, list_sum_mul_right, h48] at hdiff
    have h2 := abs_le.mp hdiff
    have h3 : (pairs.map (fun d => (rsum par.w d.cR 2 : ℝ))).sum * nsq D
        ≤ 281474976710656 / 20000 * nsq D :=
      mul_le_mul_of_nonneg_right (by linarith) (nsq_nonneg D)
    linarith [h2.1]
  · -- the cubic form
    intro D hD
    show |(pairs.map (fun d => blk (cf d) 3 (lx (xd d D)))).sum| ≤ 126 / 25 * (nsq D * √(nsq D))
    obtain ⟨cb1, cb2⟩ := cub_bound par.w pairs C hC D hD
    have hY3 : √(nsq D) ^ 3 = nsq D * √(nsq D) := by
      calc √(nsq D) ^ 3 = √(nsq D) ^ 2 * √(nsq D) := by ring
        _ = nsq D * √(nsq D) := by rw [Real.sq_sqrt (nsq_nonneg D)]
    obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = nsq D * √(nsq D) := ⟨_, rfl⟩
    rw [← hY] at hY3 ⊢
    have hY0 : 0 ≤ Y := by
      rw [hY]
      exact mul_nonneg (nsq_nonneg D) (Real.sqrt_nonneg _)
    have hY2 : Y ^ 2 = nsq D * nsq D ^ 2 := by
      rw [hY, mul_pow, Real.sq_sqrt (nsq_nonneg D)]
      ring
    have hdiff : |(pairs.map (fun d => 2 ^ par.s * blk (cf d) 3 (lx (xd d D))
          - cform par.w d.cP d.cN 3 (lx (xd d D)))).sum|
        ≤ (pairs.map (fun d => (rsum par.w d.cR 3 : ℝ) * Y)).sum := by
      refine abs_list_sum_le _ _ _ fun d hd => ?_
      have h1 := (hcf d hd).h3 (xd d D) (√(nsq D)) (fun k => abs_le_sqrt_nsq D hD _)
      rwa [hY3] at h1
    rw [list_sum_sub, list_sum_mul_left, list_sum_mul_right, h48] at hdiff
    obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, C0 = (pairs.map (fun d => cform par.w d.cP d.cN 3 (lx (xd d D)))).sum :=
      ⟨_, rfl⟩
    rw [← hC0] at hdiff cb1
    have hsq : (6 * C0) ^ 2 ≤ (30234 * 281474976710656 / 1000 * Y) ^ 2 := by
      have hn3 : 0 ≤ nsq D * nsq D ^ 2 := mul_nonneg (nsq_nonneg D) (sq_nonneg _)
      have hA : (C.A3 : ℝ) ≤ (30234 * 281474976710656) ^ 2 / 1000000 := by
        rw [le_div_iff₀ (by norm_num)]
        have e48 : (2 : ℝ) ^ 48 = 281474976710656 := by norm_num
        rw [e48] at cb2
        linarith
      calc (6 * C0) ^ 2 ≤ (C.A3 : ℝ) * nsq D * nsq D ^ 2 := cb1
        _ = (C.A3 : ℝ) * (nsq D * nsq D ^ 2) := by ring
        _ ≤ (30234 * 281474976710656) ^ 2 / 1000000 * (nsq D * nsq D ^ 2) :=
            mul_le_mul_of_nonneg_right hA hn3
        _ = (30234 * 281474976710656 / 1000 * Y) ^ 2 := by
            have e : (30234 * 281474976710656 / 1000 * Y) ^ 2
                = (30234 * 281474976710656 / 1000 : ℝ) ^ 2 * Y ^ 2 := by ring
            rw [e, hY2]
            ring
    have h6 : |6 * C0| ≤ 30234 * 281474976710656 / 1000 * Y :=
      abs_le_of_sq_le_sq hsq (mul_nonneg (by norm_num) hY0)
    have h7 := abs_le.mp h6
    have h8 := abs_le.mp hdiff
    have h9 : (pairs.map (fun d => (rsum par.w d.cR 3 : ℝ))).sum * Y ≤ 281474976710656 / 1000 * Y :=
      mul_le_mul_of_nonneg_right (by linarith) hY0
    rw [abs_le]
    constructor <;> linarith [h7.1, h7.2, h8.1, h8.2]
  · -- the remainder
    intro D hD hDk
    show |energyG (qOf D) - energy Xstar - (pairs.map (fun d => blk (cf d) 1 (lx (xd d D)))).sum
        - (pairs.map (fun d => blk (cf d) 2 (lx (xd d D)))).sum
        - (pairs.map (fun d => blk (cf d) 3 (lx (xd d D)))).sum| ≤ 147 * nsq D ^ 2
    have hz : ∀ k : ℕ, |(fun _ : ℕ => (0 : ℝ)) k| ≤ 1 / 125 := fun k => by
      show |(0 : ℝ)| ≤ 1 / 125
      rw [abs_zero]
      norm_num
    rw [energyG_pairs pairs hidx D hDk hh, energy_Xstar_gauge, energyG_pairs pairs hidx (fun _ => 0) hz hh,
      ← list_sum_sub, ← list_sum_sub, ← list_sum_sub, ← list_sum_sub]
    refine le_trans (abs_list_sum_le _ _ _ fun d hd => ?_) (rows_bound par.w pairs hR hlt D hD)
    exact (hcf d hd).rem (xd d D) (fun k => hDk _)

end N14.Local

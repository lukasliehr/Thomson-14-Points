module

public import N14.Jet.SoundBase

/-!
# Jets: soundness of the checker, the product

The product of the packed numbers of two jets is the packed number of the convolution of their slots
(`CAP.packSum_mul_packSum`), and a slot `e < 1296` of it is `cv f g e = ∑_{i ≤ e} f i * g (e - i)` if no slot
overflows (`slot_mul`); the test of the checker, `(sum of all slots) * (sum of all slots) < 2 ^ w`, excludes
this (`convAt_le`). The four products of `jmul` give, slot by slot, the centre and the radius of the product of
the two enclosed polynomials (`prod_enc`), and the bound of order six is that of `Rep.mul` (`mulK_ge`).
-/

@[expose] public section

namespace N14.Jet

open CAP Finset

/-- A slot of the convolution is at most the product of the sums of the slots. -/
theorem convAt_le (n m : ℕ) (f g : ℕ → ℕ) (k : ℕ) :
    convAt n m f g k ≤ (∑ i ∈ range n, f i) * (∑ j ∈ range m, g j) := by
  unfold convAt
  have hg : ∀ i, (if k - i < m then g (k - i) else 0) ≤ ∑ j ∈ range m, g j := by
    intro i
    split_ifs with h
    · exact Finset.single_le_sum (f := g) (fun _ _ => Nat.zero_le _) (mem_range.mpr h)
    · exact Nat.zero_le _
  calc ∑ i ∈ range (k + 1), (if i < n then f i else 0) * (if k - i < m then g (k - i) else 0)
      ≤ ∑ i ∈ range (k + 1), (if i < n then f i else 0) * (∑ j ∈ range m, g j) :=
        sum_le_sum fun i _ => Nat.mul_le_mul_left _ (hg i)
    _ = (∑ i ∈ range (k + 1), if i < n then f i else 0) * (∑ j ∈ range m, g j) :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ i ∈ range n, f i) * (∑ j ∈ range m, g j) := by
        refine Nat.mul_le_mul_right _ ?_
        rw [← Finset.sum_filter]
        refine Finset.sum_le_sum_of_subset ?_
        intro i hi
        exact mem_range.mpr (mem_filter.mp hi).2

/-- The slot `e` of the convolution of two sequences. -/
def cv (f g : ℕ → ℕ) (e : ℕ) : ℕ := ∑ i ∈ range (e + 1), f i * g (e - i)

/-- **A slot of the product of two packed numbers.** -/
theorem slot_mul (w : ℕ) (f g : ℕ → ℕ)
    (hfg : (∑ i ∈ range 1296, f i) * (∑ j ∈ range 1296, g j) < 2 ^ w) (e : ℕ) (he : e < 1296) :
    slot w (packSum w 1296 f * packSum w 1296 g) e = cv f g e := by
  rw [packSum_mul_packSum w 1296 1296 f g (by norm_num) (by norm_num),
    slot_packSum w _ _ (fun k _ => lt_of_le_of_lt (convAt_le 1296 1296 f g k) hfg) e (by omega)]
  unfold convAt cv
  refine Finset.sum_congr rfl fun i hi => ?_
  have := mem_range.mp hi
  rw [if_pos (by omega), if_pos (by omega)]

/-- The centre and the radius of a product of two enclosed numbers. -/
theorem prod_enc (x y p1 n1 r1 p2 n2 r2 : ℝ) (hp1 : 0 ≤ p1) (hn1 : 0 ≤ n1) (hr1 : 0 ≤ r1) (hp2 : 0 ≤ p2)
    (hn2 : 0 ≤ n2) (hx : |x - (p1 - n1)| ≤ r1) (hy : |y - (p2 - n2)| ≤ r2) :
    |x * y - (2 * (p1 * p2 + n1 * n2) - (p1 + n1) * (p2 + n2))|
      ≤ (p1 + n1 + r1) * (p2 + n2 + r2) - (p1 + n1) * (p2 + n2) := by
  have gy := abs_le.mp hy
  have hr2 : 0 ≤ r2 := le_trans (abs_nonneg _) hy
  have e : x * y - (2 * (p1 * p2 + n1 * n2) - (p1 + n1) * (p2 + n2))
      = (x - (p1 - n1)) * y + (p1 - n1) * (y - (p2 - n2)) := by ring
  have t1 : |(x - (p1 - n1)) * y| ≤ r1 * (p2 + n2 + r2) := by
    rw [abs_mul]
    refine mul_le_mul hx ?_ (abs_nonneg _) hr1
    rw [abs_le]
    constructor <;> linarith [gy.1, gy.2]
  have t2 : |(p1 - n1) * (y - (p2 - n2))| ≤ (p1 + n1) * r2 := by
    rw [abs_mul]
    refine mul_le_mul ?_ hy (abs_nonneg _) (by linarith)
    rw [abs_le]
    constructor <;> linarith
  rw [e]
  calc |(x - (p1 - n1)) * y + (p1 - n1) * (y - (p2 - n2))|
      ≤ |(x - (p1 - n1)) * y| + |(p1 - n1) * (y - (p2 - n2))| := abs_add_le _ _
    _ ≤ r1 * (p2 + n2 + r2) + (p1 + n1) * r2 := add_le_add t1 t2
    _ = (p1 + n1 + r1) * (p2 + n2 + r2) - (p1 + n1) * (p2 + n2) := by ring

/-- The enclosure of the coefficients for all slots: outside the valid slots everything vanishes. -/
theorem enc_all {s : ℕ} {h : ℕ → T3} {c : ℕ → ℝ} (hc : Supp c) (he : Enc s h c) (e : ℕ) :
    |2 ^ s * c e - (((if Valid e then (h e).p else 0 : ℕ) : ℝ) - ((if Valid e then (h e).n else 0 : ℕ) : ℝ))|
      ≤ ((if Valid e then (h e).r else 0 : ℕ) : ℝ) := by
  by_cases hv : Valid e
  · rw [if_pos hv, if_pos hv, if_pos hv]
    exact he e hv
  · rw [if_neg hv, if_neg hv, if_neg hv, hc e hv]
    simp

/-- The triple of a slot of the product. -/
def mulH (par : Par) (a b : Jet) (e : ℕ) : T3 :=
  resc par.s (slot par.w (a.P * b.P) e + slot par.w (a.N * b.N) e)
    (slot par.w ((a.P + a.N) * (b.P + b.N)) e - (slot par.w (a.P * b.P) e + slot par.w (a.N * b.N) e))
    (slot par.w ((a.P + a.N + a.R) * (b.P + b.N + b.R)) e - slot par.w ((a.P + a.N) * (b.P + b.N)) e)

/-- The bound of order six of the product. -/
def mulK (par : Par) (a b : Jet) : ℕ :=
  cdiv (high par.w a b + pbound par.w a * b.K + a.K * (pbound par.w b + cdiv (b.K * 1291467969) 72)) par.s

theorem jmul_eq (par : Par) (a b : Jet) :
    jmul par a b = fin par (pass par.w (mulH par a b) idxs) (mulK par a b)
      (a.ok && b.ok && Nat.blt (Nat.mul (total par.w a) (total par.w b)) (Nat.shiftLeft 1 par.w)) := rfl

theorem sum_range6 (f : ℕ → ℝ) : ∑ d ∈ range 6, f d = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Finset.sum_range_succ]

theorem sum_high (g : ℕ → ℕ → ℝ) :
    (∑ d1 ∈ range 6, ∑ d2 ∈ range 6, if 6 ≤ d1 + d2 then g d1 d2 else 0)
      = (g 1 5 + g 2 4 + g 3 3 + g 4 2 + g 5 1) + (g 2 5 + g 3 4 + g 4 3 + g 5 2) + (g 3 5 + g 4 4 + g 5 3)
        + (g 4 5 + g 5 4) + g 5 5 := by
  simp [Finset.sum_range_succ]
  ring

attribute [local irreducible] nsum tsum

/-- The bound for the polynomial of a jet on the box, in units of `2^-s`. -/
theorem pbound_ge (w : ℕ) (a : Jet) (h : ℕ → T3) (pa : IsPass w a h) :
    (∑ d ∈ range 6, (nsum h d : ℝ) * rb ^ d) ≤ (pbound w a : ℝ) := by
  unfold pbound
  rw [pa.nd_eq 0 (by norm_num), pa.nd_eq 1 (by norm_num), pa.nd_eq 2 (by norm_num), pa.nd_eq 3 (by norm_num),
    pa.nd_eq 4 (by norm_num), pa.nd_eq 5 (by norm_num)]
  have c1 := cdiv_ge (nsum h 1 * 33) 12
  have c2 := cdiv_ge (nsum h 2 * 1089) 24
  have c3 := cdiv_ge (nsum h 3 * 35937) 36
  have c4 := cdiv_ge (nsum h 4 * 1185921) 48
  have c5 := cdiv_ge (nsum h 5 * 39135393) 60
  rw [sum_range6]
  show _ ≤ ((nsum h 0 + cdiv (nsum h 1 * 33) 12 + cdiv (nsum h 2 * 1089) 24 + cdiv (nsum h 3 * 35937) 36
    + cdiv (nsum h 4 * 1185921) 48 + cdiv (nsum h 5 * 39135393) 60 : ℕ) : ℝ)
  push_cast at c1 c2 c3 c4 c5 ⊢
  unfold rb
  norm_num at c1 c2 c3 c4 c5 ⊢
  linarith

/-- The bound for the terms of degree at least 6 of a product, in units of `2^(-2s)`. -/
theorem high_ge (w : ℕ) (a b : Jet) (ha hb : ℕ → T3) (pa : IsPass w a ha) (pb : IsPass w b hb) :
    (∑ d1 ∈ range 6, ∑ d2 ∈ range 6,
        if 6 ≤ d1 + d2 then (nsum ha d1 : ℝ) * (nsum hb d2 : ℝ) * rb ^ (d1 + d2 - 6) else 0)
      ≤ (high w a b : ℝ) := by
  unfold high
  rw [pa.nd_eq 1 (by norm_num), pa.nd_eq 2 (by norm_num), pa.nd_eq 3 (by norm_num),
    pa.nd_eq 4 (by norm_num), pa.nd_eq 5 (by norm_num), pb.nd_eq 1 (by norm_num), pb.nd_eq 2 (by norm_num),
    pb.nd_eq 3 (by norm_num), pb.nd_eq 4 (by norm_num), pb.nd_eq 5 (by norm_num)]
  have c7 := cdiv_ge ((nsum ha 2 * nsum hb 5 + nsum ha 3 * nsum hb 4 + nsum ha 4 * nsum hb 3
    + nsum ha 5 * nsum hb 2) * 33) 12
  have c8 := cdiv_ge ((nsum ha 3 * nsum hb 5 + nsum ha 4 * nsum hb 4 + nsum ha 5 * nsum hb 3) * 1089) 24
  have c9 := cdiv_ge ((nsum ha 4 * nsum hb 5 + nsum ha 5 * nsum hb 4) * 35937) 36
  have c10 := cdiv_ge (nsum ha 5 * nsum hb 5 * 1185921) 48
  rw [sum_high (fun d1 d2 => (nsum ha d1 : ℝ) * (nsum hb d2 : ℝ) * rb ^ (d1 + d2 - 6))]
  show _ ≤ (((nsum ha 1 * nsum hb 5 + nsum ha 2 * nsum hb 4 + nsum ha 3 * nsum hb 3 + nsum ha 4 * nsum hb 2
      + nsum ha 5 * nsum hb 1)
    + cdiv ((nsum ha 2 * nsum hb 5 + nsum ha 3 * nsum hb 4 + nsum ha 4 * nsum hb 3
      + nsum ha 5 * nsum hb 2) * 33) 12
    + cdiv ((nsum ha 3 * nsum hb 5 + nsum ha 4 * nsum hb 4 + nsum ha 5 * nsum hb 3) * 1089) 24
    + cdiv ((nsum ha 4 * nsum hb 5 + nsum ha 5 * nsum hb 4) * 35937) 36
    + cdiv (nsum ha 5 * nsum hb 5 * 1185921) 48 : ℕ) : ℝ)
  push_cast at c7 c8 c9 c10 ⊢
  unfold rb
  norm_num at c7 c8 c9 c10 ⊢
  linarith

/-- **The product of two jets.** -/
theorem good_mul (par : Par) (r : ℝ) (hr : r ≤ rb) (a b : Jet) (F1 F2 : (Fin 4 → ℝ) → ℝ)
    (h1 : Good par r a F1) (h2 : Good par r b F2) : Good par r (jmul par a b) (fun x => F1 x * F2 x) := by
  intro hok
  rw [jmul_eq] at hok ⊢
  obtain ⟨hab, hp⟩ := fin_isPass par _ _ _ hok
  rw [Bool.and_eq_true, Bool.and_eq_true] at hab
  obtain ⟨⟨oka, okb⟩, htot⟩ := hab
  obtain ⟨ha, c1, κ1, pa, ra, k1, K1, e1⟩ := h1 oka
  obtain ⟨hb, c2, κ2, pb, rb2, k2, K2, e2⟩ := h2 okb
  have hd : (0 : ℝ) < 2 ^ par.s := by positivity
  -- the test of the product of the sums
  have htot' : tsum ha * tsum hb < 2 ^ par.w := by
    have := Nat.blt_eq.mp htot
    rw [show Nat.shiftLeft 1 par.w = 2 ^ par.w from Nat.one_shiftLeft par.w] at this
    rw [← pa.total_eq, ← pb.total_eq]
    exact this
  -- the slots of the two jets, for all slots
  obtain ⟨P1, hP1⟩ : ∃ P1 : ℕ → ℕ, ∀ e, P1 e = if Valid e then (ha e).p else 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ → ℕ, ∀ e, N1 e = if Valid e then (ha e).n else 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨R1, hR1⟩ : ∃ R1 : ℕ → ℕ, ∀ e, R1 e = if Valid e then (ha e).r else 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ P2 : ℕ → ℕ, ∀ e, P2 e = if Valid e then (hb e).p else 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ → ℕ, ∀ e, N2 e = if Valid e then (hb e).n else 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨R2, hR2⟩ : ∃ R2 : ℕ → ℕ, ∀ e, R2 e = if Valid e then (hb e).r else 0 := ⟨_, fun _ => rfl⟩
  have hT1 : ∀ e, P1 e + N1 e + R1 e = if Valid e then (ha e).t else 0 := by
    intro e
    rw [hP1, hN1, hR1]
    by_cases hv : Valid e
    · rw [if_pos hv, if_pos hv, if_pos hv, if_pos hv]
      rfl
    · rw [if_neg hv, if_neg hv, if_neg hv, if_neg hv]
  have hT2 : ∀ e, P2 e + N2 e + R2 e = if Valid e then (hb e).t else 0 := by
    intro e
    rw [hP2, hN2, hR2]
    by_cases hv : Valid e
    · rw [if_pos hv, if_pos hv, if_pos hv, if_pos hv]
      rfl
    · rw [if_neg hv, if_neg hv, if_neg hv, if_neg hv]
  have sT1 : (∑ e ∈ range 1296, (P1 e + N1 e + R1 e)) = tsum ha := by
    unfold tsum
    exact Finset.sum_congr rfl fun e _ => hT1 e
  have sT2 : (∑ e ∈ range 1296, (P2 e + N2 e + R2 e)) = tsum hb := by
    unfold tsum
    exact Finset.sum_congr rfl fun e _ => hT2 e
  have eP1 : a.P = packSum par.w 1296 P1 := by
    rw [pa.hP]
    exact packSum_congr _ _ fun j _ => (hP1 j).symm
  have eN1 : a.N = packSum par.w 1296 N1 := by
    rw [pa.hN]
    exact packSum_congr _ _ fun j _ => (hN1 j).symm
  have eR1 : a.R = packSum par.w 1296 R1 := by
    rw [pa.hR]
    exact packSum_congr _ _ fun j _ => (hR1 j).symm
  have eP2 : b.P = packSum par.w 1296 P2 := by
    rw [pb.hP]
    exact packSum_congr _ _ fun j _ => (hP2 j).symm
  have eN2 : b.N = packSum par.w 1296 N2 := by
    rw [pb.hN]
    exact packSum_congr _ _ fun j _ => (hN2 j).symm
  have eR2 : b.R = packSum par.w 1296 R2 := by
    rw [pb.hR]
    exact packSum_congr _ _ fun j _ => (hR2 j).symm
  -- every product of two of the packed numbers has slots below 2^w
  have small : ∀ f g : ℕ → ℕ, (∀ e, f e ≤ P1 e + N1 e + R1 e) → (∀ e, g e ≤ P2 e + N2 e + R2 e) →
      (∑ i ∈ range 1296, f i) * (∑ j ∈ range 1296, g j) < 2 ^ par.w := by
    intro f g hf hg
    refine lt_of_le_of_lt (Nat.mul_le_mul ?_ ?_) htot'
    · rw [← sT1]
      exact sum_le_sum fun e _ => hf e
    · rw [← sT2]
      exact sum_le_sum fun e _ => hg e
  -- the four packed numbers
  have eA1 : a.P + a.N = packSum par.w 1296 (fun e => P1 e + N1 e) := by
    rw [eP1, eN1, ← packSum_add]
  have eA2 : b.P + b.N = packSum par.w 1296 (fun e => P2 e + N2 e) := by
    rw [eP2, eN2, ← packSum_add]
  have eT1 : a.P + a.N + a.R = packSum par.w 1296 (fun e => P1 e + N1 e + R1 e) := by
    rw [eA1, eR1, ← packSum_add]
  have eT2 : b.P + b.N + b.R = packSum par.w 1296 (fun e => P2 e + N2 e + R2 e) := by
    rw [eA2, eR2, ← packSum_add]
  have sPP : ∀ e, e < 1296 → slot par.w (a.P * b.P) e = cv P1 P2 e := fun e he => by
    rw [eP1, eP2]
    exact slot_mul par.w P1 P2 (small P1 P2 (fun e => by omega) (fun e => by omega)) e he
  have sNN : ∀ e, e < 1296 → slot par.w (a.N * b.N) e = cv N1 N2 e := fun e he => by
    rw [eN1, eN2]
    exact slot_mul par.w N1 N2 (small N1 N2 (fun e => by omega) (fun e => by omega)) e he
  have sAA : ∀ e, e < 1296 → slot par.w ((a.P + a.N) * (b.P + b.N)) e
      = cv (fun e => P1 e + N1 e) (fun e => P2 e + N2 e) e := fun e he => by
    rw [eA1, eA2]
    exact slot_mul par.w _ _ (small _ _ (fun e => by omega) (fun e => by omega)) e he
  have sTT : ∀ e, e < 1296 → slot par.w ((a.P + a.N + a.R) * (b.P + b.N + b.R)) e
      = cv (fun e => P1 e + N1 e + R1 e) (fun e => P2 e + N2 e + R2 e) e := fun e he => by
    rw [eT1, eT2]
    exact slot_mul par.w _ _ (small _ _ (fun e => le_refl _) (fun e => le_refl _)) e he
  -- the norms
  have hn1 : ∀ d, d < 6 → nrm c1 d ≤ (nsum ha d : ℝ) / 2 ^ par.s := fun d _ => nrm_le_of_enc ra.supp e1 d
  have hn2 : ∀ d, d < 6 → nrm c2 d ≤ (nsum hb d : ℝ) / 2 ^ par.s := fun d _ => nrm_le_of_enc rb2.supp e2 d
  have hrep := Rep.mul ra rb2 (fun d => (nsum ha d : ℝ) / 2 ^ par.s) (fun d => (nsum hb d : ℝ) / 2 ^ par.s)
    hn1 hn2 rb hr k1 k2
  have hrb0 : (0 : ℝ) ≤ rb := by
    unfold rb
    norm_num
  refine ⟨_, _, _, hp, hrep, ?_, ?_, ?_⟩
  · -- the bound is nonnegative
    have q1 : ∀ d, (0 : ℝ) ≤ (nsum ha d : ℝ) / 2 ^ par.s := fun d => div_nonneg (Nat.cast_nonneg _) hd.le
    have q2 : ∀ d, (0 : ℝ) ≤ (nsum hb d : ℝ) / 2 ^ par.s := fun d => div_nonneg (Nat.cast_nonneg _) hd.le
    have s1 : (0 : ℝ) ≤ ∑ d1 ∈ range 6, ∑ d2 ∈ range 6,
        if 6 ≤ d1 + d2 then (nsum ha d1 : ℝ) / 2 ^ par.s * ((nsum hb d2 : ℝ) / 2 ^ par.s) * rb ^ (d1 + d2 - 6)
        else 0 :=
      sum_nonneg fun d1 _ => sum_nonneg fun d2 _ => by
        split_ifs
        · exact mul_nonneg (mul_nonneg (q1 d1) (q2 d2)) (pow_nonneg hrb0 _)
        · exact le_refl 0
    have s2 : (0 : ℝ) ≤ ∑ d ∈ range 6, (nsum ha d : ℝ) / 2 ^ par.s * rb ^ d :=
      sum_nonneg fun d _ => mul_nonneg (q1 d) (pow_nonneg hrb0 d)
    have s3 : (0 : ℝ) ≤ ∑ d ∈ range 6, (nsum hb d : ℝ) / 2 ^ par.s * rb ^ d :=
      sum_nonneg fun d _ => mul_nonneg (q2 d) (pow_nonneg hrb0 d)
    have s4 : (0 : ℝ) ≤ κ2 * rb ^ 6 := mul_nonneg k2 (pow_nonneg hrb0 6)
    have := mul_nonneg s2 k2
    have := mul_nonneg k1 (add_nonneg s3 s4)
    linarith
  · -- the bound of order six
    show _ ≤ ((mulK par a b : ℕ) : ℝ)
    unfold mulK
    refine le_trans ?_ (cdiv_ge _ _)
    rw [le_div_iff₀ hd]
    have hH := high_ge par.w a b ha hb pa pb
    have hPa := pbound_ge par.w a ha pa
    have hPb := pbound_ge par.w b hb pb
    have hK6 : κ2 * 2 ^ par.s * rb ^ 6 ≤ (cdiv (b.K * 1291467969) 72 : ℝ) := by
      refine le_trans ?_ (cdiv_ge _ _)
      have e6 : rb ^ 6 = 1291467969 / 2 ^ 72 := by
        unfold rb
        norm_num
      rw [e6]
      push_cast
      have := mul_le_mul_of_nonneg_right K2 (by norm_num : (0 : ℝ) ≤ 1291467969 / 2 ^ 72)
      linarith
    -- the three parts, in units of 2^(-2s)
    have hd0 : (2 : ℝ) ^ par.s ≠ 0 := ne_of_gt hd
    have eH : (∑ d1 ∈ range 6, ∑ d2 ∈ range 6,
          if 6 ≤ d1 + d2 then (nsum ha d1 : ℝ) / 2 ^ par.s * ((nsum hb d2 : ℝ) / 2 ^ par.s) * rb ^ (d1 + d2 - 6)
          else 0) * 2 ^ par.s * 2 ^ par.s
        = ∑ d1 ∈ range 6, ∑ d2 ∈ range 6,
          if 6 ≤ d1 + d2 then (nsum ha d1 : ℝ) * (nsum hb d2 : ℝ) * rb ^ (d1 + d2 - 6) else 0 := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d1 _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d2 _ => ?_
      generalize (nsum ha d1 : ℝ) = A
      generalize (nsum hb d2 : ℝ) = B
      generalize rb ^ (d1 + d2 - 6) = C
      split_ifs
      · field_simp
      · rw [zero_mul, zero_mul]
    have ePa : (∑ d ∈ range 6, (nsum ha d : ℝ) / 2 ^ par.s * rb ^ d) * 2 ^ par.s
        = ∑ d ∈ range 6, (nsum ha d : ℝ) * rb ^ d := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      generalize (nsum ha d : ℝ) = A
      generalize rb ^ d = C
      field_simp
    have ePb : (∑ d ∈ range 6, (nsum hb d : ℝ) / 2 ^ par.s * rb ^ d) * 2 ^ par.s
        = ∑ d ∈ range 6, (nsum hb d : ℝ) * rb ^ d := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      generalize (nsum hb d : ℝ) = A
      generalize rb ^ d = C
      field_simp
    set SH := ∑ d1 ∈ range 6, ∑ d2 ∈ range 6,
      if 6 ≤ d1 + d2 then (nsum ha d1 : ℝ) / 2 ^ par.s * ((nsum hb d2 : ℝ) / 2 ^ par.s) * rb ^ (d1 + d2 - 6)
      else 0 with hSH
    set SA := ∑ d ∈ range 6, (nsum ha d : ℝ) / 2 ^ par.s * rb ^ d with hSA
    set SB := ∑ d ∈ range 6, (nsum hb d : ℝ) / 2 ^ par.s * rb ^ d with hSB
    have hSA0 : (0 : ℝ) ≤ SA * 2 ^ par.s := by
      rw [ePa]
      exact sum_nonneg fun d _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hrb0 d)
    have hSB0 : (0 : ℝ) ≤ SB * 2 ^ par.s := by
      rw [ePb]
      exact sum_nonneg fun d _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hrb0 d)
    have hκ1 : (0 : ℝ) ≤ κ1 * 2 ^ par.s := mul_nonneg k1 hd.le
    have hκ2 : (0 : ℝ) ≤ κ2 * 2 ^ par.s := mul_nonneg k2 hd.le
    have hK60 : (0 : ℝ) ≤ κ2 * 2 ^ par.s * rb ^ 6 := mul_nonneg hκ2 (pow_nonneg hrb0 6)
    have m1 : (SA * 2 ^ par.s) * (κ2 * 2 ^ par.s) ≤ (pbound par.w a : ℝ) * (b.K : ℝ) :=
      mul_le_mul (by rw [ePa]; exact hPa) K2 hκ2 (Nat.cast_nonneg _)
    have m2 : (κ1 * 2 ^ par.s) * (SB * 2 ^ par.s + κ2 * 2 ^ par.s * rb ^ 6)
        ≤ (a.K : ℝ) * ((pbound par.w b : ℝ) + (cdiv (b.K * 1291467969) 72 : ℝ)) :=
      mul_le_mul K1 (add_le_add (by rw [ePb]; exact hPb) hK6) (add_nonneg hSB0 hK60) (Nat.cast_nonneg _)
    push_cast
    calc (SH + SA * κ2 + κ1 * (SB + κ2 * rb ^ 6)) * 2 ^ par.s * 2 ^ par.s
        = SH * 2 ^ par.s * 2 ^ par.s + (SA * 2 ^ par.s) * (κ2 * 2 ^ par.s)
          + (κ1 * 2 ^ par.s) * (SB * 2 ^ par.s + κ2 * 2 ^ par.s * rb ^ 6) := by ring
      _ ≤ (high par.w a b : ℝ) + (pbound par.w a : ℝ) * (b.K : ℝ)
          + (a.K : ℝ) * ((pbound par.w b : ℝ) + (cdiv (b.K * 1291467969) 72 : ℝ)) := by
          rw [eH]
          linarith
  · -- the coefficients
    intro e hv
    have he := hv.1
    show |2 ^ par.s * cmul c1 c2 e - (((mulH par a b e).p : ℝ) - (mulH par a b e).n)| ≤ (mulH par a b e).r
    unfold mulH
    rw [sPP e he, sNN e he, sAA e he, sTT e he]
    -- the convolution of the real coefficients
    have hd0 : (2 : ℝ) ^ par.s ≠ 0 := ne_of_gt hd
    have hcm : 2 ^ par.s * cmul c1 c2 e
        = (∑ i ∈ range (e + 1), (2 ^ par.s * c1 i) * (2 ^ par.s * c2 (e - i))) / 2 ^ par.s := by
      unfold cmul
      rw [if_pos he, Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [hcm]
    refine resc_sound par.s _ _ _ _ ?_
    -- the sums of the checker are sums of real numbers
    have hle1 : cv P1 P2 e + cv N1 N2 e ≤ cv (fun e => P1 e + N1 e) (fun e => P2 e + N2 e) e := by
      unfold cv
      rw [← Finset.sum_add_distrib]
      refine sum_le_sum fun i _ => ?_
      show P1 i * P2 (e - i) + N1 i * N2 (e - i) ≤ (P1 i + N1 i) * (P2 (e - i) + N2 (e - i))
      calc P1 i * P2 (e - i) + N1 i * N2 (e - i)
          ≤ P1 i * P2 (e - i) + N1 i * N2 (e - i) + (P1 i * N2 (e - i) + N1 i * P2 (e - i)) :=
            Nat.le_add_right _ _
        _ = (P1 i + N1 i) * (P2 (e - i) + N2 (e - i)) := by ring
    have hle2 : cv (fun e => P1 e + N1 e) (fun e => P2 e + N2 e) e
        ≤ cv (fun e => P1 e + N1 e + R1 e) (fun e => P2 e + N2 e + R2 e) e := by
      unfold cv
      refine sum_le_sum fun i _ => ?_
      exact Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    rw [Nat.cast_sub hle1, Nat.cast_sub hle2]
    unfold cv
    push_cast
    -- the five sums
    have key : ∀ i ∈ range (e + 1),
        |(2 ^ par.s * c1 i) * (2 ^ par.s * c2 (e - i))
          - (2 * ((P1 i : ℝ) * (P2 (e - i) : ℝ) + (N1 i : ℝ) * (N2 (e - i) : ℝ))
            - ((P1 i : ℝ) + (N1 i : ℝ)) * ((P2 (e - i) : ℝ) + (N2 (e - i) : ℝ)))|
        ≤ ((P1 i : ℝ) + (N1 i : ℝ) + (R1 i : ℝ)) * ((P2 (e - i) : ℝ) + (N2 (e - i) : ℝ) + (R2 (e - i) : ℝ))
          - ((P1 i : ℝ) + (N1 i : ℝ)) * ((P2 (e - i) : ℝ) + (N2 (e - i) : ℝ)) := by
      intro i _
      have g1 := enc_all ra.supp e1 i
      have g2 := enc_all rb2.supp e2 (e - i)
      rw [← hP1, ← hN1, ← hR1] at g1
      rw [← hP2, ← hN2, ← hR2] at g2
      exact prod_enc _ _ _ _ _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        (Nat.cast_nonneg _) (Nat.cast_nonneg _) g1 g2
    have hs1 : (∑ i ∈ range (e + 1), ((2 ^ par.s * c1 i) * (2 ^ par.s * c2 (e - i))
          - (2 * ((P1 i : ℝ) * (P2 (e - i) : ℝ) + (N1 i : ℝ) * (N2 (e - i) : ℝ))
            - ((P1 i : ℝ) + (N1 i : ℝ)) * ((P2 (e - i) : ℝ) + (N2 (e - i) : ℝ)))))
        = (∑ i ∈ range (e + 1), (2 ^ par.s * c1 i) * (2 ^ par.s * c2 (e - i)))
          - (2 * ((∑ i ∈ range (e + 1), (P1 i : ℝ) * (P2 (e - i) : ℝ))
              + ∑ i ∈ range (e + 1), (N1 i : ℝ) * (N2 (e - i) : ℝ))
            - ∑ i ∈ range (e + 1), ((P1 i : ℝ) + (N1 i : ℝ)) * ((P2 (e - i) : ℝ) + (N2 (e - i) : ℝ))) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
    have hs2 : (∑ i ∈ range (e + 1),
          (((P1 i : ℝ) + (N1 i : ℝ) + (R1 i : ℝ)) * ((P2 (e - i) : ℝ) + (N2 (e - i) : ℝ) + (R2 (e - i) : ℝ))
          - ((P1 i : ℝ) + (N1 i : ℝ)) * ((P2 (e - i) : ℝ) + (N2 (e - i) : ℝ))))
        = (∑ i ∈ range (e + 1),
            ((P1 i : ℝ) + (N1 i : ℝ) + (R1 i : ℝ)) * ((P2 (e - i) : ℝ) + (N2 (e - i) : ℝ) + (R2 (e - i) : ℝ)))
          - ∑ i ∈ range (e + 1), ((P1 i : ℝ) + (N1 i : ℝ)) * ((P2 (e - i) : ℝ) + (N2 (e - i) : ℝ)) :=
      Finset.sum_sub_distrib _ _
    have hfin := le_trans (Finset.abs_sum_le_sum_abs _ _) (sum_le_sum key)
    rw [hs1, hs2] at hfin
    refine le_trans (le_of_eq (congrArg abs ?_)) hfin
    ring

end N14.Jet

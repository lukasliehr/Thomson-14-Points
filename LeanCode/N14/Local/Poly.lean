module

public import N14.Jet.Sound
public import N14.Local.Scatter

/-!
# Statement 7 of T7, the assembly: the parts of a polynomial of a jet

A jet encloses a polynomial `c` of degree at most 5 in four variables (`N14.Jet.Rep`). This file contains what
the assembly needs about its parts `blk c d` of degree `d`:

* `blk_smul`: the part of degree `d` is homogeneous; `pev_split`, `pev_zero`.
* `cform w Pc Nc d x`: the form of degree `d` of the centres of a claim; `blk_enc`: the part of degree `d` of a
  polynomial that satisfies the claim differs from it by at most the sum `rsum` of the radii times `m^d`.
* `cform_s2`, `cform_s3`, `cform_s4`: the forms of the centres as sums over the lists `slots2`, `slots3`,
  `slots4` of the checker, with the monomials written as products of the local variables (`mval_s2`, …).
-/

@[expose] public section

namespace N14.Local

open CAP Finset N14.Jet

/-- The local point with the coordinates `xs 0, …, xs 3`. -/
def lx (xs : ℕ → ℝ) : Fin 4 → ℝ := fun k => xs k.val

/-! ## Homogeneity -/

theorem mval_smul (t : ℝ) (x : Fin 4 → ℝ) {e : ℕ} (he : Valid e) :
    mval e (fun k => t * x k) = t ^ sdeg e * mval e x := by
  have h := he.2
  obtain ⟨a0, ha0⟩ : ∃ a0, a0 = sdeg e - (sa1 e + sa2 e + sa3 e) := ⟨_, rfl⟩
  have hs : sdeg e = a0 + sa1 e + sa2 e + sa3 e := by omega
  show (t * x 0) ^ (sdeg e - (sa1 e + sa2 e + sa3 e)) * (t * x 1) ^ sa1 e * (t * x 2) ^ sa2 e
      * (t * x 3) ^ sa3 e
    = t ^ sdeg e * (x 0 ^ (sdeg e - (sa1 e + sa2 e + sa3 e)) * x 1 ^ sa1 e * x 2 ^ sa2 e * x 3 ^ sa3 e)
  rw [← ha0, hs, mul_pow, mul_pow, mul_pow, mul_pow, pow_add, pow_add, pow_add]
  ring

/-- **The part of degree `d` is homogeneous.** -/
theorem blk_smul (c : ℕ → ℝ) (hc : Supp c) (d : ℕ) (t : ℝ) (x : Fin 4 → ℝ) :
    blk c d (fun k => t * x k) = t ^ d * blk c d x := by
  unfold blk
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hd : sdeg e = d
  · rw [if_pos hd, if_pos hd]
    by_cases hv : Valid e
    · rw [mval_smul t x hv, hd]
      ring
    · rw [hc e hv]
      ring
  · rw [if_neg hd, if_neg hd, mul_zero]

theorem pev_split (c : ℕ → ℝ) (x : Fin 4 → ℝ) :
    pev c x = blk c 0 x + blk c 1 x + blk c 2 x + blk c 3 x + blk c 4 x + blk c 5 x := by
  rw [pev_eq_blk, sum_range6]

theorem blk_zero (c : ℕ → ℝ) (hc : Supp c) (d : ℕ) (hd : 1 ≤ d) : blk c d (fun _ => 0) = 0 := by
  have h := blk_smul c hc d 0 (fun _ => 0)
  have e : (fun k : Fin 4 => (0 : ℝ) * (fun _ : Fin 4 => (0 : ℝ)) k) = fun _ => 0 :=
    funext fun k => zero_mul _
  rw [e, zero_pow (by omega)] at h
  rw [h, zero_mul]

theorem blk_zero0 (c : ℕ → ℝ) (hc : Supp c) (x : Fin 4 → ℝ) : blk c 0 (fun _ => 0) = blk c 0 x := by
  have h := blk_smul c hc 0 0 x
  rw [pow_zero, one_mul] at h
  refine Eq.trans (congrArg (blk c 0) (funext fun k => ?_)) h
  exact (zero_mul (x k)).symm

/-- The value of the polynomial at the origin is its part of degree zero. -/
theorem pev_zero (c : ℕ → ℝ) (hc : Supp c) (x : Fin 4 → ℝ) : pev c (fun _ => 0) = blk c 0 x := by
  rw [pev_split, blk_zero c hc 1 (by norm_num), blk_zero c hc 2 (by norm_num), blk_zero c hc 3 (by norm_num),
    blk_zero c hc 4 (by norm_num), blk_zero c hc 5 (by norm_num), blk_zero0 c hc x]
  ring

/-! ## The forms of the centres -/

/-- The form of degree `d` of the centres of a claim, in units of `2^-s`. -/
noncomputable def cform (w Pc Nc d : ℕ) (x : Fin 4 → ℝ) : ℝ :=
  ∑ e ∈ range 1296,
    if Valid e ∧ sdeg e = d then ((slot w Pc e : ℝ) - (slot w Nc e : ℝ)) * mval e x else 0

/-- The sum of the radii of degree `d` of a claim. -/
def rsum (w Rc d : ℕ) : ℕ := ∑ e ∈ range 1296, if Valid e ∧ sdeg e = d then slot w Rc e else 0

/-- **The part of degree `d` of a polynomial of a claim and the form of the centres.** -/
theorem blk_enc {par : Par} {r : ℝ} {F : (Fin 4 → ℝ) → ℝ} {Pc Nc Rc n5c Kc : ℕ} {c : ℕ → ℝ} {κ : ℝ}
    (hC : Claim par r F Pc Nc Rc n5c Kc c κ) (d : ℕ) (h2 : 2 ≤ d) (h4 : d ≤ 4) (x : Fin 4 → ℝ) (m : ℝ)
    (hx : ∀ k, |x k| ≤ m) :
    |2 ^ par.s * blk c d x - cform par.w Pc Nc d x| ≤ (rsum par.w Rc d : ℝ) * m ^ d := by
  unfold blk cform rsum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Nat.cast_sum, Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (sum_le_sum fun e _ => ?_)
  by_cases hd : sdeg e = d
  · by_cases hv : Valid e
    · rw [if_pos hd, if_pos ⟨hv, hd⟩, if_pos ⟨hv, hd⟩]
      have g1 := hC.enc e hv (by omega) (by omega)
      have g2 := mval_abs_le x m hx hv
      rw [hd] at g2
      have e1 : 2 ^ par.s * (c e * mval e x) - ((slot par.w Pc e : ℝ) - (slot par.w Nc e : ℝ)) * mval e x
          = (2 ^ par.s * c e - ((slot par.w Pc e : ℝ) - (slot par.w Nc e : ℝ))) * mval e x := by ring
      rw [e1, abs_mul]
      exact mul_le_mul g1 g2 (abs_nonneg _) (Nat.cast_nonneg _)
    · rw [if_pos hd, if_neg (fun h => hv h.1), if_neg (fun h => hv h.1), hC.rep.supp e hv]
      simp
  · rw [if_neg hd, if_neg (fun h => hd h.2), if_neg (fun h => hd h.2)]
    simp

/-! ## The slots of a degree as a list -/

theorem sum_valid_deg {M : Type*} [AddCommMonoid M] (d : ℕ) (L : List ℕ) (hnd : L.Nodup)
    (hmem : ∀ e, e < 1296 → ((Valid e ∧ sdeg e = d) ↔ e ∈ L)) (hlt : ∀ e ∈ L, e < 1296) (f : ℕ → M) :
    (∑ e ∈ range 1296, if Valid e ∧ sdeg e = d then f e else 0) = (L.map f).sum := by
  rw [← Finset.sum_filter, ← List.sum_toFinset f hnd]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext e
  rw [Finset.mem_filter, mem_range, List.mem_toFinset]
  constructor
  · rintro ⟨h1, h2⟩
    exact (hmem e h1).mp h2
  · intro h
    exact ⟨hlt e h, (hmem e (hlt e h)).mpr h⟩

theorem sl2_mem : ∀ e, e < 1296 → ((Valid e ∧ sdeg e = 2) ↔ e ∈ sl2) := by decide +kernel

theorem sl3_mem : ∀ e, e < 1296 → ((Valid e ∧ sdeg e = 3) ↔ e ∈ sl3) := by decide +kernel

theorem sl4_mem : ∀ e, e < 1296 → ((Valid e ∧ sdeg e = 4) ↔ e ∈ sl4) := by decide +kernel

theorem sl2_nodup : sl2.Nodup := by decide +kernel

theorem sl3_nodup : sl3.Nodup := by decide +kernel

theorem sl4_nodup : sl4.Nodup := by decide +kernel

theorem sl2_lt : ∀ e ∈ sl2, e < 1296 := by decide +kernel

theorem sl3_lt : ∀ e ∈ sl3, e < 1296 := by decide +kernel

theorem sl4_lt : ∀ e ∈ sl4, e < 1296 := by decide +kernel

theorem sl2_eq : sl2 = slots2.map (fun t => t.1) := by decide +kernel

theorem sl3_eq : sl3 = slots3.map (fun t => t.1) := by decide +kernel

theorem sl4_eq : sl4 = slots4.map (fun t => t.1) := by decide +kernel

theorem slots4_lt : ∀ t ∈ slots4, t.2.1 < 4 ∧ t.2.2.1 < 4 ∧ t.2.2.2.1 < 4 ∧ t.2.2.2.2 < 4 := by
  decide +kernel

theorem rsumK_eq (w c : ℕ) (l : List ℕ) : rsumK w c l = (l.map (slot w c)).sum := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    show rsumK w c l + slot w c e = _
    rw [List.map_cons, List.sum_cons, ih, add_comm]

theorem rsum_eq2 (w Rc : ℕ) : rsum w Rc 2 = rsumK w Rc sl2 := by
  rw [rsumK_eq]
  exact sum_valid_deg 2 sl2 sl2_nodup sl2_mem sl2_lt (slot w Rc)

theorem rsum_eq3 (w Rc : ℕ) : rsum w Rc 3 = rsumK w Rc sl3 := by
  rw [rsumK_eq]
  exact sum_valid_deg 3 sl3 sl3_nodup sl3_mem sl3_lt (slot w Rc)

theorem rsum_eq4 (w Rc : ℕ) : rsum w Rc 4 = rsumK w Rc sl4 := by
  rw [rsumK_eq]
  exact sum_valid_deg 4 sl4 sl4_nodup sl4_mem sl4_lt (slot w Rc)

/-! ## The monomials of degree 2, 3, 4 as products of the local variables -/

theorem mval_s2 (xs : ℕ → ℝ) : ∀ t ∈ slots2, mval t.1 (lx xs) = xs t.2.1 * xs t.2.2 := by
  intro t ht
  simp only [slots2, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show xs 0 ^ 2 * xs 1 ^ 0 * xs 2 ^ 0 * xs 3 ^ 0 = xs 0 * xs 0
    ring
  · show xs 0 ^ 1 * xs 1 ^ 1 * xs 2 ^ 0 * xs 3 ^ 0 = xs 0 * xs 1
    ring
  · show xs 0 ^ 0 * xs 1 ^ 2 * xs 2 ^ 0 * xs 3 ^ 0 = xs 1 * xs 1
    ring
  · show xs 0 ^ 1 * xs 1 ^ 0 * xs 2 ^ 1 * xs 3 ^ 0 = xs 0 * xs 2
    ring
  · show xs 0 ^ 0 * xs 1 ^ 1 * xs 2 ^ 1 * xs 3 ^ 0 = xs 1 * xs 2
    ring
  · show xs 0 ^ 0 * xs 1 ^ 0 * xs 2 ^ 2 * xs 3 ^ 0 = xs 2 * xs 2
    ring
  · show xs 0 ^ 1 * xs 1 ^ 0 * xs 2 ^ 0 * xs 3 ^ 1 = xs 0 * xs 3
    ring
  · show xs 0 ^ 0 * xs 1 ^ 1 * xs 2 ^ 0 * xs 3 ^ 1 = xs 1 * xs 3
    ring
  · show xs 0 ^ 0 * xs 1 ^ 0 * xs 2 ^ 1 * xs 3 ^ 1 = xs 2 * xs 3
    ring
  · show xs 0 ^ 0 * xs 1 ^ 0 * xs 2 ^ 0 * xs 3 ^ 2 = xs 3 * xs 3
    ring

theorem mval_s3 (xs : ℕ → ℝ) : ∀ t ∈ slots3, mval t.1 (lx xs) = xs t.2.1 * xs t.2.2.1 * xs t.2.2.2 := by
  intro t ht
  simp only [slots3, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show xs 0 ^ 3 * xs 1 ^ 0 * xs 2 ^ 0 * xs 3 ^ 0 = xs 0 * xs 0 * xs 0
    ring
  · show xs 0 ^ 2 * xs 1 ^ 1 * xs 2 ^ 0 * xs 3 ^ 0 = xs 0 * xs 0 * xs 1
    ring
  · show xs 0 ^ 1 * xs 1 ^ 2 * xs 2 ^ 0 * xs 3 ^ 0 = xs 0 * xs 1 * xs 1
    ring
  · show xs 0 ^ 0 * xs 1 ^ 3 * xs 2 ^ 0 * xs 3 ^ 0 = xs 1 * xs 1 * xs 1
    ring
  · show xs 0 ^ 2 * xs 1 ^ 0 * xs 2 ^ 1 * xs 3 ^ 0 = xs 0 * xs 0 * xs 2
    ring
  · show xs 0 ^ 1 * xs 1 ^ 1 * xs 2 ^ 1 * xs 3 ^ 0 = xs 0 * xs 1 * xs 2
    ring
  · show xs 0 ^ 0 * xs 1 ^ 2 * xs 2 ^ 1 * xs 3 ^ 0 = xs 1 * xs 1 * xs 2
    ring
  · show xs 0 ^ 1 * xs 1 ^ 0 * xs 2 ^ 2 * xs 3 ^ 0 = xs 0 * xs 2 * xs 2
    ring
  · show xs 0 ^ 0 * xs 1 ^ 1 * xs 2 ^ 2 * xs 3 ^ 0 = xs 1 * xs 2 * xs 2
    ring
  · show xs 0 ^ 0 * xs 1 ^ 0 * xs 2 ^ 3 * xs 3 ^ 0 = xs 2 * xs 2 * xs 2
    ring
  · show xs 0 ^ 2 * xs 1 ^ 0 * xs 2 ^ 0 * xs 3 ^ 1 = xs 0 * xs 0 * xs 3
    ring
  · show xs 0 ^ 1 * xs 1 ^ 1 * xs 2 ^ 0 * xs 3 ^ 1 = xs 0 * xs 1 * xs 3
    ring
  · show xs 0 ^ 0 * xs 1 ^ 2 * xs 2 ^ 0 * xs 3 ^ 1 = xs 1 * xs 1 * xs 3
    ring
  · show xs 0 ^ 1 * xs 1 ^ 0 * xs 2 ^ 1 * xs 3 ^ 1 = xs 0 * xs 2 * xs 3
    ring
  · show xs 0 ^ 0 * xs 1 ^ 1 * xs 2 ^ 1 * xs 3 ^ 1 = xs 1 * xs 2 * xs 3
    ring
  · show xs 0 ^ 0 * xs 1 ^ 0 * xs 2 ^ 2 * xs 3 ^ 1 = xs 2 * xs 2 * xs 3
    ring
  · show xs 0 ^ 1 * xs 1 ^ 0 * xs 2 ^ 0 * xs 3 ^ 2 = xs 0 * xs 3 * xs 3
    ring
  · show xs 0 ^ 0 * xs 1 ^ 1 * xs 2 ^ 0 * xs 3 ^ 2 = xs 1 * xs 3 * xs 3
    ring
  · show xs 0 ^ 0 * xs 1 ^ 0 * xs 2 ^ 1 * xs 3 ^ 2 = xs 2 * xs 3 * xs 3
    ring
  · show xs 0 ^ 0 * xs 1 ^ 0 * xs 2 ^ 0 * xs 3 ^ 3 = xs 3 * xs 3 * xs 3
    ring

theorem mval_s4 (xs : ℕ → ℝ) :
    ∀ t ∈ slots4, mval t.1 (lx xs) = xs t.2.1 * xs t.2.2.1 * xs t.2.2.2.1 * xs t.2.2.2.2 := by
  intro t ht
  simp only [slots4, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show xs 0 ^ 4 * xs 1 ^ 0 * xs 2 ^ 0 * xs 3 ^ 0 = xs 0 * xs 0 * xs 0 * xs 0
    ring
  · show xs 0 ^ 3 * xs 1 ^ 1 * xs 2 ^ 0 * xs 3 ^ 0 = xs 0 * xs 0 * xs 0 * xs 1
    ring
  · show xs 0 ^ 2 * xs 1 ^ 2 * xs 2 ^ 0 * xs 3 ^ 0 = xs 0 * xs 0 * xs 1 * xs 1
    ring
  · show xs 0 ^ 1 * xs 1 ^ 3 * xs 2 ^ 0 * xs 3 ^ 0 = xs 0 * xs 1 * xs 1 * xs 1
    ring
  · show xs 0 ^ 0 * xs 1 ^ 4 * xs 2 ^ 0 * xs 3 ^ 0 = xs 1 * xs 1 * xs 1 * xs 1
    ring
  · show xs 0 ^ 3 * xs 1 ^ 0 * xs 2 ^ 1 * xs 3 ^ 0 = xs 0 * xs 0 * xs 0 * xs 2
    ring
  · show xs 0 ^ 2 * xs 1 ^ 1 * xs 2 ^ 1 * xs 3 ^ 0 = xs 0 * xs 0 * xs 1 * xs 2
    ring
  · show xs 0 ^ 1 * xs 1 ^ 2 * xs 2 ^ 1 * xs 3 ^ 0 = xs 0 * xs 1 * xs 1 * xs 2
    ring
  · show xs 0 ^ 0 * xs 1 ^ 3 * xs 2 ^ 1 * xs 3 ^ 0 = xs 1 * xs 1 * xs 1 * xs 2
    ring
  · show xs 0 ^ 2 * xs 1 ^ 0 * xs 2 ^ 2 * xs 3 ^ 0 = xs 0 * xs 0 * xs 2 * xs 2
    ring
  · show xs 0 ^ 1 * xs 1 ^ 1 * xs 2 ^ 2 * xs 3 ^ 0 = xs 0 * xs 1 * xs 2 * xs 2
    ring
  · show xs 0 ^ 0 * xs 1 ^ 2 * xs 2 ^ 2 * xs 3 ^ 0 = xs 1 * xs 1 * xs 2 * xs 2
    ring
  · show xs 0 ^ 1 * xs 1 ^ 0 * xs 2 ^ 3 * xs 3 ^ 0 = xs 0 * xs 2 * xs 2 * xs 2
    ring
  · show xs 0 ^ 0 * xs 1 ^ 1 * xs 2 ^ 3 * xs 3 ^ 0 = xs 1 * xs 2 * xs 2 * xs 2
    ring
  · show xs 0 ^ 0 * xs 1 ^ 0 * xs 2 ^ 4 * xs 3 ^ 0 = xs 2 * xs 2 * xs 2 * xs 2
    ring
  · show xs 0 ^ 3 * xs 1 ^ 0 * xs 2 ^ 0 * xs 3 ^ 1 = xs 0 * xs 0 * xs 0 * xs 3
    ring
  · show xs 0 ^ 2 * xs 1 ^ 1 * xs 2 ^ 0 * xs 3 ^ 1 = xs 0 * xs 0 * xs 1 * xs 3
    ring
  · show xs 0 ^ 1 * xs 1 ^ 2 * xs 2 ^ 0 * xs 3 ^ 1 = xs 0 * xs 1 * xs 1 * xs 3
    ring
  · show xs 0 ^ 0 * xs 1 ^ 3 * xs 2 ^ 0 * xs 3 ^ 1 = xs 1 * xs 1 * xs 1 * xs 3
    ring
  · show xs 0 ^ 2 * xs 1 ^ 0 * xs 2 ^ 1 * xs 3 ^ 1 = xs 0 * xs 0 * xs 2 * xs 3
    ring
  · show xs 0 ^ 1 * xs 1 ^ 1 * xs 2 ^ 1 * xs 3 ^ 1 = xs 0 * xs 1 * xs 2 * xs 3
    ring
  · show xs 0 ^ 0 * xs 1 ^ 2 * xs 2 ^ 1 * xs 3 ^ 1 = xs 1 * xs 1 * xs 2 * xs 3
    ring
  · show xs 0 ^ 1 * xs 1 ^ 0 * xs 2 ^ 2 * xs 3 ^ 1 = xs 0 * xs 2 * xs 2 * xs 3
    ring
  · show xs 0 ^ 0 * xs 1 ^ 1 * xs 2 ^ 2 * xs 3 ^ 1 = xs 1 * xs 2 * xs 2 * xs 3
    ring
  · show xs 0 ^ 0 * xs 1 ^ 0 * xs 2 ^ 3 * xs 3 ^ 1 = xs 2 * xs 2 * xs 2 * xs 3
    ring
  · show xs 0 ^ 2 * xs 1 ^ 0 * xs 2 ^ 0 * xs 3 ^ 2 = xs 0 * xs 0 * xs 3 * xs 3
    ring
  · show xs 0 ^ 1 * xs 1 ^ 1 * xs 2 ^ 0 * xs 3 ^ 2 = xs 0 * xs 1 * xs 3 * xs 3
    ring
  · show xs 0 ^ 0 * xs 1 ^ 2 * xs 2 ^ 0 * xs 3 ^ 2 = xs 1 * xs 1 * xs 3 * xs 3
    ring
  · show xs 0 ^ 1 * xs 1 ^ 0 * xs 2 ^ 1 * xs 3 ^ 2 = xs 0 * xs 2 * xs 3 * xs 3
    ring
  · show xs 0 ^ 0 * xs 1 ^ 1 * xs 2 ^ 1 * xs 3 ^ 2 = xs 1 * xs 2 * xs 3 * xs 3
    ring
  · show xs 0 ^ 0 * xs 1 ^ 0 * xs 2 ^ 2 * xs 3 ^ 2 = xs 2 * xs 2 * xs 3 * xs 3
    ring
  · show xs 0 ^ 1 * xs 1 ^ 0 * xs 2 ^ 0 * xs 3 ^ 3 = xs 0 * xs 3 * xs 3 * xs 3
    ring
  · show xs 0 ^ 0 * xs 1 ^ 1 * xs 2 ^ 0 * xs 3 ^ 3 = xs 1 * xs 3 * xs 3 * xs 3
    ring
  · show xs 0 ^ 0 * xs 1 ^ 0 * xs 2 ^ 1 * xs 3 ^ 3 = xs 2 * xs 3 * xs 3 * xs 3
    ring
  · show xs 0 ^ 0 * xs 1 ^ 0 * xs 2 ^ 0 * xs 3 ^ 4 = xs 3 * xs 3 * xs 3 * xs 3
    ring

/-- **The form of degree 2 of the centres** as a sum over the list of the checker. -/
theorem cform_s2 (w Pc Nc : ℕ) (xs : ℕ → ℝ) :
    cform w Pc Nc 2 (lx xs)
      = (slots2.map (fun t => ((slot w Pc t.1 : ℝ) - (slot w Nc t.1 : ℝ)) * (xs t.2.1 * xs t.2.2))).sum := by
  unfold cform
  rw [sum_valid_deg 2 sl2 sl2_nodup sl2_mem sl2_lt, sl2_eq, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  show ((slot w Pc t.1 : ℝ) - (slot w Nc t.1 : ℝ)) * mval t.1 (lx xs) = _
  rw [mval_s2 xs t ht]

theorem cform_s3 (w Pc Nc : ℕ) (xs : ℕ → ℝ) :
    cform w Pc Nc 3 (lx xs)
      = (slots3.map (fun t => ((slot w Pc t.1 : ℝ) - (slot w Nc t.1 : ℝ))
          * (xs t.2.1 * xs t.2.2.1 * xs t.2.2.2))).sum := by
  unfold cform
  rw [sum_valid_deg 3 sl3 sl3_nodup sl3_mem sl3_lt, sl3_eq, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  show ((slot w Pc t.1 : ℝ) - (slot w Nc t.1 : ℝ)) * mval t.1 (lx xs) = _
  rw [mval_s3 xs t ht]

theorem cform_s4 (w Pc Nc : ℕ) (xs : ℕ → ℝ) :
    cform w Pc Nc 4 (lx xs)
      = (slots4.map (fun t => ((slot w Pc t.1 : ℝ) - (slot w Nc t.1 : ℝ))
          * (xs t.2.1 * xs t.2.2.1 * xs t.2.2.2.1 * xs t.2.2.2.2))).sum := by
  unfold cform
  rw [sum_valid_deg 4 sl4 sl4_nodup sl4_mem sl4_lt, sl4_eq, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  show ((slot w Pc t.1 : ℝ) - (slot w Nc t.1 : ℝ)) * mval t.1 (lx xs) = _
  rw [mval_s4 xs t ht]

end N14.Local

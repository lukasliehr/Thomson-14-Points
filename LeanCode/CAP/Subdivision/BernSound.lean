module

public import CAP.Subdivision.BernPass

/-!
# E11, the sign of a polynomial in three variables on a box: soundness of the checker

**Theorem** (`CAP.Bernstein.check_sound`). If `CAP.Bernstein.check P Pp T = true`, then
for all real `x₁, x₂, x₃` with `(c_a - o_a) / q_a ≤ x_a ≤ (c_a + w_a - o_a) / q_a`,

  `0 ≤ p(x)`,   and   `0 < p(x)` if `th = 1`,

where `p(x) = pEval P Pp x₁ x₂ x₃ = ∑ e₁ e₂ e₃ ≤ n, coef P Pp (e₁ + m * (e₂ + m * e₃)) * x₁ ^ e₁ *
x₂ ^ e₂ * x₃ ^ e₃`, `m = n + 1`, and `coef P Pp e` is slot `e` of `Pp` minus the bias.

The proof follows the checker. `root_rep`: the two numbers of the root are the numbers of arrays
whose weighted sums at the homogeneous coordinates `(u, v)` differ by `∏ (q_a (u_a + v_a)) ^ n`
times `p(x)`. `tree_sound`: if the tree is accepted for an array `f`, then the weighted sum of `f`
is at least `A` times that of the binomial array at every `(u, v)` with nonnegative coordinates;
at a split the point `(u, v)` belongs to one of the two halves.
-/

@[expose] public section

namespace CAP.Bernstein

open Finset Polynomial

/-- `X` is the number of the array `f`, whose entries are at most `B`. -/
def Rep (V n X : ℕ) (f : ℕ → ℕ) (B : ℕ) : Prop :=
  X = packSum V ((n + 1) * (n + 1) * (n + 1)) f ∧ ∀ e, e < (n + 1) * (n + 1) * (n + 1) → f e ≤ B

/-! ## The geometry of the three coordinates in the checker -/

theorem stride0 (m : ℕ) : stride m 0 = 1 := if_pos rfl

theorem stride1 (m : ℕ) : stride m 1 = m := by
  unfold stride
  rw [if_neg (by decide), if_pos rfl]

theorem stride2 (m : ℕ) : stride m 2 = m * m := by
  unfold stride
  rw [if_neg (by decide), if_neg (by decide)]

theorem reps0 (m : ℕ) : reps m 0 = m * m := if_pos rfl

theorem reps1 (m : ℕ) : reps m 1 = m := by
  unfold reps
  rw [if_neg (by decide), if_pos rfl]

theorem reps2 (m : ℕ) : reps m 2 = 1 := by
  unfold reps
  rw [if_neg (by decide), if_neg (by decide)]

theorem geom0 (P : Params) : vs1 P = P.V * stride (P.n + 1) 0 ∧ msk1 P = mskA P.V (P.n + 1) 0 := by
  unfold mskA
  rw [stride0, reps0, Nat.mul_one]
  exact ⟨rfl, rfl⟩

theorem geom1 (P : Params) : vs2 P = P.V * stride (P.n + 1) 1 ∧ msk2 P = mskA P.V (P.n + 1) 1 := by
  unfold mskA
  rw [stride1, reps1]
  exact ⟨rfl, rfl⟩

theorem geom2 (P : Params) : vs3 P = P.V * stride (P.n + 1) 2 ∧ msk3 P = mskA P.V (P.n + 1) 2 := by
  have e : vs3 P = P.V * ((P.n + 1) * (P.n + 1)) := Nat.mul_assoc _ _ _
  unfold mskA
  rw [stride2, reps2, ← e]
  exact ⟨rfl, rfl⟩

/-- The distance and the mask that the checker selects for the coordinate `a` of a split. -/
theorem geom (P : Params) (a : ℕ) :
    sel a (vs1 P) (vs2 P) (vs3 P) = P.V * stride (P.n + 1) (min a 2) ∧
      sel a (msk1 P) (msk2 P) (msk3 P) = mskA P.V (P.n + 1) (min a 2) := by
  cases a with
  | zero => exact geom0 P
  | succ k =>
    cases k with
    | zero => exact geom1 P
    | succ j =>
      have e : min (j + 1 + 1) 2 = 2 := Nat.min_eq_right (by omega)
      rw [e]
      exact geom2 P

/-! ## The data -/

theorem data_rep (P : Params) (Pp : ℕ) (hV : 1 ≤ P.V) (h : dataOk P Pp = true) :
    Rep P.V P.n Pp (slot P.V Pp) (2 ^ P.aH) ∧
      Rep P.V P.n (Nat.mul (Nat.shiftLeft 1 (Nat.sub P.aH 1)) (ones P.V (cube P.n))) (fun _ => 2 ^ (P.aH - 1))
        (2 ^ P.aH) := by
  have h' : (Nat.ble P.aH P.V
      && Nat.blt Pp (1 <<< (P.V * ((P.n + 1) * (P.n + 1) * (P.n + 1))))
      && Nat.beq (Pp &&& ((1 <<< P.V - 1 <<< P.aH) * ones P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)))) 0) = true := h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.one_shiftLeft, Nat.one_shiftLeft,
    Nat.one_shiftLeft] at h'
  obtain ⟨⟨haH, hlt⟩, hbits⟩ := h'
  have hbits' := Nat.eq_of_beq_eq_true hbits
  have hs := packSum_slot P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) Pp hlt
  rw [← hs, ones_eq P.V _ hV] at hbits'
  have hd := slots_lt_of_and_hi P.V P.aH _ (slot P.V Pp) haH (fun j _ => slot_lt P.V Pp j) hbits'
  refine ⟨⟨hs.symm, fun e he => (hd e he).le⟩, ?_, fun _ _ => Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)⟩
  show (1 <<< (P.aH - 1)) * ones P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) = _
  rw [Nat.one_shiftLeft, ones_eq P.V _ hV, ← packSum_const]

/-! ## The stages of the root -/

theorem desc_stage (V n a : ℕ) (hV : 0 < V) (c w off q : ℕ) (X : ℕ × ℕ) (f g : ℕ → ℕ) (B : ℕ)
    (hf : Rep V n X.1 f B) (hg : Rep V n X.2 g B) (hB : B < 2 ^ V) :
    Rep V n (desc n (V * stride (n + 1) a) (mskA V (n + 1) a) c w off q X).1
        (actP (stride (n + 1) a) (n + 1) (tab (colDP c w off q n)) (tab (colDN c w off q n)) f g)
        (B * (gsum (c + w + off) q n).1) ∧
      Rep V n (desc n (V * stride (n + 1) a) (mskA V (n + 1) a) c w off q X).2
        (actP (stride (n + 1) a) (n + 1) (tab (colDN c w off q n)) (tab (colDP c w off q n)) f g)
        (B * (gsum (c + w + off) q n).1) := by
  obtain ⟨hX1, hfb⟩ := hf
  obtain ⟨hX2, hgb⟩ := hg
  have hX : X = (packSum V ((n + 1) * (n + 1) * (n + 1)) f, packSum V ((n + 1) * (n + 1) * (n + 1)) g) :=
    Prod.ext hX1 hX2
  have hΓ : ∀ j, ∑ k ∈ range (n + 1), (tab (colDP c w off q n) k j + tab (colDN c w off q n) k j)
      ≤ (gsum (c + w + off) q n).1 := by
    intro j
    rw [gsum_eq]
    exact colD_sum c w off q n j
  have hΓ' : ∀ j, ∑ k ∈ range (n + 1), (tab (colDN c w off q n) k j + tab (colDP c w off q n) k j)
      ≤ (gsum (c + w + off) q n).1 := fun j =>
    le_trans (le_of_eq (sum_congr rfl fun k _ => add_comm _ _)) (hΓ j)
  rw [hX, desc_rep V n a hV c w off q f g (fun e he => lt_of_le_of_lt (hfb e he) hB)
    (fun e he => lt_of_le_of_lt (hgb e he) hB)]
  exact ⟨⟨rfl, fun e he => actP_le (n + 1) a (Nat.succ_pos n) _ _ f g B _ hfb hgb hΓ e he⟩,
    ⟨rfl, fun e he => actP_le (n + 1) a (Nat.succ_pos n) _ _ f g B _ hfb hgb hΓ' e he⟩⟩

theorem asc_stage (V n a : ℕ) (hV : 0 < V) (X : ℕ) (f : ℕ → ℕ) (B : ℕ) (hf : Rep V n X f B) (hB : B < 2 ^ V) :
    Rep V n (asc n (V * stride (n + 1) a) (mskA V (n + 1) a) X)
      (act (stride (n + 1) a) (n + 1) (tab (col2 0 1 1 1 n)) f) (B * 2 ^ (n + 1)) := by
  obtain ⟨rfl, hfb⟩ := hf
  rw [asc_rep V n a hV f (fun e he => lt_of_le_of_lt (hfb e he) hB)]
  exact ⟨rfl, fun e he => act_le (n + 1) a (Nat.succ_pos n) _ f B _ hfb (colA_sum n) e he⟩

/-- The integer coefficient of the entry `e`: slot `e` of `Pp` minus the bias. -/
def coef (P : Params) (Pp e : ℕ) : ℤ := (slot P.V Pp e : ℤ) - 2 ^ (P.aH - 1)

/-- `p(x) = ∑ e₁ e₂ e₃ ≤ n, P e₁ e₂ e₃ * x₁ ^ e₁ * x₂ ^ e₂ * x₃ ^ e₃`. -/
noncomputable def pEval (P : Params) (Pp : ℕ) (x1 x2 x3 : ℝ) : ℝ :=
  ∑ e3 ∈ range (P.n + 1), ∑ e2 ∈ range (P.n + 1), ∑ e1 ∈ range (P.n + 1),
    (coef P Pp (e1 + (P.n + 1) * (e2 + (P.n + 1) * e3)) : ℝ) * x1 ^ e1 * x2 ^ e2 * x3 ^ e3

/-- The first homogeneous coordinates of the data that belong to the point `(u, v)` of the box. -/
def subU (P : Params) (u v : ℕ → ℝ) : ℕ → ℝ := fun a =>
  if a = 0 then (P.q1 : ℝ) * (u 0 + v 0) else if a = 1 then (P.q2 : ℝ) * (u 1 + v 1) else (P.q3 : ℝ) * (u 2 + v 2)

/-- The second homogeneous coordinates of the data that belong to the point `(u, v)` of the box. -/
def subV (P : Params) (u v : ℕ → ℝ) : ℕ → ℝ := fun a =>
  if a = 0 then (P.c1 : ℝ) * (u 0 + v 0) + P.w1 * v 0 - P.o1 * (u 0 + v 0)
  else if a = 1 then (P.c2 : ℝ) * (u 1 + v 1) + P.w2 * v 1 - P.o2 * (u 1 + v 1)
  else (P.c3 : ℝ) * (u 2 + v 2) + P.w3 * v 2 - P.o3 * (u 2 + v 2)

/-- The root: the two numbers are the numbers of arrays below `rootBound`, and the difference of
their weighted sums is the weighted sum of the coefficients at the substituted point. -/
theorem root_rep (P : Params) (Pp : ℕ) (hV : 1 ≤ P.V) (hq1 : 1 ≤ P.q1) (hq2 : 1 ≤ P.q2) (hq3 : 1 ≤ P.q3)
    (hd : dataOk P Pp = true) (hb : rootBound P < 2 ^ (P.V - 1)) :
    ∃ bP bN : ℕ → ℕ, Rep P.V P.n (rootP P Pp) bP (rootBound P) ∧ Rep P.V P.n (rootN P Pp) bN (rootBound P) ∧
      ∀ u v : ℕ → ℝ, Phi (P.n + 1) (hwω P.n u v) bP - Phi (P.n + 1) (hwω P.n u v) bN
        = Phi (P.n + 1) (hwω P.n (subU P u v) (subV P u v)) (slot P.V Pp)
          - Phi (P.n + 1) (hwω P.n (subU P u v) (subV P u v)) (fun _ => 2 ^ (P.aH - 1)) := by
  obtain ⟨d0P, d0N⟩ := data_rep P Pp hV hd
  -- the bounds of the stages
  have g1 := gsum_pos (P.c1 + P.w1 + P.o1) P.q1 P.n hq1
  have g2 := gsum_pos (P.c2 + P.w2 + P.o2) P.q2 P.n hq2
  have g3 := gsum_pos (P.c3 + P.w3 + P.o3) P.q3 P.n hq3
  have hp : 1 ≤ 2 ^ (P.n + 1) := Nat.one_le_two_pow
  have hR : rootBound P
      = 2 ^ P.aH * (gsum (P.c1 + P.w1 + P.o1) P.q1 P.n).1 * (gsum (P.c2 + P.w2 + P.o2) P.q2 P.n).1
        * (gsum (P.c3 + P.w3 + P.o3) P.q3 P.n).1 * 2 ^ (P.n + 1) * 2 ^ (P.n + 1) * 2 ^ (P.n + 1) := by
    show ((1 <<< P.aH) * (gsum (P.c1 + P.w1 + P.o1) P.q1 P.n).1 * (gsum (P.c2 + P.w2 + P.o2) P.q2 P.n).1
        * (gsum (P.c3 + P.w3 + P.o3) P.q3 P.n).1) <<< (3 * (P.n + 1)) = _
    rw [Nat.shiftLeft_eq, Nat.one_shiftLeft]
    ring
  have hV2 : 2 ^ (P.V - 1) ≤ 2 ^ P.V := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have hb' : rootBound P < 2 ^ P.V := lt_of_lt_of_le hb hV2
  rw [hR] at hb'
  have b5 := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hp) hb'
  have b4 := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hp) b5
  have b3 := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hp) b4
  have b2 := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ g3) b3
  have b1 := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ g2) b2
  have b0 := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ g1) b1
  -- the stages
  have s1 := desc_stage P.V P.n 0 hV P.c1 P.w1 P.o1 P.q1
    (Pp, Nat.mul (Nat.shiftLeft 1 (Nat.sub P.aH 1)) (ones P.V (cube P.n))) _ _ _ d0P d0N b0
  have s2 := desc_stage P.V P.n 1 hV P.c2 P.w2 P.o2 P.q2 _ _ _ _ s1.1 s1.2 b1
  have s3 := desc_stage P.V P.n 2 hV P.c3 P.w3 P.o3 P.q3 _ _ _ _ s2.1 s2.2 b2
  have a1P := asc_stage P.V P.n 0 hV _ _ _ s3.1 b3
  have a2P := asc_stage P.V P.n 1 hV _ _ _ a1P b4
  have a3P := asc_stage P.V P.n 2 hV _ _ _ a2P b5
  have a1N := asc_stage P.V P.n 0 hV _ _ _ s3.2 b3
  have a2N := asc_stage P.V P.n 1 hV _ _ _ a1N b4
  have a3N := asc_stage P.V P.n 2 hV _ _ _ a2N b5
  rw [← (geom0 P).1, ← (geom0 P).2, ← (geom1 P).1, ← (geom1 P).2, ← (geom2 P).1, ← (geom2 P).2, ← hR] at a3P a3N
  refine ⟨_, _, a3P, a3N, fun u v => ?_⟩
  rw [Phi_col2 P.n 2 (by decide), Phi_col2 P.n 2 (by decide), Phi_col2 P.n 1 (by decide),
    Phi_col2 P.n 1 (by decide), Phi_col2 P.n 0 (by decide), Phi_col2 P.n 0 (by decide),
    Phi_actP P.n 2 (by decide), Phi_actP P.n 1 (by decide), Phi_actP P.n 0 (by decide)]
  congr 1 <;>
  · refine Phi_congr_weight _ _ _ _ fun b k hb _ => ?_
    obtain rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 := by omega
    all_goals simp [hwω, updR, subU, subV]

/-- The weighted sum of the coefficients. -/
theorem Phi_data (P : Params) (Pp : ℕ) (U V : ℕ → ℝ) :
    Phi (P.n + 1) (hwω P.n U V) (slot P.V Pp) - Phi (P.n + 1) (hwω P.n U V) (fun _ => 2 ^ (P.aH - 1))
      = ∑ e3 ∈ range (P.n + 1), ∑ e2 ∈ range (P.n + 1), ∑ e1 ∈ range (P.n + 1),
          (coef P Pp (e1 + (P.n + 1) * (e2 + (P.n + 1) * e3)) : ℝ)
            * (hw P.n (U 0) (V 0) e1 * hw P.n (U 1) (V 1) e2 * hw P.n (U 2) (V 2) e3) := by
  rw [Phi_cube, Phi_cube, ← sum_sub_distrib]
  refine sum_congr rfl fun e3 _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun e2 _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun e1 _ => ?_
  unfold coef hwω
  push_cast
  ring

/-! ## The binomial array in the checker -/

theorem binomJ_eq (P : Params) : binomJ P = packSum P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) (cJ P.n) := by
  rw [← binom_packSum]
  show (1 + 1 <<< P.V) ^ P.n * (1 + 1 <<< (P.V * (P.n + 1))) ^ P.n
      * (1 + 1 <<< (P.V * (P.n + 1) * (P.n + 1))) ^ P.n = _
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.one_shiftLeft]

theorem linP_half : linP 1 2 + linP 1 0 = C 2 * (1 + X) := by
  unfold linP
  have h2 : (C 2 : ℕ[X]) = 1 + 1 := by
    rw [← C_1, ← C_add]
    norm_num
  rw [C_0, C_1, zero_mul, add_zero, h2]
  ring

theorem linP_halfR : linP 1 0 + linP 1 2 = C 2 * (1 + X) := by
  rw [add_comm, linP_half]

/-- A table whose columns are `col2` and whose two linear forms have the sum `2 * (1 + X)` multiplies
the binomial array by `2 ^ n`. -/
theorem act_cJ (n a : ℕ) (ha : a ≤ 2) (α β α' β' : ℕ) (hsum : linP α β + linP α' β' = C 2 * (1 + X)) (e : ℕ)
    (he : e < (n + 1) * (n + 1) * (n + 1)) :
    act (stride (n + 1) a) (n + 1) (tab (col2 α β α' β' n)) (cJ n) e = 2 ^ n * cJ n e := by
  have hf : ∀ j, fwd (n + 1) (tab (col2 α β α' β' n)) n.choose j = 2 ^ n * n.choose j := by
    intro j
    have h1 : fwd (n + 1) (tab (col2 α β α' β' n)) n.choose j = ((linP α β + linP α' β') ^ n).coeff j := by
      rw [add_pow, finsetSum_coeff]
      unfold fwd tab col2
      refine sum_congr rfl fun k _ => ?_
      rw [← C_eq_natCast, coeff_mul_C, Nat.cast_id, mul_comm]
    rw [h1, hsum, mul_pow, ← C_pow, coeff_C_mul, coeff_one_add_X_pow, Nat.cast_id]
  unfold cJ
  rw [act_W3 (n + 1) a ha (Nat.succ_pos n) _ _ e he]
  obtain ⟨ν, hν⟩ := W3_factor (n + 1) a ha (fun _ : ℕ => n.choose)
  obtain ⟨lo, k, hi, hlo, hk, hhi, rfl⟩ := decomp (n + 1) a e (Nat.succ_pos n) he
  have h0 := hν n.choose lo k hi hlo hk hhi
  rw [upd_eq_self (fun _ : ℕ => n.choose) a] at h0
  rw [hν _ lo k hi hlo hk hhi, h0, hf]
  ring

/-! ## The tree -/

/-- The weighted sum of the binomial array at the point `(u, v)`. -/
def Jv (n : ℕ) (u v : ℕ → ℝ) : ℝ := (u 0 + v 0) ^ n * (u 1 + v 1) ^ n * (u 2 + v 2) ^ n

theorem Jv_half (n a : ℕ) (ha : a ≤ 2) (u v u' v' : ℕ → ℝ) (hu : ∀ b, b ≠ a → u' b = u b)
    (hv : ∀ b, b ≠ a → v' b = v b) (h : 2 * (u' a + v' a) = u a + v a) : 2 ^ n * Jv n u' v' = Jv n u v := by
  unfold Jv
  obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  · rw [hu 1 (by decide), hu 2 (by decide), hv 1 (by decide), hv 2 (by decide), ← h, mul_pow]
    ring
  · rw [hu 0 (by decide), hu 2 (by decide), hv 0 (by decide), hv 2 (by decide), ← h, mul_pow]
    ring
  · rw [hu 0 (by decide), hu 1 (by decide), hv 0 (by decide), hv 1 (by decide), ← h, mul_pow]
    ring

theorem floorN_eq (P : Params) (hV : 1 ≤ P.V) (hn : P.n ≤ P.V) (f : ℕ → ℕ)
    (hf : ∀ e, e < (P.n + 1) * (P.n + 1) * (P.n + 1) → f e < 2 ^ P.V) :
    floorN P (packSum P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) f)
      = packSum P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) (fun e => f e / 2 ^ P.n) := by
  show (packSum P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) f
      &&& ((1 <<< P.V - 1 <<< P.n) * ones P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)))) >>> P.n = _
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft]
  exact floor_packSum P.V P.n _ f hn hV hf

/-- The entries of a half of an array that is at most `2 * A` times the binomial array. -/
theorem half_bound (n a A : ℕ) (ha : a ≤ 2) (α β α' β' : ℕ) (hsum : linP α β + linP α' β' = C 2 * (1 + X))
    (f : ℕ → ℕ) (hf : ∀ e, e < (n + 1) * (n + 1) * (n + 1) → f e ≤ 2 * A * cJ n e) (e : ℕ)
    (he : e < (n + 1) * (n + 1) * (n + 1)) :
    act (stride (n + 1) a) (n + 1) (tab (col2 α β α' β' n)) (fun e => f e / 2 ^ n) e ≤ 2 * A * cJ n e := by
  have hm : 0 < n + 1 := Nat.succ_pos n
  have h1 : 2 ^ n * act (stride (n + 1) a) (n + 1) (tab (col2 α β α' β' n)) (fun e => f e / 2 ^ n) e
      ≤ act (stride (n + 1) a) (n + 1) (tab (col2 α β α' β' n)) f e := by
    rw [← act_smul]
    exact act_mono (n + 1) a hm _ _ f (fun e _ => Nat.mul_div_le (f e) (2 ^ n)) e he
  have h2 : act (stride (n + 1) a) (n + 1) (tab (col2 α β α' β' n)) f e
      ≤ 2 * A * (2 ^ n * cJ n e) := by
    rw [← act_cJ n a ha α β α' β' hsum e he, ← act_smul]
    exact act_mono (n + 1) a hm _ f _ hf e he
  have h3 : 2 ^ n * act (stride (n + 1) a) (n + 1) (tab (col2 α β α' β' n)) (fun e => f e / 2 ^ n) e
      ≤ 2 ^ n * (2 * A * cJ n e) := le_trans (le_trans h1 h2) (le_of_eq (by ring))
  exact Nat.le_of_mul_le_mul_left h3 (Nat.two_pow_pos n)

theorem fits_eq (P : Params) (h : fits P = true) : (2 * P.A + P.th) * 2 ^ (3 * P.n) < 2 ^ (P.V - 1) := by
  have h' : Nat.blt ((2 * P.A + P.th) <<< (3 * P.n)) (1 <<< (P.V - 1)) = true := h
  rw [Nat.blt_eq, Nat.shiftLeft_eq, Nat.one_shiftLeft] at h'
  exact h'

/-- The conditions on the parameters that the tree part of the checker needs. -/
def Pre (P : Params) : Prop := 1 ≤ P.V ∧ P.n ≤ P.V ∧ fits P = true

/-- The statement that the tree part of the checker proves for the number `X`: if `X` is the number
of an array `f` that is at most `2 * A` times the binomial array, then at every point `(u, v)`
with nonnegative coordinates the weighted sum of `f` is at least `A` times that of the binomial
array, and larger if `th = 1` and the latter is positive. -/
def Good (P : Params) (X : ℕ) : Prop :=
  ∀ f : ℕ → ℕ, X = packSum P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) f →
    (∀ e, e < (P.n + 1) * (P.n + 1) * (P.n + 1) → f e ≤ 2 * P.A * cJ P.n e) →
    ∀ u v : ℕ → ℝ, (∀ a, 0 ≤ u a) → (∀ a, 0 ≤ v a) →
      (P.A : ℝ) * Jv P.n u v ≤ Phi (P.n + 1) (hwω P.n u v) f ∧
        (P.th = 1 → 0 < Jv P.n u v → (P.A : ℝ) * Jv P.n u v < Phi (P.n + 1) (hwω P.n u v) f)

theorem entries_lt (P : Params) (hp : Pre P) (f : ℕ → ℕ)
    (hf : ∀ e, e < (P.n + 1) * (P.n + 1) * (P.n + 1) → f e ≤ 2 * P.A * cJ P.n e) (e : ℕ)
    (he : e < (P.n + 1) * (P.n + 1) * (P.n + 1)) : f e < 2 ^ (P.V - 1) :=
  calc f e ≤ 2 * P.A * cJ P.n e := hf e he
    _ ≤ 2 * P.A * 2 ^ (3 * P.n) := Nat.mul_le_mul_left _ (cJ_le P.n e)
    _ ≤ (2 * P.A + P.th) * 2 ^ (3 * P.n) := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    _ < 2 ^ (P.V - 1) := fits_eq P hp.2.2

/-- A leaf: the comparison of the array with `(A + th) * J`. -/
theorem leaf_good (P : Params) (hp : Pre P) (X : ℕ)
    (h : UniPos.geTest P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) X (offJ P) = true) : Good P X := by
  intro f hX hf u v hu hv
  have hF := fits_eq P hp.2.2
  have h' : UniPos.geTest P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) X ((P.A + P.th) * binomJ P) = true := h
  rw [hX, binomJ_eq, ← packSum_mul] at h'
  have hAJ : ∀ e, e < (P.n + 1) * (P.n + 1) * (P.n + 1) → (P.A + P.th) * cJ P.n e < 2 ^ (P.V - 1) := by
    intro e _
    calc (P.A + P.th) * cJ P.n e ≤ (P.A + P.th) * 2 ^ (3 * P.n) := Nat.mul_le_mul_left _ (cJ_le P.n e)
      _ ≤ (2 * P.A + P.th) * 2 ^ (3 * P.n) := Nat.mul_le_mul_right _ (by omega)
      _ < 2 ^ (P.V - 1) := hF
  have key := UniPos.geTest_sound P.V _ f (fun e => (P.A + P.th) * cJ P.n e) hp.1 (entries_lt P hp f hf) hAJ h'
  have hm := Phi_mono (P.n + 1) (hwω P.n u v) (W3_hw_nonneg P.n u v hu hv) key
  rw [Phi_smul, Phi_cJ] at hm
  have hJv : 0 ≤ Jv P.n u v := by
    unfold Jv
    have : ∀ a, 0 ≤ (u a + v a) ^ P.n := fun a => pow_nonneg (add_nonneg (hu a) (hv a)) _
    exact mul_nonneg (mul_nonneg (this 0) (this 1)) (this 2)
  have hm' : ((P.A : ℝ) + P.th) * Jv P.n u v ≤ Phi (P.n + 1) (hwω P.n u v) f := by
    unfold Jv
    push_cast at hm
    exact hm
  have hth : (0 : ℝ) ≤ P.th := Nat.cast_nonneg _
  refine ⟨by nlinarith, fun h1 hpos => ?_⟩
  rw [h1] at hm'
  push_cast at hm'
  nlinarith

/-- A split: the statement for the two halves gives the statement for the array. -/
theorem split_good (P : Params) (hp : Pre P) (a X : ℕ) (hl : Good P (child P a 0 X))
    (hr : Good P (child P a 1 X)) : Good P X := by
  intro f hX hf u v hu hv
  obtain ⟨hV, hn, hfit⟩ := hp
  have hV2 : 2 ^ (P.V - 1) ≤ 2 ^ P.V := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have ha2 : min a 2 ≤ 2 := Nat.min_le_right a 2
  have hfV : ∀ e, e < (P.n + 1) * (P.n + 1) * (P.n + 1) → f e < 2 ^ P.V := fun e he =>
    lt_of_lt_of_le (entries_lt P ⟨hV, hn, hfit⟩ f hf e he) hV2
  have hf'V : ∀ e, e < (P.n + 1) * (P.n + 1) * (P.n + 1) → f e / 2 ^ P.n < 2 ^ P.V := fun e he =>
    lt_of_le_of_lt (Nat.div_le_self _ _) (hfV e he)
  have e0 : child P a 0 X = packSum P.V ((P.n + 1) * (P.n + 1) * (P.n + 1))
      (act (stride (P.n + 1) (min a 2)) (P.n + 1) (tab (col2 1 2 1 0 P.n)) (fun e => f e / 2 ^ P.n)) := by
    show half P.n (sel a (vs1 P) (vs2 P) (vs3 P)) (sel a (msk1 P) (msk2 P) (msk3 P)) (floorN P X) = _
    rw [hX, (geom P a).1, (geom P a).2, floorN_eq P hV hn f hfV, half_rep P.V P.n (min a 2) hV _ hf'V]
  have e1' : child P a 1 X = packSum P.V ((P.n + 1) * (P.n + 1) * (P.n + 1))
      (act (stride (P.n + 1) (min a 2)) (P.n + 1) (tab (col2 1 0 1 2 P.n)) (fun e => f e / 2 ^ P.n)) := by
    show halfR P.n (sel a (vs1 P) (vs2 P) (vs3 P)) (sel a (msk1 P) (msk2 P) (msk3 P)) (floorN P X) = _
    rw [hX, (geom P a).1, (geom P a).2, floorN_eq P hV hn f hfV, halfR_rep P.V P.n (min a 2) hV _ hf'V]
  have il := hl _ e0 (half_bound P.n (min a 2) P.A ha2 1 2 1 0 linP_half f hf)
  have ir := hr _ e1' (half_bound P.n (min a 2) P.A ha2 1 0 1 2 linP_halfR f hf)
  -- the array and its floor
  have e2 : (2 : ℝ) ^ P.n * Phi (P.n + 1) (hwω P.n u v) (fun e => f e / 2 ^ P.n)
      ≤ Phi (P.n + 1) (hwω P.n u v) f := by
    have h0 := Phi_mono (P.n + 1) (hwω P.n u v) (W3_hw_nonneg P.n u v hu hv)
      (f := fun e => 2 ^ P.n * (f e / 2 ^ P.n)) (g := f) (fun e _ => Nat.mul_div_le (f e) (2 ^ P.n))
    rw [Phi_smul] at h0
    push_cast at h0
    exact h0
  have h2pos : (0 : ℝ) < 2 ^ P.n := by positivity
  rcases le_total (u (min a 2)) (v (min a 2)) with huv | huv
  · -- the point lies in the half of `half`
    have hv' : ∀ b, 0 ≤ updR v (min a 2) ((v (min a 2) - u (min a 2)) / 2) b := by
      intro b
      by_cases hb : b = min a 2
      · rw [hb, updR_self]
        linarith
      · rw [updR_ne _ _ _ _ hb]
        exact hv b
    obtain ⟨i1, i2⟩ := il u (updR v (min a 2) ((v (min a 2) - u (min a 2)) / 2)) hu hv'
    have e1 : Phi (P.n + 1) (hwω P.n u (updR v (min a 2) ((v (min a 2) - u (min a 2)) / 2)))
          (act (stride (P.n + 1) (min a 2)) (P.n + 1) (tab (col2 1 2 1 0 P.n)) (fun e => f e / 2 ^ P.n))
        = Phi (P.n + 1) (hwω P.n u v) (fun e => f e / 2 ^ P.n) := by
      rw [Phi_col2 P.n (min a 2) ha2]
      refine Phi_congr_weight _ _ _ _ fun b k _ _ => ?_
      unfold hwω
      by_cases hb : b = min a 2
      · rw [hb, updR_self, updR_self, updR_self]
        have ea : ((1 : ℕ) : ℝ) * u (min a 2) + ((0 : ℕ) : ℝ) * ((v (min a 2) - u (min a 2)) / 2) = u (min a 2) := by
          push_cast
          ring
        have eb : ((1 : ℕ) : ℝ) * u (min a 2) + ((2 : ℕ) : ℝ) * ((v (min a 2) - u (min a 2)) / 2) = v (min a 2) := by
          push_cast
          ring
        rw [ea, eb]
      · rw [updR_ne _ _ _ _ hb, updR_ne _ _ _ _ hb, updR_ne _ _ _ _ hb]
    have e3 : (2 : ℝ) ^ P.n * Jv P.n u (updR v (min a 2) ((v (min a 2) - u (min a 2)) / 2)) = Jv P.n u v :=
      Jv_half P.n (min a 2) ha2 u v u _ (fun _ _ => rfl) (fun b hb => updR_ne _ _ _ _ hb)
        (by rw [updR_self]; ring)
    rw [e1] at i1 i2
    refine ⟨?_, fun h1 hpos => ?_⟩
    · calc (P.A : ℝ) * Jv P.n u v
          = 2 ^ P.n * ((P.A : ℝ) * Jv P.n u (updR v (min a 2) ((v (min a 2) - u (min a 2)) / 2))) := by
            rw [← e3]
            ring
        _ ≤ 2 ^ P.n * Phi (P.n + 1) (hwω P.n u v) (fun e => f e / 2 ^ P.n) :=
            mul_le_mul_of_nonneg_left i1 h2pos.le
        _ ≤ Phi (P.n + 1) (hwω P.n u v) f := e2
    · have hpos' : 0 < Jv P.n u (updR v (min a 2) ((v (min a 2) - u (min a 2)) / 2)) := by
        rw [← e3] at hpos
        exact pos_of_mul_pos_right hpos h2pos.le
      calc (P.A : ℝ) * Jv P.n u v
          = 2 ^ P.n * ((P.A : ℝ) * Jv P.n u (updR v (min a 2) ((v (min a 2) - u (min a 2)) / 2))) := by
            rw [← e3]
            ring
        _ < 2 ^ P.n * Phi (P.n + 1) (hwω P.n u v) (fun e => f e / 2 ^ P.n) :=
            mul_lt_mul_of_pos_left (i2 h1 hpos') h2pos
        _ ≤ Phi (P.n + 1) (hwω P.n u v) f := e2
  · -- the point lies in the half of `halfR`
    have hu' : ∀ b, 0 ≤ updR u (min a 2) (v (min a 2)) b := by
      intro b
      by_cases hb : b = min a 2
      · rw [hb, updR_self]
        exact hv _
      · rw [updR_ne _ _ _ _ hb]
        exact hu b
    have hv' : ∀ b, 0 ≤ updR v (min a 2) ((u (min a 2) - v (min a 2)) / 2) b := by
      intro b
      by_cases hb : b = min a 2
      · rw [hb, updR_self]
        linarith
      · rw [updR_ne _ _ _ _ hb]
        exact hv b
    obtain ⟨i1, i2⟩ := ir (updR u (min a 2) (v (min a 2)))
      (updR v (min a 2) ((u (min a 2) - v (min a 2)) / 2)) hu' hv'
    have e1 : Phi (P.n + 1) (hwω P.n (updR u (min a 2) (v (min a 2)))
            (updR v (min a 2) ((u (min a 2) - v (min a 2)) / 2)))
          (act (stride (P.n + 1) (min a 2)) (P.n + 1) (tab (col2 1 0 1 2 P.n)) (fun e => f e / 2 ^ P.n))
        = Phi (P.n + 1) (hwω P.n u v) (fun e => f e / 2 ^ P.n) := by
      rw [Phi_col2 P.n (min a 2) ha2]
      refine Phi_congr_weight _ _ _ _ fun b k _ _ => ?_
      unfold hwω
      by_cases hb : b = min a 2
      · rw [hb, updR_self, updR_self, updR_self, updR_self]
        have ea : ((1 : ℕ) : ℝ) * v (min a 2) + ((2 : ℕ) : ℝ) * ((u (min a 2) - v (min a 2)) / 2) = u (min a 2) := by
          push_cast
          ring
        have eb : ((1 : ℕ) : ℝ) * v (min a 2) + ((0 : ℕ) : ℝ) * ((u (min a 2) - v (min a 2)) / 2) = v (min a 2) := by
          push_cast
          ring
        rw [ea, eb]
      · rw [updR_ne _ _ _ _ hb, updR_ne _ _ _ _ hb, updR_ne _ _ _ _ hb, updR_ne _ _ _ _ hb]
    have e3 : (2 : ℝ) ^ P.n * Jv P.n (updR u (min a 2) (v (min a 2)))
        (updR v (min a 2) ((u (min a 2) - v (min a 2)) / 2)) = Jv P.n u v :=
      Jv_half P.n (min a 2) ha2 u v _ _ (fun b hb => updR_ne _ _ _ _ hb) (fun b hb => updR_ne _ _ _ _ hb)
        (by rw [updR_self, updR_self]; ring)
    rw [e1] at i1 i2
    refine ⟨?_, fun h1 hpos => ?_⟩
    · calc (P.A : ℝ) * Jv P.n u v
          = 2 ^ P.n * ((P.A : ℝ) * Jv P.n (updR u (min a 2) (v (min a 2)))
              (updR v (min a 2) ((u (min a 2) - v (min a 2)) / 2))) := by
            rw [← e3]
            ring
        _ ≤ 2 ^ P.n * Phi (P.n + 1) (hwω P.n u v) (fun e => f e / 2 ^ P.n) :=
            mul_le_mul_of_nonneg_left i1 h2pos.le
        _ ≤ Phi (P.n + 1) (hwω P.n u v) f := e2
    · have hpos' : 0 < Jv P.n (updR u (min a 2) (v (min a 2)))
          (updR v (min a 2) ((u (min a 2) - v (min a 2)) / 2)) := by
        rw [← e3] at hpos
        exact pos_of_mul_pos_right hpos h2pos.le
      calc (P.A : ℝ) * Jv P.n u v
          = 2 ^ P.n * ((P.A : ℝ) * Jv P.n (updR u (min a 2) (v (min a 2)))
              (updR v (min a 2) ((u (min a 2) - v (min a 2)) / 2))) := by
            rw [← e3]
            ring
        _ < 2 ^ P.n * Phi (P.n + 1) (hwω P.n u v) (fun e => f e / 2 ^ P.n) :=
            mul_lt_mul_of_pos_left (i2 h1 hpos') h2pos
        _ ≤ Phi (P.n + 1) (hwω P.n u v) f := e2


/-- **The tree.** If the checker accepts the tree for the number `X`, the statement `Good` holds
for `X`. -/
theorem tree_good (P : Params) (hp : Pre P) : ∀ (T : Tree) (X : ℕ), treeOk P (offJ P) T X = true → Good P X := by
  intro T
  induction T with
  | leaf => exact fun X h => leaf_good P hp X h
  | split a l r ihl ihr =>
    intro X h
    have h' : (treeOk P (offJ P) l (child P a 0 X) && treeOk P (offJ P) r (child P a 1 X)) = true := h
    rw [Bool.and_eq_true] at h'
    exact split_good P hp a X (ihl _ h'.1) (ihr _ h'.2)

/-! ## The theorem -/

/-- A point of an interval of the box is `(c - o + w * t) / q` with `0 ≤ t ≤ 1`. -/
theorem exists_t (c w o q : ℕ) (hq : 1 ≤ q) (x : ℝ) (h1 : ((c : ℝ) - o) / q ≤ x)
    (h2 : x ≤ ((c : ℝ) + w - o) / q) : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (q : ℝ) * x = c + w * t - o := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_le_iff₀ hq'] at h1
  rw [le_div_iff₀ hq'] at h2
  by_cases hw : w = 0
  · subst hw
    refine ⟨0, le_rfl, zero_le_one, ?_⟩
    push_cast at h2 ⊢
    linarith
  · have hw' : (0 : ℝ) < w := by exact_mod_cast Nat.pos_of_ne_zero hw
    have e : (w : ℝ) * ((x * q - c + o) / w) = x * q - c + o := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ hw'.ne'
    refine ⟨(x * q - c + o) / w, div_nonneg (by linarith) hw'.le, (div_le_one hw').mpr (by linarith), ?_⟩
    rw [e]
    ring

theorem hw_scale (n e : ℕ) (he : e ≤ n) (q x : ℝ) : hw n q (q * x) e = q ^ n * x ^ e := by
  unfold hw
  rw [mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel he]

theorem rootOk_eq (P : Params) (Pp : ℕ) (h : rootOk P Pp = true) :
    (1 ≤ P.V ∧ P.n ≤ P.V ∧ fits P = true) ∧ 1 ≤ P.q1 ∧ 1 ≤ P.q2 ∧ 1 ≤ P.q3 ∧ dataOk P Pp = true ∧
      rootBound P < 2 ^ (P.V - 1) ∧
      UniPos.geTest P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) (P.A * binomJ P) (rootP P Pp) = true ∧
      UniPos.geTest P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) (P.A * binomJ P) (rootN P Pp) = true := by
  have h' : (Nat.ble 1 P.V && Nat.ble P.n P.V && Nat.ble P.th 1 && Nat.ble 1 P.q1 && Nat.ble 1 P.q2
      && Nat.ble 1 P.q3 && dataOk P Pp && Nat.blt (rootBound P) (1 <<< (P.V - 1)) && fits P
      && UniPos.geTest P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) (P.A * binomJ P) (rootP P Pp)
      && UniPos.geTest P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) (P.A * binomJ P) (rootN P Pp)) = true := h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.one_shiftLeft] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hV, hn⟩, _⟩, hq1⟩, hq2⟩, hq3⟩, hd⟩, hb⟩, hfit⟩, hgP⟩, hgN⟩ := h'
  exact ⟨⟨hV, hn, hfit⟩, hq1, hq2, hq3, hd, hb, hgP, hgN⟩

/-- **The root.** If the tests of the root are accepted and the statement `Good` holds for the
array of the root, then `p ≥ 0` on the box, and `p > 0` on the box if `th = 1`. -/
theorem root_sound (P : Params) (Pp : ℕ) (h : rootOk P Pp = true) (hg : Good P (rootX P Pp)) (x1 x2 x3 : ℝ)
    (h1 : ((P.c1 : ℝ) - P.o1) / P.q1 ≤ x1) (h1' : x1 ≤ ((P.c1 : ℝ) + P.w1 - P.o1) / P.q1)
    (h2 : ((P.c2 : ℝ) - P.o2) / P.q2 ≤ x2) (h2' : x2 ≤ ((P.c2 : ℝ) + P.w2 - P.o2) / P.q2)
    (h3 : ((P.c3 : ℝ) - P.o3) / P.q3 ≤ x3) (h3' : x3 ≤ ((P.c3 : ℝ) + P.w3 - P.o3) / P.q3) :
    0 ≤ pEval P Pp x1 x2 x3 ∧ (P.th = 1 → 0 < pEval P Pp x1 x2 x3) := by
  obtain ⟨⟨hV, hn, hfit⟩, hq1, hq2, hq3, hd, hb, hgP, hgN⟩ := rootOk_eq P Pp h
  obtain ⟨bP, bN, ⟨hXP, hbP⟩, ⟨hXN, hbN⟩, hPhi⟩ := root_rep P Pp hV hq1 hq2 hq3 hd hb
  have hF := fits_eq P hfit
  -- the two parts of the root are at most `A` times the binomial array
  have hAJ : ∀ e, e < (P.n + 1) * (P.n + 1) * (P.n + 1) → P.A * cJ P.n e < 2 ^ (P.V - 1) := by
    intro e _
    calc P.A * cJ P.n e ≤ P.A * 2 ^ (3 * P.n) := Nat.mul_le_mul_left _ (cJ_le P.n e)
      _ ≤ (2 * P.A + P.th) * 2 ^ (3 * P.n) := Nat.mul_le_mul_right _ (by omega)
      _ < 2 ^ (P.V - 1) := hF
  have hAJeq : P.A * binomJ P = packSum P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) (fun e => P.A * cJ P.n e) := by
    rw [binomJ_eq, ← packSum_mul]
  rw [hAJeq, hXP] at hgP
  rw [hAJeq, hXN] at hgN
  have gP := UniPos.geTest_sound P.V _ (fun e => P.A * cJ P.n e) bP hV hAJ
    (fun e he => lt_of_le_of_lt (hbP e he) hb) hgP
  have gN := UniPos.geTest_sound P.V _ (fun e => P.A * cJ P.n e) bN hV hAJ
    (fun e he => lt_of_le_of_lt (hbN e he) hb) hgN
  -- the array of the tree
  have hX : rootP P Pp + (P.A * binomJ P - rootN P Pp)
      = packSum P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) (fun e => bP e + (P.A * cJ P.n e - bN e)) := by
    rw [hAJeq, hXP, hXN, packSum_sub P.V _ _ _ gN, ← packSum_add]
  have hbound : ∀ e, e < (P.n + 1) * (P.n + 1) * (P.n + 1) →
      bP e + (P.A * cJ P.n e - bN e) ≤ 2 * P.A * cJ P.n e := by
    intro e he
    have a1 := gP e he
    have a2 : P.A * cJ P.n e - bN e ≤ P.A * cJ P.n e := Nat.sub_le _ _
    have a3 : 2 * P.A * cJ P.n e = P.A * cJ P.n e + P.A * cJ P.n e := by ring
    omega
  -- the point of the box in homogeneous coordinates
  obtain ⟨t1, t1a, t1b, e1⟩ := exists_t P.c1 P.w1 P.o1 P.q1 hq1 x1 h1 h1'
  obtain ⟨t2, t2a, t2b, e2⟩ := exists_t P.c2 P.w2 P.o2 P.q2 hq2 x2 h2 h2'
  obtain ⟨t3, t3a, t3b, e3⟩ := exists_t P.c3 P.w3 P.o3 P.q3 hq3 x3 h3 h3'
  have hv : ∀ a : ℕ, 0 ≤ (if a = 0 then t1 else if a = 1 then t2 else t3) := by
    intro a
    split_ifs <;> assumption
  have hu : ∀ a : ℕ, 0 ≤ 1 - (if a = 0 then t1 else if a = 1 then t2 else t3) := by
    intro a
    split_ifs <;> linarith
  obtain ⟨k1, k2⟩ := hg _ hX hbound
    (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
    (fun a => if a = 0 then t1 else if a = 1 then t2 else t3) hu hv
  have hJv : Jv P.n (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
      (fun a => if a = 0 then t1 else if a = 1 then t2 else t3) = 1 := by
    unfold Jv
    simp
  rw [hJv, mul_one] at k1 k2
  -- the weighted sum of the array of the tree
  have hsum : Phi (P.n + 1) (hwω P.n (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
        (fun a => if a = 0 then t1 else if a = 1 then t2 else t3)) (fun e => bP e + (P.A * cJ P.n e - bN e))
      = (P.A : ℝ) + (Phi (P.n + 1) (hwω P.n (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
          (fun a => if a = 0 then t1 else if a = 1 then t2 else t3)) bP
        - Phi (P.n + 1) (hwω P.n (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
          (fun a => if a = 0 then t1 else if a = 1 then t2 else t3)) bN) := by
    rw [Phi_add, Phi_sub _ _ gN, Phi_smul, Phi_cJ]
    simp
    ring
  rw [hsum, hPhi, Phi_data] at k1 k2
  -- the substituted point
  have hU0 : subU P (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
      (fun a => if a = 0 then t1 else if a = 1 then t2 else t3) 0 = P.q1 := by simp [subU]
  have hU1 : subU P (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
      (fun a => if a = 0 then t1 else if a = 1 then t2 else t3) 1 = P.q2 := by simp [subU]
  have hU2 : subU P (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
      (fun a => if a = 0 then t1 else if a = 1 then t2 else t3) 2 = P.q3 := by simp [subU]
  have hV0 : subV P (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
      (fun a => if a = 0 then t1 else if a = 1 then t2 else t3) 0 = P.q1 * x1 := by
    rw [e1]
    simp [subV]
  have hV1 : subV P (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
      (fun a => if a = 0 then t1 else if a = 1 then t2 else t3) 1 = P.q2 * x2 := by
    rw [e2]
    simp [subV]
  have hV2 : subV P (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
      (fun a => if a = 0 then t1 else if a = 1 then t2 else t3) 2 = P.q3 * x3 := by
    rw [e3]
    simp [subV]
  rw [hU0, hU1, hU2, hV0, hV1, hV2] at k1 k2
  have hQ : (0 : ℝ) < (P.q1 : ℝ) ^ P.n * (P.q2 : ℝ) ^ P.n * (P.q3 : ℝ) ^ P.n := by
    have a1 : (0 : ℝ) < P.q1 := by exact_mod_cast hq1
    have a2 : (0 : ℝ) < P.q2 := by exact_mod_cast hq2
    have a3 : (0 : ℝ) < P.q3 := by exact_mod_cast hq3
    positivity
  have hfin : ∑ e3 ∈ range (P.n + 1), ∑ e2 ∈ range (P.n + 1), ∑ e1 ∈ range (P.n + 1),
        (coef P Pp (e1 + (P.n + 1) * (e2 + (P.n + 1) * e3)) : ℝ)
          * (hw P.n (P.q1 : ℝ) (P.q1 * x1) e1 * hw P.n (P.q2 : ℝ) (P.q2 * x2) e2 * hw P.n (P.q3 : ℝ) (P.q3 * x3) e3)
      = (P.q1 : ℝ) ^ P.n * (P.q2 : ℝ) ^ P.n * (P.q3 : ℝ) ^ P.n * pEval P Pp x1 x2 x3 := by
    unfold pEval
    rw [mul_sum]
    refine sum_congr rfl fun e3 he3 => ?_
    rw [mul_sum]
    refine sum_congr rfl fun e2 he2 => ?_
    rw [mul_sum]
    refine sum_congr rfl fun e1 he1 => ?_
    rw [hw_scale P.n e1 (Nat.lt_succ_iff.mp (mem_range.mp he1)), hw_scale P.n e2 (Nat.lt_succ_iff.mp (mem_range.mp he2)),
      hw_scale P.n e3 (Nat.lt_succ_iff.mp (mem_range.mp he3))]
    ring
  rw [hfin] at k1 k2
  refine ⟨?_, fun hth => ?_⟩
  · have h0 : 0 ≤ (P.q1 : ℝ) ^ P.n * (P.q2 : ℝ) ^ P.n * (P.q3 : ℝ) ^ P.n * pEval P Pp x1 x2 x3 := by linarith
    exact (mul_nonneg_iff_of_pos_left hQ).mp h0
  · have h0 : 0 < (P.q1 : ℝ) ^ P.n * (P.q2 : ℝ) ^ P.n * (P.q3 : ℝ) ^ P.n * pEval P Pp x1 x2 x3 := by
      have := k2 hth one_pos
      linarith
    exact (mul_pos_iff_of_pos_left hQ).mp h0


/-- **Soundness of the checker of the sign of a polynomial on a box.** If the checker accepts, then
`p ≥ 0` on the box, and `p > 0` on the box if `th = 1`. -/
theorem check_sound (P : Params) (Pp : ℕ) (T : Tree) (h : check P Pp T = true) (x1 x2 x3 : ℝ)
    (h1 : ((P.c1 : ℝ) - P.o1) / P.q1 ≤ x1) (h1' : x1 ≤ ((P.c1 : ℝ) + P.w1 - P.o1) / P.q1)
    (h2 : ((P.c2 : ℝ) - P.o2) / P.q2 ≤ x2) (h2' : x2 ≤ ((P.c2 : ℝ) + P.w2 - P.o2) / P.q2)
    (h3 : ((P.c3 : ℝ) - P.o3) / P.q3 ≤ x3) (h3' : x3 ≤ ((P.c3 : ℝ) + P.w3 - P.o3) / P.q3) :
    0 ≤ pEval P Pp x1 x2 x3 ∧ (P.th = 1 → 0 < pEval P Pp x1 x2 x3) := by
  have h' : (rootOk P Pp && treeOk P (offJ P) T (rootX P Pp)) = true := h
  rw [Bool.and_eq_true] at h'
  exact root_sound P Pp h'.1 (tree_good P (rootOk_eq P Pp h'.1).1 T _ h'.2) x1 x2 x3 h1 h1' h2 h2' h3 h3'

theorem rootIs_pre (P : Params) (Pp X : ℕ) (h : rootIs P Pp X = true) : Pre P := by
  have h' : (rootOk P Pp && Nat.beq (rootX P Pp) X) = true := h
  rw [Bool.and_eq_true] at h'
  exact (rootOk_eq P Pp h'.1).1

/-- **Soundness for a divided tree.** If the tests of the root are accepted, `X` is the array of the
root, and the statement `Good` holds for `X`, which `tree_good` and `split_good` give from the
trees of the parts, then `p ≥ 0` on the box, and `p > 0` on the box if `th = 1`. -/
theorem check_parts_sound (P : Params) (Pp X : ℕ) (h : rootIs P Pp X = true) (hg : Good P X) (x1 x2 x3 : ℝ)
    (h1 : ((P.c1 : ℝ) - P.o1) / P.q1 ≤ x1) (h1' : x1 ≤ ((P.c1 : ℝ) + P.w1 - P.o1) / P.q1)
    (h2 : ((P.c2 : ℝ) - P.o2) / P.q2 ≤ x2) (h2' : x2 ≤ ((P.c2 : ℝ) + P.w2 - P.o2) / P.q2)
    (h3 : ((P.c3 : ℝ) - P.o3) / P.q3 ≤ x3) (h3' : x3 ≤ ((P.c3 : ℝ) + P.w3 - P.o3) / P.q3) :
    0 ≤ pEval P Pp x1 x2 x3 ∧ (P.th = 1 → 0 < pEval P Pp x1 x2 x3) := by
  have h' : (rootOk P Pp && Nat.beq (rootX P Pp) X) = true := h
  rw [Bool.and_eq_true] at h'
  have hX : rootX P Pp = X := Nat.eq_of_beq_eq_true h'.2
  rw [← hX] at hg
  exact root_sound P Pp h'.1 hg x1 x2 x3 h1 h1' h2 h2' h3 h3'

end CAP.Bernstein

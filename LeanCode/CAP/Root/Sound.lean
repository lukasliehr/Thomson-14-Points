module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.IntervalCases
public import CAP.Root.Jet

/-!
# E7, isolated zeros: soundness of the checker

Let `prog` be a program and `k` a register. For a real number `y` let `jsem P prog y` be the list
of the real jets of the registers, where register `0` is the variable `y` (with the derivatives `1`
and `0`), and let `jf P prog k c y` be the component `c` of the jet of register `k`
(`c = 0, 1, 2`: value, first and second derivative).

**Theorem** (`CAP.Root.check_sound`). Suppose that
`CAP.Root.check P prog k c cb cr ab bb witI witA witB = true`, and let `I` be the set of all `y` in
the ball `(cb, cr)`. Then

* for every `y ∈ I`: `jf P prog k 1 y` is the derivative of `jf P prog k 0` at `y`, and
  `jf P prog k 2 y` is the derivative of `jf P prog k 1` at `y`, and `jf P prog k (c + 1) y > 0`;
* there is exactly one `x ∈ I` with `jf P prog k c x = 0`, and it lies between the points `a` and
  `b` with the midpoints `ab` and `bb`.

For `c = 0` this is a zero of the function `F = jf P prog k 0`, for `c = 1` a zero of its
derivative.

The proof has three parts: the invariant of the loop (`InvJ`), which states for a fixed point `x`
of the ball of the variable that the registers enclose the real jets at `x` and that the
components are derivatives of each other at `x`; the three evaluations; and the intermediate
value theorem together with strict monotonicity (`exists_unique_zero`).
-/

@[expose] public section

namespace CAP.Root

open CAP.Interval

/-! ## Zeros of a function with positive derivative -/

theorem exists_unique_zero {g g' : ℝ → ℝ} {lo hi a b : ℝ} (hla : lo ≤ a) (hab : a < b) (hbh : b ≤ hi)
    (hg : ∀ y ∈ Set.Icc lo hi, HasDerivAt g (g' y) y) (hpos : ∀ y ∈ Set.Icc lo hi, 0 < g' y)
    (ha : g a < 0) (hb : 0 < g b) :
    ∃ x, a < x ∧ x < b ∧ g x = 0 ∧ ∀ y ∈ Set.Icc lo hi, g y = 0 → y = x := by
  have hcont : ContinuousOn g (Set.Icc lo hi) := fun y hy => (hg y hy).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn g (Set.Icc lo hi) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc lo hi) hcont fun y hy => ?_
    rw [interior_Icc] at hy
    have hy' : y ∈ Set.Icc lo hi := Set.Ioo_subset_Icc_self hy
    rw [(hg y hy').deriv]
    exact hpos y hy'
  have hsub : Set.Icc a b ⊆ Set.Icc lo hi := Set.Icc_subset_Icc hla hbh
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo hab.le (hcont.mono hsub)
    (show (0 : ℝ) ∈ Set.Ioo (g a) (g b) from ⟨ha, hb⟩)
  exact ⟨x, hx.1, hx.2, hx0, fun y hy hy0 =>
    hmono.injOn hy (hsub (Set.Ioo_subset_Icc_self hx)) (hy0.trans hx0.symm)⟩

/-! ## A jet as six slots -/

/-- The six numbers of a jet. -/
def jf6 (J : Jet) : ℕ → ℕ
  | 0 => J.1.1
  | 1 => J.1.2.1
  | 2 => J.2.1.1
  | 3 => J.2.1.2.1
  | 4 => J.2.2.1
  | _ => J.2.2.2.1

/-- The six numbers of a jet fit into a slot. -/
def Fits (W : ℕ) (J : Jet) : Prop := ∀ j, j < 6 → jf6 J j < 2 ^ W

theorem packJ_eq (W : ℕ) (J : Jet) : packJ W J =
    J.1.1 + (J.1.2.1 + (J.2.1.1 + (J.2.1.2.1 + (J.2.2.1 + J.2.2.2.1 * 2 ^ W) * 2 ^ W) * 2 ^ W) * 2 ^ W)
      * 2 ^ W := by
  simp only [← Nat.shiftLeft_eq]
  rfl

theorem packJ_packSum (W : ℕ) (J : Jet) : packJ W J = packSum W 6 (jf6 J) := by
  rw [packJ_eq]
  simp only [packSum, Finset.sum_range_succ, Finset.sum_range_zero, jf6]
  ring

theorem fits_of_lor {W : ℕ} {J : Jet}
    (h : (((J.1.1 ||| J.1.2.1) ||| (J.2.1.1 ||| J.2.1.2.1)) ||| (J.2.2.1 ||| J.2.2.2.1)) >>> W = 0) :
    Fits W J := by
  obtain ⟨h1, h2⟩ := lt_of_lor_lt (lt_of_shiftRight_eq_zero h)
  obtain ⟨h3, h4⟩ := lt_of_lor_lt h1
  obtain ⟨h5, h6⟩ := lt_of_lor_lt h3
  obtain ⟨h7, h8⟩ := lt_of_lor_lt h4
  obtain ⟨h9, h10⟩ := lt_of_lor_lt h2
  intro j hj
  interval_cases j
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10

theorem slot_packJ {W : ℕ} {J : Jet} (h : Fits W J) (j : ℕ) (hj : j < 6) :
    slot W (packJ W J) j = jf6 J j := by
  rw [packJ_packSum]
  exact slot_packSum W 6 (jf6 J) h j hj

theorem packJ_lt {W : ℕ} {J : Jet} (h : Fits W J) : packJ W J < 2 ^ (W * 6) := by
  rw [packJ_packSum]
  exact packSum_lt W 6 (jf6 J) h

/-- The registers below a new register are unchanged. -/
theorem rdJ_push_lo (W R k v i : ℕ) (hR : R < 2 ^ (W * (6 * k))) (hi : i < k) :
    rdJ W (R + v * 2 ^ (W * (6 * k))) i = rdJ W R i := by
  show ((slot W _ (6 * i), slot W _ (6 * i + 1), true), (slot W _ (6 * i + 2), slot W _ (6 * i + 3), true),
      (slot W _ (6 * i + 4), slot W _ (6 * i + 5), true))
    = ((slot W R (6 * i), slot W R (6 * i + 1), true), (slot W R (6 * i + 2), slot W R (6 * i + 3), true),
      (slot W R (6 * i + 4), slot W R (6 * i + 5), true))
  rw [slot_add_mul_lo W (6 * k) R v (6 * i) hR (by omega),
    slot_add_mul_lo W (6 * k) R v (6 * i + 1) hR (by omega),
    slot_add_mul_lo W (6 * k) R v (6 * i + 2) hR (by omega),
    slot_add_mul_lo W (6 * k) R v (6 * i + 3) hR (by omega),
    slot_add_mul_lo W (6 * k) R v (6 * i + 4) hR (by omega),
    slot_add_mul_lo W (6 * k) R v (6 * i + 5) hR (by omega)]

/-- The new register consists of the six numbers of the jet. -/
theorem rdJ_push_hi (W R k : ℕ) (J : Jet) (hR : R < 2 ^ (W * (6 * k))) (hJ : Fits W J) :
    rdJ W (R + packJ W J * 2 ^ (W * (6 * k))) k
      = ((J.1.1, J.1.2.1, true), (J.2.1.1, J.2.1.2.1, true), (J.2.2.1, J.2.2.2.1, true)) := by
  show ((slot W _ (6 * k + 0), slot W _ (6 * k + 1), true), (slot W _ (6 * k + 2), slot W _ (6 * k + 3), true),
      (slot W _ (6 * k + 4), slot W _ (6 * k + 5), true)) = _
  rw [slot_add_mul_hi W (6 * k) R _ 0 hR, slot_add_mul_hi W (6 * k) R _ 1 hR,
    slot_add_mul_hi W (6 * k) R _ 2 hR, slot_add_mul_hi W (6 * k) R _ 3 hR,
    slot_add_mul_hi W (6 * k) R _ 4 hR, slot_add_mul_hi W (6 * k) R _ 5 hR,
    slot_packJ hJ 0 (by omega), slot_packJ hJ 1 (by omega), slot_packJ hJ 2 (by omega),
    slot_packJ hJ 3 (by omega), slot_packJ hJ 4 (by omega), slot_packJ hJ 5 (by omega)]
  rfl

/-! ## The invariant -/

/-- For the point `x`: the packed number `R` consists of `k` registers, the registers enclose the
real jets `G x`, and the components of the functions `G` are derivatives of each other at `x`. -/
structure InvJ (P : Params) (B R k : ℕ) (G : ℝ → List RJ) (x : ℝ) : Prop where
  len : ∀ y, (G y).length = k
  size : R < 2 ^ (P.W * (6 * k))
  enc : ∀ i, i < k → JEnc P.p B (rdJ P.W R i) ((G x).getD i 0)
  smooth : ∀ i, i < k → HasDerivAt (fun y => ((G y).getD i 0).1) ((G x).getD i 0).2.1 x ∧
    HasDerivAt (fun y => ((G y).getD i 0).2.1) ((G x).getD i 0).2.2 x

/-- An accepted instruction: its jet encloses the real jet, and the components of the real jet are
derivatives of each other. -/
theorem stepJ_sound (P : Params) (B R k : ℕ) (hB : B = 2 ^ (P.W - 1)) (hp : 1 ≤ P.p) (wit : List ℕ)
    (G : ℝ → List RJ) (x : ℝ) (hI : InvJ P B R k G x) (ins : Instr)
    (hv : (stepJ P B R k wit ins).1.1.1.2.2 = true) (hidx : (stepJ P B R k wit ins).1.2 = true) :
    JEnc P.p B (stepJ P B R k wit ins).1.1 (jden P (G x) ins) ∧
      HasDerivAt (fun y => (jden P (G y) ins).1) (jden P (G x) ins).2.1 x ∧
      HasDerivAt (fun y => (jden P (G y) ins).2.1) (jden P (G x) ins).2.2 x := by
  cases ins with
  | nat n =>
    refine ⟨⟨?_, zero_enc _ _, zero_enc _ _⟩, hasDerivAt_const x _, hasDerivAt_const x _⟩
    intro _
    show Enc P.p B (B + n <<< P.p) 0 (n : ℝ)
    rw [Nat.shiftLeft_eq]
    exact nat_sound P.p B n
  | cst b =>
    refine ⟨⟨?_, zero_enc _ _, zero_enc _ _⟩, hasDerivAt_const x _, hasDerivAt_const x _⟩
    intro _
    show Enc P.p B b 0 (((b : ℝ) - 2 ^ (P.W - 1)) / 2 ^ P.p)
    have h := cst_sound P.p B b
    rw [hB] at h ⊢
    push_cast at h
    exact h
  | add i j =>
    have hij : (Nat.blt i k && Nat.blt j k) = true := hidx
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at hij
    exact ⟨jadd_sound (hI.enc i hij.1) (hI.enc j hij.2),
      (hI.smooth i hij.1).1.fun_add (hI.smooth j hij.2).1,
      (hI.smooth i hij.1).2.fun_add (hI.smooth j hij.2).2⟩
  | sub i j =>
    have hij : (Nat.blt i k && Nat.blt j k) = true := hidx
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at hij
    exact ⟨jsub_sound (hI.enc i hij.1) (hI.enc j hij.2),
      (hI.smooth i hij.1).1.fun_sub (hI.smooth j hij.2).1,
      (hI.smooth i hij.1).2.fun_sub (hI.smooth j hij.2).2⟩
  | mul i j =>
    have hij : (Nat.blt i k && Nat.blt j k) = true := hidx
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at hij
    obtain ⟨d1, d2⟩ := hasDeriv_mul2 (f' := fun y => ((G y).getD i 0).2.1)
      (g' := fun y => ((G y).getD j 0).2.1) (hI.smooth i hij.1).1 (hI.smooth j hij.2).1
      (hI.smooth i hij.1).2 (hI.smooth j hij.2).2
    exact ⟨jmul_sound (hI.enc i hij.1) (hI.enc j hij.2), d1, d2⟩
  | inv i =>
    have hi : i < k := by
      have h : Nat.blt i k = true := hidx
      rwa [Nat.blt_eq] at h
    have h0 : ((G x).getD i 0).1 ≠ 0 := finv_ne_zero (hI.enc i hi).1 hv
    obtain ⟨d1, d2⟩ := hasDeriv_inv2 (f' := fun y => ((G y).getD i 0).2.1) (hI.smooth i hi).1
      (hI.smooth i hi).2 h0
    exact ⟨jinv_sound (hI.enc i hi), d1, d2⟩
  | sqrt i =>
    cases wit with
    | nil => exact Bool.noConfusion (show false = true from hidx)
    | cons t tl =>
      have hi : i < k := by
        have h : Nat.blt i k = true := hidx
        rwa [Nat.blt_eq] at h
      have h0 : 0 < ((G x).getD i 0).1 := fsqrt_pos (hI.enc i hi).1 hv
      obtain ⟨d1, d2⟩ := hasDeriv_sqrt2 (f' := fun y => ((G y).getD i 0).2.1) (hI.smooth i hi).1
        (hI.smooth i hi).2 h0
      exact ⟨jsqrt_sound hp (hI.enc i hi), d1, d2⟩

/-- Storing a jet as the next register preserves the invariant. -/
theorem push_invJ (P : Params) (B R k : ℕ) (J : Jet) (G : ℝ → List RJ) (x : ℝ) (v : ℝ → RJ)
    (hI : InvJ P B R k G x) (hJ : JEnc P.p B J (v x))
    (hfl : J.1.2.2 = true ∧ J.2.1.2.2 = true ∧ J.2.2.2.2 = true) (hfit : Fits P.W J)
    (hd1 : HasDerivAt (fun y => (v y).1) (v x).2.1 x) (hd2 : HasDerivAt (fun y => (v y).2.1) (v x).2.2 x) :
    InvJ P B (R + packJ P.W J * 2 ^ (P.W * (6 * k))) (k + 1) (fun y => G y ++ [v y]) x := by
  have hlo : ∀ (y : ℝ) (i : ℕ), i < k → (G y ++ [v y]).getD i 0 = (G y).getD i 0 := fun y i hi =>
    getD_append_lt _ _ _ _ (by rw [hI.len y]; exact hi)
  have hhi : ∀ y : ℝ, (G y ++ [v y]).getD k 0 = v y := fun y => by
    have h := getD_append_length (G y) 0 (v y)
    rwa [hI.len y] at h
  refine ⟨fun y => by simp [hI.len y], ?_, ?_, ?_⟩
  · have h := add_mul_lt_two_pow P.W (6 * k) 6 R (packJ P.W J) hI.size (packJ_lt hfit)
    rwa [show 6 * k + 6 = 6 * (k + 1) by ring] at h
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · rw [rdJ_push_lo P.W R k _ i hI.size hlt, hlo x i hlt]
      exact hI.enc i hlt
    · subst heq
      rw [rdJ_push_hi P.W R i J hI.size hfit, hhi x]
      exact ⟨fun _ => hJ.1 hfl.1, fun _ => hJ.2.1 hfl.2.1, fun _ => hJ.2.2 hfl.2.2⟩
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · have e1 : (fun y => ((G y ++ [v y]).getD i 0).1) = fun y => ((G y).getD i 0).1 := by
        funext y
        rw [hlo y i hlt]
      have e2 : (fun y => ((G y ++ [v y]).getD i 0).2.1) = fun y => ((G y).getD i 0).2.1 := by
        funext y
        rw [hlo y i hlt]
      rw [e1, e2, hlo x i hlt]
      exact hI.smooth i hlt
    · subst heq
      have e1 : (fun y => ((G y ++ [v y]).getD i 0).1) = fun y => (v y).1 := by
        funext y
        rw [hhi y]
      have e2 : (fun y => ((G y ++ [v y]).getD i 0).2.1) = fun y => (v y).2.1 := by
        funext y
        rw [hhi y]
      rw [e1, e2, hhi x]
      exact ⟨hd1, hd2⟩

/-- The loop preserves the invariant and ends with the final test. -/
theorem runJ_sound (P : Params) (B : ℕ) (hB : B = 2 ^ (P.W - 1)) (hp : 1 ≤ P.p) (fin : ℕ → ℕ → Bool) :
    ∀ (prog : List Instr) (R k : ℕ) (wit : List ℕ) (G : ℝ → List RJ) (x : ℝ), InvJ P B R k G x →
      runJ P B fin prog R k wit = true →
      ∃ R' k', InvJ P B R' k' (fun y => jsemFrom P prog (G y)) x ∧ fin R' k' = true
  | [], R, k, _, _, _, hI, h => ⟨R, k, hI, h⟩
  | ins :: rest, R, k, wit, G, x, hI, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false
        (runJ P B fin rest (R + packJ P.W (stepJ P B R k wit ins).1.1 <<< (6 * P.W * k)) (k + 1)
          (stepJ P B R k wit ins).2)
        (okJ P.W (stepJ P B R k wit ins).1.1 && (stepJ P B R k wit ins).1.2) = true := h
    rw [bool_rec_and, Bool.and_eq_true, Bool.and_eq_true] at h'
    obtain ⟨⟨hok, hidx⟩, hrest⟩ := h'
    generalize hJ : (stepJ P B R k wit ins).1.1 = J at hok hrest
    have hok' : (J.1.2.2 && J.2.1.2.2 && J.2.2.2.2 &&
        Nat.beq ((((J.1.1 ||| J.1.2.1) ||| (J.2.1.1 ||| J.2.1.2.1)) ||| (J.2.2.1 ||| J.2.2.2.1)) >>> P.W) 0)
        = true := hok
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hok'
    obtain ⟨⟨⟨f1, f2⟩, f3⟩, hlor⟩ := hok'
    have hfit := fits_of_lor (Nat.eq_of_beq_eq_true hlor)
    obtain ⟨hE, hd1, hd2⟩ := stepJ_sound P B R k hB hp wit G x hI ins (by rw [hJ]; exact f1) hidx
    rw [hJ] at hE
    have hI' := push_invJ P B R k J G x (fun y => jden P (G y) ins) hI hE ⟨f1, f2, f3⟩ hfit hd1 hd2
    rw [Nat.shiftLeft_eq, show 6 * P.W * k = P.W * (6 * k) by ring] at hrest
    exact runJ_sound P B hB hp fin rest _ _ _ _ x hI' hrest

/-! ## The components of a register -/

/-- The component `c` of a real jet: value, first derivative, second derivative. -/
def comp : ℕ → RJ → ℝ
  | 0, v => v.1
  | 1, v => v.2.1
  | _, v => v.2.2

/-- The component `c` of register `k` as a function of the variable. -/
noncomputable def jf (P : Params) (prog : List Instr) (k c : ℕ) (y : ℝ) : ℝ :=
  comp c ((jsem P prog y).getD k 0)

theorem enc_pos {p B b r : ℕ} {v : ℝ} (h : Enc p B b r v) (hb : B + 1 + r ≤ b) : 0 < v := by
  unfold Enc at h
  rw [abs_le] at h
  have hb' : (B : ℝ) + 1 + r ≤ b := by exact_mod_cast hb
  have h2 : 0 < v * 2 ^ p := by linarith [h.1]
  exact pos_of_mul_pos_left h2 (two_pow_pos' p).le

theorem enc_neg {p B b r : ℕ} {v : ℝ} (h : Enc p B b r v) (hb : b + r + 1 ≤ B) : v < 0 := by
  unfold Enc at h
  rw [abs_le] at h
  have hb' : (b : ℝ) + r + 1 ≤ B := by exact_mod_cast hb
  have h2 : v * 2 ^ p < 0 := by linarith [h.2]
  by_contra hcon
  have : 0 ≤ v * 2 ^ p := mul_nonneg (not_lt.mp hcon) (two_pow_pos' p).le
  linarith

/-- The enclosure of the component `c` of register `i`. -/
theorem enc_comp {P : Params} {B R k : ℕ} {G : ℝ → List RJ} {x : ℝ} (hI : InvJ P B R k G x) (i c : ℕ)
    (hi : i < k) (hc : c ≤ 2) :
    Enc P.p B (slot P.W R (6 * i + 2 * c)) (slot P.W R (6 * i + 2 * c + 1)) (comp c ((G x).getD i 0)) := by
  have h := hI.enc i hi
  interval_cases c
  · exact h.1 rfl
  · exact h.2.1 rfl
  · exact h.2.2 rfl

theorem pos_of_posAt {P : Params} {B R k : ℕ} {G : ℝ → List RJ} {x : ℝ} (hI : InvJ P B R k G x) (i c : ℕ)
    (hi : i < k) (hc : c ≤ 2) (h : posAt P.W B R i c = true) : 0 < comp c ((G x).getD i 0) :=
  enc_pos (enc_comp hI i c hi hc) (Nat.le_of_ble_eq_true h)

theorem neg_of_negAt {P : Params} {B R k : ℕ} {G : ℝ → List RJ} {x : ℝ} (hI : InvJ P B R k G x) (i c : ℕ)
    (hi : i < k) (hc : c ≤ 2) (h : negAt P.W B R i c = true) : comp c ((G x).getD i 0) < 0 :=
  enc_neg (enc_comp hI i c hi hc) (Nat.le_of_ble_eq_true h)

/-! ## One evaluation -/

/-- The invariant for the register of the variable. -/
theorem init_invJ (P : Params) (xb xr : ℕ) (hpW : P.p + 2 ≤ P.W) (hxb : xb < 2 ^ P.W) (hxr : xr < 2 ^ P.W)
    (x : ℝ) (hx : Enc P.p (2 ^ (P.W - 1)) xb xr x) :
    InvJ P (2 ^ (P.W - 1)) (initJ P (2 ^ (P.W - 1)) xb xr) 1 (fun y => [(y, 1, 0)]) x := by
  have h0 : InvJ P (2 ^ (P.W - 1)) 0 0 (fun _ => []) x :=
    ⟨fun _ => rfl, Nat.two_pow_pos _, fun i hi => absurd hi (Nat.not_lt_zero i),
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  have hfit : Fits P.W ((xb, xr, true), (2 ^ (P.W - 1) + 1 <<< P.p, 0, true), (2 ^ (P.W - 1), 0, true)) := by
    obtain ⟨j, hj⟩ : ∃ j, P.W = j + 2 := ⟨P.W - 2, by omega⟩
    have h1 : 2 ^ P.p ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (P.W - 1) = 2 * 2 ^ j := by
      rw [hj, show j + 2 - 1 = j + 1 by omega, pow_succ]
      ring
    have h3 : 2 ^ P.W = 4 * 2 ^ j := by
      rw [hj, pow_succ, pow_succ]
      ring
    have h4 : 0 < 2 ^ j := Nat.two_pow_pos j
    intro i hi
    interval_cases i
    · exact hxb
    · exact hxr
    · show 2 ^ (P.W - 1) + 1 <<< P.p < 2 ^ P.W
      rw [Nat.one_shiftLeft]
      omega
    · exact Nat.two_pow_pos _
    · show 2 ^ (P.W - 1) < 2 ^ P.W
      omega
    · exact Nat.two_pow_pos _
  have h := push_invJ P (2 ^ (P.W - 1)) 0 0
    ((xb, xr, true), (2 ^ (P.W - 1) + 1 <<< P.p, 0, true), (2 ^ (P.W - 1), 0, true)) (fun _ => []) x
    (fun y => (y, 1, 0)) h0 ⟨fun _ => hx, one_enc _ _, zero_enc _ _⟩ ⟨rfl, rfl, rfl⟩ hfit
    (hasDerivAt_id' x) (hasDerivAt_const x _)
  have e : 0 + packJ P.W ((xb, xr, true), (2 ^ (P.W - 1) + 1 <<< P.p, 0, true), (2 ^ (P.W - 1), 0, true))
      * 2 ^ (P.W * (6 * 0)) = initJ P (2 ^ (P.W - 1)) xb xr := by
    rw [Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
    rfl
  rw [e] at h
  exact h

/-- One evaluation: the invariant holds at the end for every point of the ball of the variable. -/
theorem eval_sound (P : Params) (prog : List Instr) (fin : ℕ → ℕ → Bool) (xb xr : ℕ) (wit : List ℕ)
    (hp : 1 ≤ P.p) (hpW : P.p + 2 ≤ P.W) (hxb : xb < 2 ^ P.W) (hxr : xr < 2 ^ P.W)
    (h : runJ P (2 ^ (P.W - 1)) fin prog (initJ P (2 ^ (P.W - 1)) xb xr) 1 wit = true) (x : ℝ)
    (hx : Enc P.p (2 ^ (P.W - 1)) xb xr x) :
    ∃ R' k', InvJ P (2 ^ (P.W - 1)) R' k' (jsem P prog) x ∧ fin R' k' = true :=
  runJ_sound P _ rfl hp fin prog _ _ wit _ x (init_invJ P xb xr hpW hxb hxr x hx) h

/-! ## The theorem -/

/-- The point with the midpoint `b` lies in the ball `(b, 0)`. -/
theorem enc_point (p B b : ℕ) : Enc p B b 0 (((b : ℝ) - B) / 2 ^ p) := cst_sound p B b

/-- A ball is an interval. -/
theorem enc_iff_mem_Icc (p B b r : ℕ) (y : ℝ) :
    Enc p B b r y ↔ y ∈ Set.Icc (((b : ℝ) - B - r) / 2 ^ p) (((b : ℝ) - B + r) / 2 ^ p) := by
  have hs := two_pow_pos' p
  unfold Enc
  rw [abs_le, Set.mem_Icc, div_le_iff₀ hs, le_div_iff₀ hs]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Soundness of the checker of E7.** If the checker accepts, then on the ball `(cb, cr)` the
components of register `k` are derivatives of each other, the component `c + 1` is positive, and
the component `c` has exactly one zero, which lies between the points with the midpoints `ab` and
`bb`. -/
theorem check_sound (P : Params) (prog : List Instr) (k c cb cr ab bb : ℕ) (witI witA witB : List ℕ)
    (h : check P prog k c cb cr ab bb witI witA witB = true) :
    (∀ y : ℝ, Enc P.p (2 ^ (P.W - 1)) cb cr y →
      HasDerivAt (jf P prog k 0) (jf P prog k 1 y) y ∧ HasDerivAt (jf P prog k 1) (jf P prog k 2 y) y ∧
        0 < jf P prog k (c + 1) y) ∧
    ∃ x : ℝ, ((ab : ℝ) - 2 ^ (P.W - 1)) / 2 ^ P.p < x ∧ x < ((bb : ℝ) - 2 ^ (P.W - 1)) / 2 ^ P.p ∧
      Enc P.p (2 ^ (P.W - 1)) cb cr x ∧ jf P prog k c x = 0 ∧
      ∀ y : ℝ, Enc P.p (2 ^ (P.W - 1)) cb cr y → jf P prog k c y = 0 → y = x := by
  have h' : (Nat.ble 1 P.p && Nat.ble (P.p + 2) P.W && Nat.ble c 1 &&
      Nat.beq (((cb ||| cr) ||| (ab ||| bb)) >>> P.W) 0 &&
      Nat.ble cb (ab + cr) && Nat.blt ab bb && Nat.ble bb (cb + cr) &&
      runJ P (1 <<< (P.W - 1)) (fun R n => Nat.blt k n && posAt P.W (1 <<< (P.W - 1)) R k (c + 1))
        prog (initJ P (1 <<< (P.W - 1)) cb cr) 1 witI &&
      runJ P (1 <<< (P.W - 1)) (fun R n => Nat.blt k n && negAt P.W (1 <<< (P.W - 1)) R k c)
        prog (initJ P (1 <<< (P.W - 1)) ab 0) 1 witA &&
      runJ P (1 <<< (P.W - 1)) (fun R n => Nat.blt k n && posAt P.W (1 <<< (P.W - 1)) R k c)
        prog (initJ P (1 <<< (P.W - 1)) bb 0) 1 witB) = true := h
  simp only [Bool.and_eq_true, Nat.one_shiftLeft] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hp, hpW⟩, hc⟩, hlor⟩, h1⟩, h2⟩, h3⟩, hrI⟩, hrA⟩, hrB⟩ := h'
  have hp : 1 ≤ P.p := Nat.le_of_ble_eq_true hp
  have hpW : P.p + 2 ≤ P.W := Nat.le_of_ble_eq_true hpW
  have hc : c ≤ 1 := Nat.le_of_ble_eq_true hc
  have h1 : cb ≤ ab + cr := Nat.le_of_ble_eq_true h1
  have h2 : ab < bb := by rwa [Nat.blt_eq] at h2
  have h3 : bb ≤ cb + cr := Nat.le_of_ble_eq_true h3
  obtain ⟨hcbr, habb⟩ := lt_of_lor_lt (lt_of_shiftRight_eq_zero (Nat.eq_of_beq_eq_true hlor))
  obtain ⟨hcb, hcr⟩ := lt_of_lor_lt hcbr
  obtain ⟨hab, hbb⟩ := lt_of_lor_lt habb
  have hs := two_pow_pos' P.p
  -- the interval
  have hI : ∀ y : ℝ, Enc P.p (2 ^ (P.W - 1)) cb cr y →
      HasDerivAt (jf P prog k 0) (jf P prog k 1 y) y ∧ HasDerivAt (jf P prog k 1) (jf P prog k 2 y) y ∧
        0 < jf P prog k (c + 1) y := by
    intro y hy
    obtain ⟨R', k', hInv, hfin⟩ := eval_sound P prog _ cb cr witI hp hpW hcb hcr hrI y hy
    rw [Bool.and_eq_true, Nat.blt_eq] at hfin
    obtain ⟨d1, d2⟩ := hInv.smooth k hfin.1
    exact ⟨d1, d2, pos_of_posAt hInv k (c + 1) hfin.1 (by omega) hfin.2⟩
  -- the two points
  have hA : jf P prog k c (((ab : ℝ) - 2 ^ (P.W - 1)) / 2 ^ P.p) < 0 := by
    have hx := enc_point P.p (2 ^ (P.W - 1)) ab
    push_cast at hx
    obtain ⟨R', k', hInv, hfin⟩ := eval_sound P prog _ ab 0 witA hp hpW hab (Nat.two_pow_pos _) hrA _ hx
    rw [Bool.and_eq_true, Nat.blt_eq] at hfin
    exact neg_of_negAt hInv k c hfin.1 (by omega) hfin.2
  have hBp : 0 < jf P prog k c (((bb : ℝ) - 2 ^ (P.W - 1)) / 2 ^ P.p) := by
    have hx := enc_point P.p (2 ^ (P.W - 1)) bb
    push_cast at hx
    obtain ⟨R', k', hInv, hfin⟩ := eval_sound P prog _ bb 0 witB hp hpW hbb (Nat.two_pow_pos _) hrB _ hx
    rw [Bool.and_eq_true, Nat.blt_eq] at hfin
    exact pos_of_posAt hInv k c hfin.1 (by omega) hfin.2
  refine ⟨hI, ?_⟩
  -- the interval as a set
  have hIcc : ∀ y : ℝ, Enc P.p (2 ^ (P.W - 1)) cb cr y ↔
      y ∈ Set.Icc (((cb : ℝ) - 2 ^ (P.W - 1) - cr) / 2 ^ P.p) (((cb : ℝ) - 2 ^ (P.W - 1) + cr) / 2 ^ P.p) := by
    intro y
    have e := enc_iff_mem_Icc P.p (2 ^ (P.W - 1)) cb cr y
    push_cast at e
    exact e
  have h1' : (cb : ℝ) ≤ ab + cr := by exact_mod_cast h1
  have h2' : (ab : ℝ) < bb := by exact_mod_cast h2
  have h3' : (bb : ℝ) ≤ cb + cr := by exact_mod_cast h3
  have hg : ∀ y ∈ Set.Icc (((cb : ℝ) - 2 ^ (P.W - 1) - cr) / 2 ^ P.p)
      (((cb : ℝ) - 2 ^ (P.W - 1) + cr) / 2 ^ P.p), HasDerivAt (jf P prog k c) (jf P prog k (c + 1) y) y := by
    intro y hy
    obtain ⟨d1, d2, _⟩ := hI y ((hIcc y).mpr hy)
    interval_cases c
    · exact d1
    · exact d2
  have hla : ((cb : ℝ) - 2 ^ (P.W - 1) - cr) / 2 ^ P.p ≤ ((ab : ℝ) - 2 ^ (P.W - 1)) / 2 ^ P.p :=
    div_le_div_of_nonneg_right (by linarith) hs.le
  have hbh : ((bb : ℝ) - 2 ^ (P.W - 1)) / 2 ^ P.p ≤ ((cb : ℝ) - 2 ^ (P.W - 1) + cr) / 2 ^ P.p :=
    div_le_div_of_nonneg_right (by linarith) hs.le
  obtain ⟨x, hx1, hx2, hx0, huniq⟩ := exists_unique_zero hla (div_lt_div_of_pos_right (by linarith) hs) hbh hg
    (fun y hy => (hI y ((hIcc y).mpr hy)).2.2) hA hBp
  exact ⟨x, hx1, hx2, (hIcc x).mpr ⟨hla.trans hx1.le, hx2.le.trans hbh⟩, hx0,
    fun y hy hy0 => huniq y ((hIcc y).mp hy) hy0⟩

/-! ## The value of a register and the stationary points -/

theorem getD_map_fst (regs : List RJ) (i : ℕ) : (regs.map Prod.fst).getD i 0 = (regs.getD i 0).1 := by
  induction regs generalizing i with
  | nil => rfl
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ n => exact ih n

/-- The value of the jet of an instruction is the real number of the instruction. -/
theorem jden_val (P : Params) (regs : List RJ) (ins : Instr) :
    (jden P regs ins).1 = den P (regs.map Prod.fst) ins := by
  cases ins <;> simp only [jden, den, rmul, rinv, rsqrt, getD_map_fst]

theorem jsemFrom_val (P : Params) : ∀ (prog : List Instr) (regs : List RJ),
    (jsemFrom P prog regs).map Prod.fst = sem P prog (regs.map Prod.fst)
  | [], _ => rfl
  | ins :: rest, regs => by
    have h := jsemFrom_val P rest (regs ++ [jden P regs ins])
    rw [List.map_append, List.map_cons, List.map_nil, jden_val] at h
    exact h

/-- The value of register `k` is the real number that the program of E6 defines. -/
theorem jf_zero (P : Params) (prog : List Instr) (k : ℕ) (y : ℝ) :
    jf P prog k 0 y = (sem P prog [y]).getD k 0 := by
  have h := jsemFrom_val P prog [(y, 1, 0)]
  show ((jsem P prog y).getD k 0).1 = _
  rw [← getD_map_fst]
  exact congrArg (fun l => l.getD k 0) h

/-- **Stationary points.** If the checker accepts with `c = 1`, the function `F` of register `k`
has exactly one stationary point in the ball `(cb, cr)`, and it lies between the points with the
midpoints `ab` and `bb`. -/
theorem stationary_sound (P : Params) (prog : List Instr) (k cb cr ab bb : ℕ) (witI witA witB : List ℕ)
    (h : check P prog k 1 cb cr ab bb witI witA witB = true) :
    ∃ x : ℝ, ((ab : ℝ) - 2 ^ (P.W - 1)) / 2 ^ P.p < x ∧ x < ((bb : ℝ) - 2 ^ (P.W - 1)) / 2 ^ P.p ∧
      HasDerivAt (fun y => (sem P prog [y]).getD k 0) 0 x ∧
      ∀ y : ℝ, Enc P.p (2 ^ (P.W - 1)) cb cr y →
        HasDerivAt (fun y => (sem P prog [y]).getD k 0) 0 y → y = x := by
  obtain ⟨hI, x, hx1, hx2, hxI, hx0, huniq⟩ := check_sound P prog k 1 cb cr ab bb witI witA witB h
  have hF : (fun y => (sem P prog [y]).getD k 0) = jf P prog k 0 := funext fun y => (jf_zero P prog k y).symm
  rw [hF]
  refine ⟨x, hx1, hx2, ?_, fun y hy hd => huniq y hy ((hI y hy).1.unique hd)⟩
  have hd := (hI x hxI).1
  rwa [hx0] at hd

/-- **Zeros.** If the checker accepts with `c = 0`, the function `F` of register `k` has exactly one
zero in the ball `(cb, cr)`, and it lies between the points with the midpoints `ab` and `bb`. -/
theorem zero_sound (P : Params) (prog : List Instr) (k cb cr ab bb : ℕ) (witI witA witB : List ℕ)
    (h : check P prog k 0 cb cr ab bb witI witA witB = true) :
    ∃ x : ℝ, ((ab : ℝ) - 2 ^ (P.W - 1)) / 2 ^ P.p < x ∧ x < ((bb : ℝ) - 2 ^ (P.W - 1)) / 2 ^ P.p ∧
      (sem P prog [x]).getD k 0 = 0 ∧
      ∀ y : ℝ, Enc P.p (2 ^ (P.W - 1)) cb cr y → (sem P prog [y]).getD k 0 = 0 → y = x := by
  obtain ⟨_, x, hx1, hx2, _, hx0, huniq⟩ := check_sound P prog k 0 cb cr ab bb witI witA witB h
  refine ⟨x, hx1, hx2, ?_, fun y hy hy0 => huniq y hy ?_⟩
  · rw [← jf_zero]
    exact hx0
  · rw [jf_zero]
    exact hy0

end CAP.Root

module

public import CAP.Subdivision.BernSound
public import N14.Box.Kernel

/-!
# T7, the slack on a domain: soundness of the checker of a tree

The checker `N14.Box.go` reads a tree and carries the array `X` of the polynomial of a cell and the arrays `Ys`
of the constraints. This file proves what an accepted tree means for these arrays (`go_sound`): the statement
`GoodT`. If `X` is the number of an array `f` and the `Ys` are the numbers of arrays `gs`, then at every point
`(u, v)` with nonnegative coordinates at which the value of every `g` is at most `AG` times the value of the
binomial array, the value of `f` is at least `A` times the value of the binomial array.

The proof follows `CAP.Bernstein.tree_good`. A split passes from the arrays to those of the two halves
(`child_rep`), and a point belongs to one of the halves (`child_point`); both lemmas hold for every array, so
that they apply to `X` and to the `Ys` at once. A leaf with multipliers compares the entries of
`X + ∑ μ_c Y_c` with those of `(A + ∑ μ_c AG) J` (`accGo_spec`).
-/

@[expose] public section

namespace N14.Box

open CAP CAP.Bernstein Finset Polynomial

/-- The table of the pass of one half of a split: `half` for `side = 0`, `halfR` otherwise. -/
noncomputable def colS (side n : ℕ) : ℕ → ℕ[X] := if side = 0 then col2 1 2 1 0 n else col2 1 0 1 2 n

/-- `X` is the number of the array `f`, whose entries are at most `2 * B` times those of the binomial array. -/
def Arr (P : Params) (B X : ℕ) (f : ℕ → ℕ) : Prop :=
  X = packSum P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) f ∧
    ∀ e, e < (P.n + 1) * (P.n + 1) * (P.n + 1) → f e ≤ 2 * B * cJ P.n e

/-- The array of one half of a split. -/
theorem child_rep (P : Params) (B a side : ℕ) (hV : 1 ≤ P.V) (hn : P.n ≤ P.V)
    (hB : 2 * B * 2 ^ (3 * P.n) < 2 ^ (P.V - 1)) (X : ℕ) (f : ℕ → ℕ) (hf : Arr P B X f) :
    Arr P B (child P a side X)
      (act (stride (P.n + 1) (min a 2)) (P.n + 1) (tab (colS side P.n)) (fun e => f e / 2 ^ P.n)) := by
  obtain ⟨hX, hf⟩ := hf
  have hV2 : 2 ^ (P.V - 1) ≤ 2 ^ P.V := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have ha2 : min a 2 ≤ 2 := Nat.min_le_right a 2
  have hfV : ∀ e, e < (P.n + 1) * (P.n + 1) * (P.n + 1) → f e < 2 ^ P.V := fun e he =>
    calc f e ≤ 2 * B * cJ P.n e := hf e he
      _ ≤ 2 * B * 2 ^ (3 * P.n) := Nat.mul_le_mul_left _ (cJ_le P.n e)
      _ < 2 ^ (P.V - 1) := hB
      _ ≤ 2 ^ P.V := hV2
  have hf'V : ∀ e, e < (P.n + 1) * (P.n + 1) * (P.n + 1) → f e / 2 ^ P.n < 2 ^ P.V := fun e he =>
    lt_of_le_of_lt (Nat.div_le_self _ _) (hfV e he)
  cases side with
  | zero =>
    have hc : colS 0 P.n = col2 1 2 1 0 P.n := if_pos rfl
    rw [hc]
    refine ⟨?_, half_bound P.n (min a 2) B ha2 1 2 1 0 linP_half f hf⟩
    show half P.n (sel a (vs1 P) (vs2 P) (vs3 P)) (sel a (msk1 P) (msk2 P) (msk3 P)) (floorN P X) = _
    rw [hX, (geom P a).1, (geom P a).2, floorN_eq P hV hn f hfV, half_rep P.V P.n (min a 2) hV _ hf'V]
  | succ k =>
    have hc : colS (k + 1) P.n = col2 1 0 1 2 P.n := if_neg (Nat.succ_ne_zero k)
    rw [hc]
    refine ⟨?_, half_bound P.n (min a 2) B ha2 1 0 1 2 linP_halfR f hf⟩
    show halfR P.n (sel a (vs1 P) (vs2 P) (vs3 P)) (sel a (msk1 P) (msk2 P) (msk3 P)) (floorN P X) = _
    rw [hX, (geom P a).1, (geom P a).2, floorN_eq P hV hn f hfV, halfR_rep P.V P.n (min a 2) hV _ hf'V]

/-- A point with nonnegative coordinates belongs to one of the two halves of a split: there are a side and a
point of this half such that the value of the pass of every array at the new point is the value of the array
at the old point. -/
theorem child_point (n a : ℕ) (ha : a ≤ 2) (u v : ℕ → ℝ) (hu : ∀ b, 0 ≤ u b) (hv : ∀ b, 0 ≤ v b) :
    ∃ (side : ℕ) (u' v' : ℕ → ℝ), (side = 0 ∨ side = 1) ∧ (∀ b, 0 ≤ u' b) ∧ (∀ b, 0 ≤ v' b) ∧
      2 ^ n * Jv n u' v' = Jv n u v ∧
      ∀ g : ℕ → ℕ, Phi (n + 1) (hwω n u' v') (act (stride (n + 1) a) (n + 1) (tab (colS side n)) g)
        = Phi (n + 1) (hwω n u v) g := by
  rcases le_total (u a) (v a) with huv | huv
  · refine ⟨0, u, updR v a ((v a - u a) / 2), Or.inl rfl, hu, ?_, ?_, fun g => ?_⟩
    · intro b
      by_cases hb : b = a
      · rw [hb, updR_self]
        linarith
      · rw [updR_ne _ _ _ _ hb]
        exact hv b
    · exact Jv_half n a ha u v u _ (fun _ _ => rfl) (fun b hb => updR_ne _ _ _ _ hb)
        (by rw [updR_self]; ring)
    · have hc : colS 0 n = col2 1 2 1 0 n := if_pos rfl
      rw [hc, Phi_col2 n a ha]
      refine Phi_congr_weight _ _ _ _ fun b k _ _ => ?_
      unfold hwω
      by_cases hb : b = a
      · rw [hb, updR_self, updR_self, updR_self]
        have ea : ((1 : ℕ) : ℝ) * u a + ((0 : ℕ) : ℝ) * ((v a - u a) / 2) = u a := by
          push_cast
          ring
        have eb : ((1 : ℕ) : ℝ) * u a + ((2 : ℕ) : ℝ) * ((v a - u a) / 2) = v a := by
          push_cast
          ring
        rw [ea, eb]
      · rw [updR_ne _ _ _ _ hb, updR_ne _ _ _ _ hb, updR_ne _ _ _ _ hb]
  · refine ⟨1, updR u a (v a), updR v a ((u a - v a) / 2), Or.inr rfl, ?_, ?_, ?_, fun g => ?_⟩
    · intro b
      by_cases hb : b = a
      · rw [hb, updR_self]
        exact hv _
      · rw [updR_ne _ _ _ _ hb]
        exact hu b
    · intro b
      by_cases hb : b = a
      · rw [hb, updR_self]
        linarith
      · rw [updR_ne _ _ _ _ hb]
        exact hv b
    · exact Jv_half n a ha u v _ _ (fun b hb => updR_ne _ _ _ _ hb) (fun b hb => updR_ne _ _ _ _ hb)
        (by rw [updR_self, updR_self]; ring)
    · have hc : colS 1 n = col2 1 0 1 2 n := if_neg (by decide)
      rw [hc, Phi_col2 n a ha]
      refine Phi_congr_weight _ _ _ _ fun b k _ _ => ?_
      unfold hwω
      by_cases hb : b = a
      · rw [hb, updR_self, updR_self, updR_self, updR_self]
        have ea : ((1 : ℕ) : ℝ) * v a + ((2 : ℕ) : ℝ) * ((u a - v a) / 2) = u a := by
          push_cast
          ring
        have eb : ((1 : ℕ) : ℝ) * v a + ((0 : ℕ) : ℝ) * ((u a - v a) / 2) = v a := by
          push_cast
          ring
        rw [ea, eb]
      · rw [updR_ne _ _ _ _ hb, updR_ne _ _ _ _ hb, updR_ne _ _ _ _ hb, updR_ne _ _ _ _ hb]

/-- The value of the array of the floors, times `2 ^ n`, is at most the value of the array. -/
theorem Phi_floor (n : ℕ) (u v : ℕ → ℝ) (hu : ∀ a, 0 ≤ u a) (hv : ∀ a, 0 ≤ v a) (f : ℕ → ℕ) :
    (2 : ℝ) ^ n * Phi (n + 1) (hwω n u v) (fun e => f e / 2 ^ n) ≤ Phi (n + 1) (hwω n u v) f := by
  have h0 := Phi_mono (n + 1) (hwω n u v) (W3_hw_nonneg n u v hu hv)
    (f := fun e => 2 ^ n * (f e / 2 ^ n)) (g := f) (fun e _ => Nat.mul_div_le (f e) (2 ^ n))
  rw [Phi_smul] at h0
  push_cast at h0
  exact h0

theorem Jv_nonneg (n : ℕ) (u v : ℕ → ℝ) (hu : ∀ a, 0 ≤ u a) (hv : ∀ a, 0 ≤ v a) : 0 ≤ Jv n u v := by
  unfold Jv
  have : ∀ a, 0 ≤ (u a + v a) ^ n := fun a => pow_nonneg (add_nonneg (hu a) (hv a)) _
  exact mul_nonneg (mul_nonneg (this 0) (this 1)) (this 2)

theorem Phi_nonneg (n : ℕ) (u v : ℕ → ℝ) (hu : ∀ a, 0 ≤ u a) (hv : ∀ a, 0 ≤ v a) (f : ℕ → ℕ) :
    0 ≤ Phi (n + 1) (hwω n u v) f := by
  unfold Phi
  exact sum_nonneg fun e _ => mul_nonneg (Nat.cast_nonneg _) (W3_hw_nonneg n u v hu hv e)

/-- The value of an array whose entries are at least `c` times those of the binomial array. -/
theorem Phi_ge (n c : ℕ) (u v : ℕ → ℝ) (hu : ∀ a, 0 ≤ u a) (hv : ∀ a, 0 ≤ v a) (f : ℕ → ℕ)
    (h : ∀ e, e < (n + 1) * (n + 1) * (n + 1) → c * cJ n e ≤ f e) :
    (c : ℝ) * Jv n u v ≤ Phi (n + 1) (hwω n u v) f := by
  have hm := Phi_mono (n + 1) (hwω n u v) (W3_hw_nonneg n u v hu hv) (f := fun e => c * cJ n e) (g := f) h
  rw [Phi_smul, Phi_cJ] at hm
  unfold Jv
  exact hm

/-! ## The statement for the arrays of a node -/

/-- The statement that an accepted tree proves for the number `X` of the array of the polynomial and the
numbers `Ys` of the arrays of the constraints. -/
def GoodT (P : Params) (AG : ℕ) (X : ℕ) (Ys : List ℕ) : Prop :=
  ∀ (f : ℕ → ℕ) (gs : List (ℕ → ℕ)), Arr P P.A X f → List.Forall₂ (Arr P AG) Ys gs →
    ∀ u v : ℕ → ℝ, (∀ a, 0 ≤ u a) → (∀ a, 0 ≤ v a) →
      (∀ g ∈ gs, Phi (P.n + 1) (hwω P.n u v) g ≤ (AG : ℝ) * Jv P.n u v) →
      (P.A : ℝ) * Jv P.n u v ≤ Phi (P.n + 1) (hwω P.n u v) f

/-- The conditions on the slot width that the trees of a run with at most `r` constraints need. -/
structure TreeFit (P : Params) (AG r mb : ℕ) : Prop where
  hV : 1 ≤ P.V
  hn : P.n ≤ P.V
  hfit : 2 * (P.A + r * 2 ^ mb * (AG + 1)) * 2 ^ (3 * P.n) < 2 ^ (P.V - 1)

theorem TreeFit.fitA {P : Params} {AG r mb : ℕ} (h : TreeFit P AG r mb) :
    2 * P.A * 2 ^ (3 * P.n) < 2 ^ (P.V - 1) :=
  lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))) h.hfit

/-- The sums of the leaves fit: for `d ≤ r * 2 ^ mb`. -/
theorem TreeFit.fitD {P : Params} {AG r mb : ℕ} (h : TreeFit P AG r mb) (d : ℕ) (hd : d ≤ r * 2 ^ mb) :
    2 * (P.A + d * AG) * 2 ^ (3 * P.n) < 2 ^ (P.V - 1) := by
  refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_left ?_ _))) h.hfit
  exact Nat.mul_le_mul hd (Nat.le_succ _)

theorem childs_length (P : Params) (a side : ℕ) (Ys : List ℕ) : (childs P a side Ys).length = Ys.length := by
  induction Ys with
  | nil => rfl
  | cons Y Ys ih => exact congrArg Nat.succ ih

/-- The arrays of one half of a split, for a list of arrays. -/
theorem childs_rep (P : Params) (B a side : ℕ) (hV : 1 ≤ P.V) (hn : P.n ≤ P.V)
    (hB : 2 * B * 2 ^ (3 * P.n) < 2 ^ (P.V - 1)) (Ys : List ℕ) (gs : List (ℕ → ℕ))
    (h : List.Forall₂ (Arr P B) Ys gs) :
    List.Forall₂ (Arr P B) (childs P a side Ys)
      (gs.map fun g => act (stride (P.n + 1) (min a 2)) (P.n + 1) (tab (colS side P.n)) (fun e => g e / 2 ^ P.n)) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hd _ ih => exact List.Forall₂.cons (child_rep P B a side hV hn hB _ _ hd) ih

/-- A split: the statement for the two halves gives the statement for the arrays. -/
theorem split_goodT (P : Params) (AG r mb a : ℕ) (hfit : TreeFit P AG r mb) (hr1 : 1 ≤ r) (X : ℕ) (Ys : List ℕ)
    (hl : GoodT P AG (child P a 0 X) (childs P a 0 Ys)) (hr : GoodT P AG (child P a 1 X) (childs P a 1 Ys)) :
    GoodT P AG X Ys := by
  intro f gs hf hgs u v hu hv hprem
  have ha2 : min a 2 ≤ 2 := Nat.min_le_right a 2
  have hBG : 2 * AG * 2 ^ (3 * P.n) < 2 ^ (P.V - 1) := by
    refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ?_)) hfit.hfit
    calc AG ≤ 1 * 1 * (AG + 1) := by omega
      _ ≤ r * 2 ^ mb * (AG + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul hr1 Nat.one_le_two_pow)
      _ ≤ P.A + r * 2 ^ mb * (AG + 1) := Nat.le_add_left _ _
  obtain ⟨side, u', v', hside, hu', hv', hJ, hΦ⟩ := child_point P.n (min a 2) ha2 u v hu hv
  have h2pos : (0 : ℝ) < 2 ^ P.n := by positivity
  -- the statement of the half
  have hgood : GoodT P AG (child P a side X) (childs P a side Ys) := by
    rcases hside with rfl | rfl
    · exact hl
    · exact hr
  have hfc := child_rep P P.A a side hfit.hV hfit.hn hfit.fitA X f hf
  have hgc := childs_rep P AG a side hfit.hV hfit.hn hBG Ys gs hgs
  have key := hgood _ _ hfc hgc u' v' hu' hv' (by
    intro g' hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    rw [hΦ (fun e => g e / 2 ^ P.n)]
    have h1 := Phi_floor P.n u v hu hv g
    have h2 := hprem g hg
    have h3 : (2 : ℝ) ^ P.n * Phi (P.n + 1) (hwω P.n u v) (fun e => g e / 2 ^ P.n)
        ≤ 2 ^ P.n * ((AG : ℝ) * Jv P.n u' v') := by
      calc (2 : ℝ) ^ P.n * Phi (P.n + 1) (hwω P.n u v) (fun e => g e / 2 ^ P.n)
          ≤ Phi (P.n + 1) (hwω P.n u v) g := h1
        _ ≤ (AG : ℝ) * Jv P.n u v := h2
        _ = 2 ^ P.n * ((AG : ℝ) * Jv P.n u' v') := by rw [← hJ]; ring
    exact le_of_mul_le_mul_left h3 h2pos)
  rw [hΦ (fun e => f e / 2 ^ P.n)] at key
  calc (P.A : ℝ) * Jv P.n u v = 2 ^ P.n * ((P.A : ℝ) * Jv P.n u' v') := by rw [← hJ]; ring
    _ ≤ 2 ^ P.n * Phi (P.n + 1) (hwω P.n u v) (fun e => f e / 2 ^ P.n) := mul_le_mul_of_nonneg_left key h2pos.le
    _ ≤ Phi (P.n + 1) (hwω P.n u v) f := Phi_floor P.n u v hu hv f

/-! ## The leaves -/

theorem AJ_packSum (P : Params) (c : ℕ) :
    c * binomJ P = packSum P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) (fun e => c * cJ P.n e) := by
  rw [binomJ_eq, ← packSum_mul]

theorem cJ_bound (P : Params) (c : ℕ) (hc : 2 * c * 2 ^ (3 * P.n) < 2 ^ (P.V - 1)) (e : ℕ) :
    2 * c * cJ P.n e < 2 ^ (P.V - 1) :=
  lt_of_le_of_lt (Nat.mul_le_mul_left _ (cJ_le P.n e)) hc

/-- A leaf: every entry of `X` is at least `A` times that of the binomial array. -/
theorem leaf_goodT (P : Params) (AG r mb : ℕ) (hfit : TreeFit P AG r mb) (X : ℕ) (Ys : List ℕ)
    (h : UniPos.geTest P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) X (P.A * binomJ P) = true) : GoodT P AG X Ys := by
  intro f gs hf _ u v hu hv _
  obtain ⟨hX, hfb⟩ := hf
  rw [hX, AJ_packSum] at h
  have key := UniPos.geTest_sound P.V _ f (fun e => P.A * cJ P.n e) hfit.hV
    (fun e he => lt_of_le_of_lt (hfb e he) (cJ_bound P P.A hfit.fitA e))
    (fun e _ => by
      have h3 := cJ_bound P P.A hfit.fitA e
      have e4 : 2 * P.A * cJ P.n e = P.A * cJ P.n e + P.A * cJ P.n e := by ring
      omega) h
  exact Phi_ge P.n P.A u v hu hv f key

/-- The sum of a leaf with multipliers. -/
theorem accGo_spec (P : Params) (AG mb : ℕ) : ∀ (Ys : List ℕ) (gs : List (ℕ → ℕ)),
    List.Forall₂ (Arr P AG) Ys gs → ∀ (s X m : ℕ) (F : ℕ → ℕ),
      X = packSum P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) F →
      ∃ (F' : ℕ → ℕ) (d : ℕ), accGo mb Ys s X m = (packSum P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) F', m + d) ∧
        d ≤ Ys.length * 2 ^ mb ∧
        (∀ e, e < (P.n + 1) * (P.n + 1) * (P.n + 1) → F' e ≤ F e + 2 * (d * AG) * cJ P.n e) ∧
        ∀ u v : ℕ → ℝ, (∀ a, 0 ≤ u a) → (∀ a, 0 ≤ v a) →
          (∀ g ∈ gs, Phi (P.n + 1) (hwω P.n u v) g ≤ (AG : ℝ) * Jv P.n u v) →
          Phi (P.n + 1) (hwω P.n u v) F' ≤ Phi (P.n + 1) (hwω P.n u v) F + (d : ℝ) * AG * Jv P.n u v := by
  intro Ys gs h
  induction h with
  | nil =>
    intro s X m F hX
    refine ⟨F, 0, ?_, Nat.zero_le _, fun e _ => Nat.le_add_right _ _, fun u v _ _ _ => ?_⟩
    · show (X, m) = _
      rw [hX]
      rfl
    · simp
  | @cons Y g Ys gs hd _ ih =>
    intro s X m F hX
    obtain ⟨hY, hgb⟩ := hd
    have hμ : s &&& mask mb < 2 ^ mb := by
      rw [mask_eq]
      exact Nat.and_lt_two_pow _ (Nat.sub_one_lt (Nat.two_pow_pos mb |>.ne'))
    have hstep : lin (Nat.land s (mask mb)) Y X
        = packSum P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) (fun e => (s &&& mask mb) * g e + F e) := by
      rw [lin_eq, hY, hX, packSum_add, packSum_mul]
      rfl
    obtain ⟨F', d, hacc, hd', hF', hΦ⟩ := ih (Nat.shiftRight s mb) _ (Nat.add m (Nat.land s (mask mb))) _ hstep
    refine ⟨F', (s &&& mask mb) + d, ?_, ?_, fun e he => ?_, fun u v hu hv hprem => ?_⟩
    · show accGo mb Ys (Nat.shiftRight s mb) (lin (Nat.land s (mask mb)) Y X) (Nat.add m (Nat.land s (mask mb))) = _
      rw [hacc]
      show (_, m + (s &&& mask mb) + d) = _
      rw [Nat.add_assoc]
    · have : (Ys.length + 1) * 2 ^ mb = 2 ^ mb + Ys.length * 2 ^ mb := by ring
      rw [List.length_cons, this]
      exact Nat.add_le_add hμ.le hd'
    · have h1 := hF' e he
      have h2 := hgb e he
      have h3 : (s &&& mask mb) * g e ≤ (s &&& mask mb) * (2 * AG * cJ P.n e) := Nat.mul_le_mul_left _ h2
      have h4 : (s &&& mask mb) * g e + F e + 2 * (d * AG) * cJ P.n e
          ≤ F e + 2 * (((s &&& mask mb) + d) * AG) * cJ P.n e := by nlinarith
      exact le_trans h1 h4
    · have h1 := hΦ u v hu hv (fun g' hg' => hprem g' (List.mem_cons_of_mem _ hg'))
      have h2 := hprem g List.mem_cons_self
      have h3 : Phi (P.n + 1) (hwω P.n u v) (fun e => (s &&& mask mb) * g e + F e)
          = ((s &&& mask mb : ℕ) : ℝ) * Phi (P.n + 1) (hwω P.n u v) g + Phi (P.n + 1) (hwω P.n u v) F := by
        rw [Phi_add, Phi_smul]
      rw [h3] at h1
      have hμ0 : (0 : ℝ) ≤ ((s &&& mask mb : ℕ) : ℝ) := Nat.cast_nonneg _
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left h2 hμ0]

/-- A leaf with multipliers. -/
theorem acc_goodT (R : Run) (P : Params) (r : ℕ) (hfit : TreeFit P R.AG r R.mb) (s X : ℕ) (Ys : List ℕ)
    (hlen : Ys.length ≤ r) (h : accOk R P (binomJ P) s X Ys = true) : GoodT P R.AG X Ys := by
  intro f gs hf hgs u v hu hv hprem
  obtain ⟨hX, hfb⟩ := hf
  obtain ⟨F', d, hacc, hd, hF', hΦ⟩ := accGo_spec P R.AG R.mb Ys gs hgs s X 0 f hX
  have hd' : d ≤ r * 2 ^ R.mb := le_trans hd (Nat.mul_le_mul_right _ hlen)
  have h' : UniPos.geTest P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) (accGo R.mb Ys s X 0).1
      ((P.A + (accGo R.mb Ys s X 0).2 * R.AG) * binomJ P) = true := h
  rw [hacc, AJ_packSum] at h'
  simp only [Nat.zero_add] at h'
  have hb := hfit.fitD d hd'
  have key := UniPos.geTest_sound P.V _ F' (fun e => (P.A + d * R.AG) * cJ P.n e) hfit.hV
    (fun e he => by
      have h1 := hF' e he
      have h2 := hfb e he
      have h3 := cJ_bound P (P.A + d * R.AG) hb e
      have e4 : 2 * (P.A + d * R.AG) * cJ P.n e = 2 * P.A * cJ P.n e + 2 * (d * R.AG) * cJ P.n e := by ring
      omega)
    (fun e _ => by
      have h3 := cJ_bound P (P.A + d * R.AG) hb e
      have e4 : 2 * (P.A + d * R.AG) * cJ P.n e = (P.A + d * R.AG) * cJ P.n e + (P.A + d * R.AG) * cJ P.n e := by
        ring
      omega) h'
  have h1 := Phi_ge P.n (P.A + d * R.AG) u v hu hv F' key
  have h2 := hΦ u v hu hv hprem
  push_cast at h1
  nlinarith

theorem binomJ_pos (P : Params) : 0 < binomJ P := by
  have h : ∀ k : ℕ, 0 < (1 + 1 <<< k) ^ P.n := fun k => pow_pos (Nat.add_pos_left Nat.one_pos _) _
  exact Nat.mul_pos (Nat.mul_pos (h _) (h _)) (h _)

/-- The entry `c` of a list of arrays is an array of the list, or the number `0`. -/
theorem nth_rep (P : Params) (B : ℕ) : ∀ (Ys : List ℕ) (gs : List (ℕ → ℕ)), List.Forall₂ (Arr P B) Ys gs →
    ∀ c : ℕ, nth Ys c = 0 ∨ ∃ g ∈ gs, Arr P B (nth Ys c) g := by
  intro Ys gs h
  induction h with
  | nil => exact fun _ => Or.inl rfl
  | @cons Y g Ys gs hd _ ih =>
    intro c
    cases c with
    | zero => exact Or.inr ⟨g, List.mem_cons_self, hd⟩
    | succ c =>
      rcases ih c with h0 | ⟨g', hg', ha⟩
      · exact Or.inl h0
      · exact Or.inr ⟨g', List.mem_cons_of_mem _ hg', ha⟩

/-- A leaf outside the domain: every entry of the array of a constraint is at least `AG + 1` times that of
the binomial array. -/
theorem out_goodT (P : Params) (AG r mb c : ℕ) (hfit : TreeFit P AG r mb) (hr1 : 1 ≤ r) (X : ℕ) (Ys : List ℕ)
    (h : UniPos.geTest P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) (nth Ys c) ((AG + 1) * binomJ P) = true) :
    GoodT P AG X Ys := by
  intro f gs _ hgs u v hu hv hprem
  have hJ := Jv_nonneg P.n u v hu hv
  have hAG1 : 2 * (AG + 1) * 2 ^ (3 * P.n) < 2 ^ (P.V - 1) := by
    refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ?_)) hfit.hfit
    calc AG + 1 = 1 * 1 * (AG + 1) := by ring
      _ ≤ r * 2 ^ mb * (AG + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul hr1 Nat.one_le_two_pow)
      _ ≤ P.A + r * 2 ^ mb * (AG + 1) := Nat.le_add_left _ _
  rcases nth_rep P AG Ys gs hgs c with h0 | ⟨g, hg, hY, hgb⟩
  · -- the number `0` is not accepted
    rw [h0] at h
    unfold UniPos.geTest at h
    rw [Bool.and_eq_true] at h
    have h1 : 0 - (AG + 1) * binomJ P + (AG + 1) * binomJ P = 0 := Nat.eq_of_beq_eq_true h.1
    have h2 := binomJ_pos P
    have h3 : 0 < (AG + 1) * binomJ P := Nat.mul_pos (Nat.succ_pos _) h2
    omega
  · rw [hY, AJ_packSum] at h
    have key := UniPos.geTest_sound P.V _ g (fun e => (AG + 1) * cJ P.n e) hfit.hV
      (fun e he => by
        have h1 := hgb e he
        have h3 := cJ_bound P (AG + 1) hAG1 e
        have e4 : 2 * (AG + 1) * cJ P.n e = 2 * AG * cJ P.n e + 2 * cJ P.n e := by ring
        omega)
      (fun e _ => by
        have h3 := cJ_bound P (AG + 1) hAG1 e
        have e4 : 2 * (AG + 1) * cJ P.n e = (AG + 1) * cJ P.n e + (AG + 1) * cJ P.n e := by ring
        omega) h
    have h1 := Phi_ge P.n (AG + 1) u v hu hv g key
    have h2 := hprem g hg
    push_cast at h1
    have h3 : Jv P.n u v = 0 := by nlinarith
    rw [h3, mul_zero]
    exact Phi_nonneg P.n u v hu hv f

/-! ## The tree -/

theorem go_succ (R : Run) (P : Params) (J f s X : ℕ) (Ys : List ℕ) (k : ℕ → Bool) :
    go R P J (f + 1) s X Ys k =
      Bool.rec (motive := fun _ => Bool)
        (Nat.rec (motive := fun _ => Bool)
          (UniPos.geTest P.V (cube P.n) X (Nat.mul P.A J) && k (Nat.shiftRight s 3))
          (fun t _ => Nat.rec (motive := fun _ => Bool)
            (accOk R P J (Nat.shiftRight s 3) X Ys && k (skip R.mb Ys (Nat.shiftRight s 3)))
            (fun t' _ => Nat.rec (motive := fun _ => Bool)
              (UniPos.geTest P.V (cube P.n) (nth Ys (Nat.land (Nat.shiftRight s 3) (mask R.ob)))
                  (Nat.mul (Nat.succ R.AG) J) && k (Nat.shiftRight s (Nat.add 3 R.ob)))
              (fun _ _ => false)
              t')
            t)
          (Nat.sub (Nat.land s 7) 3))
        (go R P J f (Nat.shiftRight s 3) (child P (Nat.land s 7) 0 X) (childs P (Nat.land s 7) 0 Ys)
          (fun s' => go R P J f s' (child P (Nat.land s 7) 1 X) (childs P (Nat.land s 7) 1 Ys) k))
        (Nat.blt (Nat.land s 7) 3) := rfl

/-- **The tree.** If the checker accepts a tree for the arrays `X` and `Ys`, the statement `GoodT` holds for
them, and the test of the rest of the number is accepted. -/
theorem go_sound (R : Run) (P : Params) (r : ℕ) (hfit : TreeFit P R.AG r R.mb) (hr1 : 1 ≤ r) :
    ∀ (fuel s X : ℕ) (Ys : List ℕ) (k : ℕ → Bool), Ys.length ≤ r →
      go R P (binomJ P) fuel s X Ys k = true → GoodT P R.AG X Ys ∧ ∃ s', k s' = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro s X Ys k _ h
    exact absurd h (by simp [go])
  | succ f ih =>
    intro s X Ys k hlen h
    rw [go_succ] at h
    cases hb : Nat.blt (Nat.land s 7) 3 with
    | true =>
      rw [hb] at h
      have h1 : go R P (binomJ P) f (Nat.shiftRight s 3) (child P (Nat.land s 7) 0 X)
          (childs P (Nat.land s 7) 0 Ys)
          (fun s' => go R P (binomJ P) f s' (child P (Nat.land s 7) 1 X) (childs P (Nat.land s 7) 1 Ys) k)
          = true := h
      obtain ⟨gl, s1, hs1⟩ := ih _ _ _ _ (by rw [childs_length]; exact hlen) h1
      obtain ⟨gr, s2, hs2⟩ := ih _ _ _ _ (by rw [childs_length]; exact hlen) hs1
      exact ⟨split_goodT P R.AG r R.mb _ hfit hr1 X Ys gl gr, s2, hs2⟩
    | false =>
      rw [hb] at h
      generalize Nat.sub (Nat.land s 7) 3 = t at h
      cases t with
      | zero =>
        have h1 : (UniPos.geTest P.V (cube P.n) X (Nat.mul P.A (binomJ P)) && k (Nat.shiftRight s 3)) = true := h
        rw [Bool.and_eq_true] at h1
        exact ⟨leaf_goodT P R.AG r R.mb hfit X Ys h1.1, _, h1.2⟩
      | succ t =>
        cases t with
        | zero =>
          have h1 : (accOk R P (binomJ P) (Nat.shiftRight s 3) X Ys
              && k (skip R.mb Ys (Nat.shiftRight s 3))) = true := h
          rw [Bool.and_eq_true] at h1
          exact ⟨acc_goodT R P r hfit _ X Ys hlen h1.1, _, h1.2⟩
        | succ t =>
          cases t with
          | zero =>
            have h1 : (UniPos.geTest P.V (cube P.n) (nth Ys (Nat.land (Nat.shiftRight s 3) (mask R.ob)))
                (Nat.mul (Nat.succ R.AG) (binomJ P)) && k (Nat.shiftRight s (Nat.add 3 R.ob))) = true := h
            rw [Bool.and_eq_true] at h1
            exact ⟨out_goodT P R.AG r R.mb _ hfit hr1 X Ys h1.1, _, h1.2⟩
          | succ t => exact absurd (show false = true from h) (by decide)

end N14.Box

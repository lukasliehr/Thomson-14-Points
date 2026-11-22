module

public import N14.Jet.Rep
public import CAP.Core.PackedMul

/-!
# Jets: the packed numbers of a pass

Every jet of the checker is the result of one pass over the slots (`pass`), followed by the test that the sum
of all its slots is below `2 ^ w` (`fin`). This file states what a pass computes:

* `pass_P`, `pass_N`, `pass_R`: the three numbers are the packed numbers (`CAP.packSum`) of the functions
  `e ↦ (h e).p`, `(h e).n`, `(h e).r` on the valid slots (the slots of `idxs`), and `0` elsewhere;
* `IsPass w J h`: the jet `J` consists of these numbers, and the sum of all slots is below `2 ^ w`. Then the
  slots can be read (`IsPass.slotP`, …), the number `S` holds the sums by degree (`IsPass.nd_eq`) and the sum of
  all slots (`IsPass.total_eq`);
* `fin_isPass`: a jet `fin par (pass w h idxs) K ok` whose flag is set is such a jet.
-/

@[expose] public section

namespace N14.Jet

open CAP Finset

theorem idxs_nodup : idxs.Nodup := by decide +kernel

/-- The sum of the three parts of a triple. -/
def T3.t (x : T3) : ℕ := x.p + x.n + x.r

theorem pass_cons (w : ℕ) (h : ℕ → T3) (e : ℕ) (l : List ℕ) :
    pass w h (e :: l) = ⟨(pass w h l).P + (h e).p <<< (w * e), (pass w h l).N + (h e).n <<< (w * e),
      (pass w h l).R + (h e).r <<< (w * e),
      (pass w h l).S + ((h e).p + (h e).n + (h e).r) * (1 <<< (w * (e / 216)) + 1 <<< (w * 6)), 0, true⟩ :=
  rfl

theorem pass_sums (w : ℕ) (h : ℕ → T3) (l : List ℕ) :
    (pass w h l).P = (l.map fun e => (h e).p * 2 ^ (w * e)).sum ∧
    (pass w h l).N = (l.map fun e => (h e).n * 2 ^ (w * e)).sum ∧
    (pass w h l).R = (l.map fun e => (h e).r * 2 ^ (w * e)).sum ∧
    (pass w h l).S = (l.map fun e => (h e).t * (2 ^ (w * (e / 216)) + 2 ^ (w * 6))).sum := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons e l ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    rw [pass_cons]
    simp only [List.map_cons, List.sum_cons, Nat.shiftLeft_eq, one_mul]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1, add_comm]
    · rw [h2, add_comm]
    · rw [h3, add_comm]
    · rw [h4, add_comm]
      rfl

/-- A sum over the list of the slots as a sum over all slots. -/
theorem sum_idxs (g : ℕ → ℕ) : (idxs.map g).sum = ∑ e ∈ range 1296, if Valid e then g e else 0 := by
  rw [← List.sum_toFinset g idxs_nodup, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext e
  rw [List.mem_toFinset, mem_filter, mem_range, ← valid_iff_mem]
  exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩

theorem sum_idxs_pack (w : ℕ) (g : ℕ → ℕ) :
    (idxs.map fun e => g e * 2 ^ (w * e)).sum = packSum w 1296 (fun e => if Valid e then g e else 0) := by
  rw [sum_idxs]
  unfold packSum
  refine Finset.sum_congr rfl fun e _ => ?_
  show (if Valid e then g e * 2 ^ (w * e) else 0) = (if Valid e then g e else 0) * 2 ^ (w * e)
  split_ifs
  · rfl
  · rw [zero_mul]

theorem pass_P (w : ℕ) (h : ℕ → T3) :
    (pass w h idxs).P = packSum w 1296 (fun e => if Valid e then (h e).p else 0) := by
  rw [(pass_sums w h idxs).1, sum_idxs_pack]

theorem pass_N (w : ℕ) (h : ℕ → T3) :
    (pass w h idxs).N = packSum w 1296 (fun e => if Valid e then (h e).n else 0) := by
  rw [(pass_sums w h idxs).2.1, sum_idxs_pack]

theorem pass_R (w : ℕ) (h : ℕ → T3) :
    (pass w h idxs).R = packSum w 1296 (fun e => if Valid e then (h e).r else 0) := by
  rw [(pass_sums w h idxs).2.2.1, sum_idxs_pack]

theorem pass_S (w : ℕ) (h : ℕ → T3) :
    (pass w h idxs).S
      = ∑ e ∈ range 1296, if Valid e then (h e).t * (2 ^ (w * (e / 216)) + 2 ^ (w * 6)) else 0 := by
  rw [(pass_sums w h idxs).2.2.2, sum_idxs]

/-- The jet `J` is the result of the pass with the triples `h`, and no slot overflows. -/
structure IsPass (w : ℕ) (J : Jet) (h : ℕ → T3) : Prop where
  hP : J.P = packSum w 1296 (fun e => if Valid e then (h e).p else 0)
  hN : J.N = packSum w 1296 (fun e => if Valid e then (h e).n else 0)
  hR : J.R = packSum w 1296 (fun e => if Valid e then (h e).r else 0)
  hS : J.S = ∑ e ∈ range 1296, if Valid e then (h e).t * (2 ^ (w * (e / 216)) + 2 ^ (w * 6)) else 0
  tot : (∑ e ∈ range 1296, if Valid e then (h e).t else 0) < 2 ^ w

/-- The sum of the slots of degree `d`. -/
def nsum (h : ℕ → T3) (d : ℕ) : ℕ := ∑ e ∈ range 1296, if sdeg e = d then (if Valid e then (h e).t else 0) else 0

/-- The sum of all slots. -/
def tsum (h : ℕ → T3) : ℕ := ∑ e ∈ range 1296, if Valid e then (h e).t else 0

theorem tsum_eq (h : ℕ → T3) : tsum h = ∑ d ∈ range 6, nsum h d := sum_by_deg _

theorem nsum_le (h : ℕ → T3) (d : ℕ) (hd : d < 6) : nsum h d ≤ tsum h := by
  rw [tsum_eq]
  exact Finset.single_le_sum (f := fun d => nsum h d) (fun _ _ => Nat.zero_le _) (mem_range.mpr hd)

theorem term_le (h : ℕ → T3) (e : ℕ) (he : e < 1296) : (if Valid e then (h e).t else 0) ≤ tsum h :=
  Finset.single_le_sum (f := fun e => if Valid e then (h e).t else 0) (fun _ _ => Nat.zero_le _)
    (mem_range.mpr he)

/-- The number `S` of a pass: the sums by degree in the slots `0, …, 5`, and the sum of all slots above. -/
theorem stats_eq (w : ℕ) (h : ℕ → T3) :
    (∑ e ∈ range 1296, if Valid e then (h e).t * (2 ^ (w * (e / 216)) + 2 ^ (w * 6)) else 0)
      = packSum w 6 (nsum h) + tsum h * 2 ^ (w * 6) := by
  have e1 : ∀ e : ℕ, (if Valid e then (h e).t * (2 ^ (w * (e / 216)) + 2 ^ (w * 6)) else 0)
      = (if Valid e then (h e).t else 0) * 2 ^ (w * sdeg e)
        + (if Valid e then (h e).t else 0) * 2 ^ (w * 6) := by
    intro e
    unfold sdeg
    split_ifs
    · ring
    · simp
  simp only [e1]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  have hA : (∑ e ∈ range 1296, (if Valid e then (h e).t else 0) * 2 ^ (w * sdeg e)) = packSum w 6 (nsum h) := by
    rw [sum_by_deg (fun e => (if Valid e then (h e).t else 0) * 2 ^ (w * sdeg e))]
    unfold packSum nsum
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases hd : sdeg e = d
    · rw [if_pos hd, if_pos hd, hd]
    · rw [if_neg hd, if_neg hd, zero_mul]
  rw [hA]
  rfl

namespace IsPass

variable {w : ℕ} {J : Jet} {h : ℕ → T3}

theorem tsum_lt (H : IsPass w J h) : tsum h < 2 ^ w := H.tot

theorem lt (H : IsPass w J h) (e : ℕ) (he : e < 1296) : (if Valid e then (h e).t else 0) < 2 ^ w :=
  lt_of_le_of_lt (term_le h e he) H.tot

theorem slotP (H : IsPass w J h) (e : ℕ) (he : e < 1296) :
    slot w J.P e = if Valid e then (h e).p else 0 := by
  rw [H.hP]
  refine slot_packSum w 1296 _ (fun j hj => ?_) e he
  have := H.lt j hj
  unfold T3.t at this
  split_ifs at this ⊢ <;> omega

theorem slotN (H : IsPass w J h) (e : ℕ) (he : e < 1296) :
    slot w J.N e = if Valid e then (h e).n else 0 := by
  rw [H.hN]
  refine slot_packSum w 1296 _ (fun j hj => ?_) e he
  have := H.lt j hj
  unfold T3.t at this
  split_ifs at this ⊢ <;> omega

theorem slotR (H : IsPass w J h) (e : ℕ) (he : e < 1296) :
    slot w J.R e = if Valid e then (h e).r else 0 := by
  rw [H.hR]
  refine slot_packSum w 1296 _ (fun j hj => ?_) e he
  have := H.lt j hj
  unfold T3.t at this
  split_ifs at this ⊢ <;> omega

theorem S_eq (H : IsPass w J h) : J.S = packSum w 6 (nsum h) + tsum h * 2 ^ (w * 6) := by
  rw [H.hS, stats_eq]

theorem total_eq (H : IsPass w J h) : total w J = tsum h := by
  unfold total
  show J.S >>> (w * 6) = tsum h
  rw [Nat.shiftRight_eq_div_pow, H.S_eq, Nat.add_mul_div_right _ _ (Nat.two_pow_pos (w * 6)),
    Nat.div_eq_of_lt (packSum_lt w 6 (nsum h) fun d hd => lt_of_le_of_lt (nsum_le h d hd) H.tot), zero_add]

theorem nd_eq (H : IsPass w J h) (d : ℕ) (hd : d < 6) : nd w J d = nsum h d := by
  unfold nd
  have e : J.S = packSum w 7 (fun j => if j < 6 then nsum h j else tsum h) := by
    have h1 : packSum w 6 (fun j => if j < 6 then nsum h j else tsum h) = packSum w 6 (nsum h) :=
      packSum_congr w 6 fun j hj => by rw [if_pos hj]
    have h2 : packSum w (7 - 6) (fun j => if j + 6 < 6 then nsum h (j + 6) else tsum h) = tsum h := by
      simp [packSum]
    rw [H.S_eq, packSum_split w 6 7 _ (by norm_num), h1, h2, mul_comm]
  rw [e]
  rw [slot_packSum w 7 _ (fun j hj => ?_) d (by omega), if_pos hd]
  split_ifs with h6
  · exact lt_of_le_of_lt (nsum_le h j h6) H.tot
  · exact H.tot

end IsPass

/-- **A jet of a pass whose flag is set.** -/
theorem fin_isPass (par : Par) (h : ℕ → T3) (K : ℕ) (ok : Bool)
    (hok : (fin par (pass par.w h idxs) K ok).ok = true) :
    ok = true ∧ IsPass par.w (fin par (pass par.w h idxs) K ok) h := by
  have h1 : (ok && Nat.blt (total par.w (pass par.w h idxs)) (Nat.shiftLeft 1 par.w)) = true := hok
  rw [Bool.and_eq_true] at h1
  obtain ⟨h2, h3⟩ := h1
  have h4 : total par.w (pass par.w h idxs) < 2 ^ par.w := by
    have := Nat.blt_eq.mp h3
    rw [show Nat.shiftLeft 1 par.w = 2 ^ par.w from Nat.one_shiftLeft par.w] at this
    exact this
  have hS := pass_S par.w h
  rw [stats_eq] at hS
  have h5 : tsum h ≤ total par.w (pass par.w h idxs) := by
    unfold total
    show tsum h ≤ (pass par.w h idxs).S >>> (par.w * 6)
    rw [Nat.shiftRight_eq_div_pow, Nat.le_div_iff_mul_le (Nat.two_pow_pos _), hS]
    exact Nat.le_add_left _ _
  refine ⟨h2, ⟨pass_P par.w h, pass_N par.w h, pass_R par.w h, pass_S par.w h, lt_of_le_of_lt h5 h4⟩⟩

theorem fin_K (par : Par) (a : Jet) (K : ℕ) (ok : Bool) : (fin par a K ok).K = K := rfl

end N14.Jet

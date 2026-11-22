module

public import N14.Jet.SoundBase

/-!
# Jets: soundness of the checker, variables and trigonometric functions of a variable

`good_var`: the jet `jvar par k cp cn cr` encloses `x ↦ x k' + a` for a constant `a` with the enclosure
`(cp, cn, cr)`; `k' = min k 3` is the variable that the checker uses for the number `k` (`kf`).
`good_trig`: the jet `jtrig par k …` encloses `x ↦ a cos (x k') - b sin (x k')`.
-/

@[expose] public section

namespace N14.Jet

open CAP Finset

/-- The variable with the number `k`: the checker uses the variable 3 for every number above 2. -/
def kf (k : ℕ) : Fin 4 := ⟨min k 3, by omega⟩

theorem uk_eq (k : ℕ) : uk k = if k = 0 then 216 else if k = 1 then 217 else if k = 2 then 222 else 252 := by
  unfold uk
  rw [cond_beq, cond_beq, cond_beq]

theorem uk_kf (k : ℕ) : uk (kf k).val = uk k := by
  rw [uk_eq, uk_eq]
  show (if min k 3 = 0 then 216 else if min k 3 = 1 then 217 else if min k 3 = 2 then 222 else 252)
    = if k = 0 then 216 else if k = 1 then 217 else if k = 2 then 222 else 252
  rcases Nat.lt_or_ge k 3 with h | h
  · rw [Nat.min_eq_left h.le]
  · rw [Nat.min_eq_right h]
    have h0 : k ≠ 0 := by omega
    have h1 : k ≠ 1 := by omega
    have h2 : k ≠ 2 := by omega
    simp [h0, h1, h2]

theorem uk_ge (k : ℕ) : 216 ≤ uk k := by
  rw [uk_eq]
  split_ifs <;> omega

/-- A valid slot that is a multiple of the slot of a variable is the slot of a power of at most 5. -/
theorem div_uk_lt (k e : ℕ) (he : e < 1296) : e / uk k < 6 := by
  have h := uk_ge k
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  omega

/-! ## A variable -/

/-- The triple of a slot of the jet of a variable. -/
def varH (s k cp cn cr : ℕ) (e : ℕ) : T3 :=
  cond (Nat.beq e 0) ⟨cp, cn, cr⟩ (cond (Nat.beq e (uk k)) ⟨Nat.shiftLeft 1 s, 0, 0⟩ ⟨0, 0, 0⟩)

theorem varH_eq (s k cp cn cr e : ℕ) :
    varH s k cp cn cr e = if e = 0 then ⟨cp, cn, cr⟩ else if e = uk k then ⟨2 ^ s, 0, 0⟩ else ⟨0, 0, 0⟩ := by
  unfold varH
  rw [cond_beq, cond_beq]
  show _ = if e = 0 then (⟨cp, cn, cr⟩ : T3) else if e = uk k then ⟨2 ^ s, 0, 0⟩ else ⟨0, 0, 0⟩
  rw [show Nat.shiftLeft 1 s = 2 ^ s from Nat.one_shiftLeft s]

theorem good_var (par : Par) (r : ℝ) (k cp cn cr : ℕ) (a : ℝ)
    (ha : |2 ^ par.s * a - ((cp : ℝ) - cn)| ≤ cr) :
    Good par r (jvar par k cp cn cr) (fun x => x (kf k) + a) := by
  intro hok
  obtain ⟨_, hp⟩ := fin_isPass par (varH par.s k cp cn cr) 0 true hok
  refine ⟨_, _, 0, hp, Rep.var r (kf k) a, le_refl 0, ?_, ?_⟩
  · show (0 : ℝ) * 2 ^ par.s ≤ ((0 : ℕ) : ℝ)
    simp
  · intro e hv
    have hu := uk_ge k
    show |2 ^ par.s * (∑ j ∈ range 6, if e = j * uk (kf k).val then
        (if j = 0 then a else if j = 1 then (1 : ℝ) else 0) else 0)
      - (((varH par.s k cp cn cr e).p : ℝ) - (varH par.s k cp cn cr e).n)| ≤ (varH par.s k cp cn cr e).r
    rw [powers_coef, uk_kf, varH_eq]
    by_cases h0 : e = 0
    · subst h0
      rw [if_pos rfl, if_pos ⟨Nat.zero_mod _, by rw [Nat.zero_div]; norm_num⟩, Nat.zero_div, if_pos rfl]
      exact ha
    · rw [if_neg h0]
      by_cases h1 : e = uk k
      · rw [if_pos h1, h1, if_pos ⟨Nat.mod_self _, by rw [Nat.div_self (by omega)]; norm_num⟩,
          Nat.div_self (by omega), if_neg (by norm_num), if_pos rfl]
        push_cast
        simp
      · rw [if_neg h1]
        have hz : (if e % uk k = 0 ∧ e / uk k < 6 then
            (if e / uk k = 0 then a else if e / uk k = 1 then (1 : ℝ) else 0) else 0) = 0 := by
          by_cases hm : e % uk k = 0 ∧ e / uk k < 6
          · rw [if_pos hm]
            have he : e = e / uk k * uk k := by
              have := Nat.div_add_mod e (uk k)
              rw [hm.1, add_zero, mul_comm] at this
              exact this.symm
            have hj0 : e / uk k ≠ 0 := by
              intro hj
              rw [hj, zero_mul] at he
              exact h0 he
            have hj1 : e / uk k ≠ 1 := by
              intro hj
              rw [hj, one_mul] at he
              exact h1 he
            rw [if_neg hj0, if_neg hj1]
          · rw [if_neg hm]
        rw [hz]
        simp

/-! ## The trigonometric functions of a variable -/

/-- The triple of a slot of the trigonometric jet. -/
def trigH (k cp cn cr sp sn sr : ℕ) (e : ℕ) : T3 :=
  cond (Nat.beq (Nat.mod e (uk k)) 0)
    (cond (Nat.beq (Nat.div e (uk k)) 0) (tput cp cn cr 1 false)
      (cond (Nat.beq (Nat.div e (uk k)) 1) (tput sp sn sr 1 true)
      (cond (Nat.beq (Nat.div e (uk k)) 2) (tput cp cn cr 2 true)
      (cond (Nat.beq (Nat.div e (uk k)) 3) (tput sp sn sr 6 false)
      (cond (Nat.beq (Nat.div e (uk k)) 4) (tput cp cn cr 24 false)
      (cond (Nat.beq (Nat.div e (uk k)) 5) (tput sp sn sr 120 true) ⟨0, 0, 0⟩))))))
    ⟨0, 0, 0⟩

theorem jtrig_eq (par : Par) (k cp cn cr sp sn sr : ℕ) :
    jtrig par k cp cn cr sp sn sr = fin par (pass par.w (trigH k cp cn cr sp sn sr) idxs)
      (Nat.add (cdivn (Nat.mul (Nat.add (Nat.add cp cn) cr) 7) 4320)
        (cdivn (Nat.mul (Nat.add (Nat.add sp sn) sr) 33) 18063360)) true := rfl

/-- The triple of `tput` encloses `±Y / d`. -/
theorem tput_sound (p n r d : ℕ) (hd : 0 < d) (neg : Bool) (Y : ℝ) (hY : |Y - ((p : ℝ) - n)| ≤ r) :
    |(if neg then -Y else Y) / d - (((tput p n r d neg).p : ℝ) - (tput p n r d neg).n)|
      ≤ (tput p n r d neg).r := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hp := Nat.div_add_mod p d
  have hn := Nat.div_add_mod n d
  have hpm := Nat.mod_lt p hd
  have hnm := Nat.mod_lt n hd
  have ep : (p : ℝ) = d * (p / d : ℕ) + (p % d : ℕ) := by exact_mod_cast hp.symm
  have en : (n : ℝ) = d * (n / d : ℕ) + (n % d : ℕ) := by exact_mod_cast hn.symm
  have hflag : |((p % d : ℕ) : ℝ) / d - ((n % d : ℕ) : ℝ) / d| ≤ ((1 - (1 - (p % d + n % d)) : ℕ) : ℝ) := by
    by_cases h0 : p % d + n % d = 0
    · have h1 : p % d = 0 := by omega
      have h2 : n % d = 0 := by omega
      rw [h0, h1, h2]
      simp
    · have h1 : 1 - (1 - (p % d + n % d)) = 1 := by omega
      rw [h1, Nat.cast_one, abs_le]
      have a1 : ((p % d : ℕ) : ℝ) / d < 1 := by
        rw [div_lt_one hd']
        exact_mod_cast hpm
      have a2 : ((n % d : ℕ) : ℝ) / d < 1 := by
        rw [div_lt_one hd']
        exact_mod_cast hnm
      have a3 : (0 : ℝ) ≤ ((p % d : ℕ) : ℝ) / d := by positivity
      have a4 : (0 : ℝ) ≤ ((n % d : ℕ) : ℝ) / d := by positivity
      constructor <;> linarith
  have hr := cdivn_ge r d hd
  have g := abs_le.mp hY
  have b1 : (Y - ((p : ℝ) - n)) / d ≤ (r : ℝ) / d := div_le_div_of_nonneg_right g.2 hd'.le
  have b2 : -((r : ℝ) / d) ≤ (Y - ((p : ℝ) - n)) / d := by
    rw [← neg_div]
    exact div_le_div_of_nonneg_right g.1 hd'.le
  have f := abs_le.mp hflag
  have er : (tput p n r d neg).r = cdivn r d + (1 - (1 - (p % d + n % d))) := by
    unfold tput
    cases neg <;> rfl
  have key : Y / d - (((p / d : ℕ) : ℝ) - ((n / d : ℕ) : ℝ))
      = (Y - ((p : ℝ) - n)) / d + (((p % d : ℕ) : ℝ) / d - ((n % d : ℕ) : ℝ) / d) := by
    rw [ep, en]
    field_simp
    ring
  rw [er]
  push_cast
  cases neg
  · have e1 : (tput p n r d false).p = p / d ∧ (tput p n r d false).n = n / d := ⟨rfl, rfl⟩
    rw [e1.1, e1.2]
    simp only [Bool.false_eq_true, if_false]
    rw [key, abs_le]
    constructor <;> linarith [f.1, f.2]
  · have e1 : (tput p n r d true).p = n / d ∧ (tput p n r d true).n = p / d := ⟨rfl, rfl⟩
    rw [e1.1, e1.2]
    simp only [if_true]
    have key' : -Y / d - (((n / d : ℕ) : ℝ) - ((p / d : ℕ) : ℝ))
        = -((Y - ((p : ℝ) - n)) / d + (((p % d : ℕ) : ℝ) / d - ((n % d : ℕ) : ℝ) / d)) := by
      rw [← key]
      ring
    rw [key', abs_neg, abs_le]
    constructor <;> linarith [f.1, f.2]

theorem good_trig (par : Par) (r : ℝ) (hr : r ≤ rb) (k cp cn cr sp sn sr : ℕ) (a b : ℝ)
    (ha : |2 ^ par.s * a - ((cp : ℝ) - cn)| ≤ cr) (hb : |2 ^ par.s * b - ((sp : ℝ) - sn)| ≤ sr) :
    Good par r (jtrig par k cp cn cr sp sn sr)
      (fun x => a * Real.cos (x (kf k)) - b * Real.sin (x (kf k))) := by
  intro hok
  rw [jtrig_eq] at hok ⊢
  obtain ⟨_, hp⟩ := fin_isPass par (trigH k cp cn cr sp sn sr) _ true hok
  have hd : (0 : ℝ) < 2 ^ par.s := by positivity
  have hrb : rb ≤ 1 := by
    unfold rb
    norm_num
  have ga := abs_le.mp ha
  have gb := abs_le.mp hb
  have habs : |a| * 2 ^ par.s ≤ (cp : ℝ) + cn + cr := by
    rw [← abs_of_pos hd, ← abs_mul, mul_comm, abs_le]
    have h1 : (0 : ℝ) ≤ cp := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ cn := Nat.cast_nonneg _
    constructor <;> linarith [ga.1, ga.2]
  have hbbs : |b| * 2 ^ par.s ≤ (sp : ℝ) + sn + sr := by
    rw [← abs_of_pos hd, ← abs_mul, mul_comm, abs_le]
    have h1 : (0 : ℝ) ≤ sp := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ sn := Nat.cast_nonneg _
    constructor <;> linarith [gb.1, gb.2]
  refine ⟨_, _, _, hp, Rep.trig r rb hr hrb (kf k) a b, ?_, ?_, ?_⟩
  · unfold rb
    positivity
  · show (|a| * (7 / 4320) + |b| * (rb / 4410)) * 2 ^ par.s
      ≤ ((cdivn ((cp + cn + cr) * 7) 4320 + cdivn ((sp + sn + sr) * 33) 18063360 : ℕ) : ℝ)
    have c1 := cdivn_ge ((cp + cn + cr) * 7) 4320 (by norm_num)
    have c2 := cdivn_ge ((sp + sn + sr) * 33) 18063360 (by norm_num)
    push_cast at c1 c2 ⊢
    unfold rb
    have t1 : |a| * (7 / 4320) * 2 ^ par.s ≤ ((cp : ℝ) + cn + cr) * 7 / 4320 := by
      have := mul_le_mul_of_nonneg_right habs (by norm_num : (0 : ℝ) ≤ 7 / 4320)
      linarith
    have t2 : |b| * (33 / 4096 / 4410) * 2 ^ par.s ≤ ((sp : ℝ) + sn + sr) * 33 / 18063360 := by
      have := mul_le_mul_of_nonneg_right hbbs (by norm_num : (0 : ℝ) ≤ 33 / 18063360)
      linarith
    linarith
  · intro e hv
    have he := hv.1
    have hu := uk_ge k
    have hj := div_uk_lt k e he
    show |2 ^ par.s * (∑ j ∈ range 6, if e = j * uk (kf k).val then Rep.tcoef a b j else 0)
      - (((trigH k cp cn cr sp sn sr e).p : ℝ) - (trigH k cp cn cr sp sn sr e).n)|
      ≤ (trigH k cp cn cr sp sn sr e).r
    rw [powers_coef, uk_kf]
    unfold trigH
    rw [cond_beq]
    show |2 ^ par.s * (if e % uk k = 0 ∧ e / uk k < 6 then Rep.tcoef a b (e / uk k) else 0)
      - (((if e % uk k = 0 then
            (cond (Nat.beq (e / uk k) 0) (tput cp cn cr 1 false)
            (cond (Nat.beq (e / uk k) 1) (tput sp sn sr 1 true)
            (cond (Nat.beq (e / uk k) 2) (tput cp cn cr 2 true)
            (cond (Nat.beq (e / uk k) 3) (tput sp sn sr 6 false)
            (cond (Nat.beq (e / uk k) 4) (tput cp cn cr 24 false)
            (cond (Nat.beq (e / uk k) 5) (tput sp sn sr 120 true) ⟨0, 0, 0⟩))))))
          else (⟨0, 0, 0⟩ : T3)).p : ℝ)
        - (if e % uk k = 0 then
            (cond (Nat.beq (e / uk k) 0) (tput cp cn cr 1 false)
            (cond (Nat.beq (e / uk k) 1) (tput sp sn sr 1 true)
            (cond (Nat.beq (e / uk k) 2) (tput cp cn cr 2 true)
            (cond (Nat.beq (e / uk k) 3) (tput sp sn sr 6 false)
            (cond (Nat.beq (e / uk k) 4) (tput cp cn cr 24 false)
            (cond (Nat.beq (e / uk k) 5) (tput sp sn sr 120 true) ⟨0, 0, 0⟩))))))
          else (⟨0, 0, 0⟩ : T3)).n)|
      ≤ (if e % uk k = 0 then
            (cond (Nat.beq (e / uk k) 0) (tput cp cn cr 1 false)
            (cond (Nat.beq (e / uk k) 1) (tput sp sn sr 1 true)
            (cond (Nat.beq (e / uk k) 2) (tput cp cn cr 2 true)
            (cond (Nat.beq (e / uk k) 3) (tput sp sn sr 6 false)
            (cond (Nat.beq (e / uk k) 4) (tput cp cn cr 24 false)
            (cond (Nat.beq (e / uk k) 5) (tput sp sn sr 120 true) ⟨0, 0, 0⟩))))))
          else (⟨0, 0, 0⟩ : T3)).r
    by_cases hm : e % uk k = 0
    · rw [if_pos ⟨hm, hj⟩, if_pos hm]
      generalize e / uk k = j at hj
      have t0 := tput_sound cp cn cr 1 (by norm_num) false (2 ^ par.s * a) ha
      have t1 := tput_sound sp sn sr 1 (by norm_num) true (2 ^ par.s * b) hb
      have t2 := tput_sound cp cn cr 2 (by norm_num) true (2 ^ par.s * a) ha
      have t3 := tput_sound sp sn sr 6 (by norm_num) false (2 ^ par.s * b) hb
      have t4 := tput_sound cp cn cr 24 (by norm_num) false (2 ^ par.s * a) ha
      have t5 := tput_sound sp sn sr 120 (by norm_num) true (2 ^ par.s * b) hb
      simp only [Bool.false_eq_true, if_false, if_true, Nat.cast_one, Nat.cast_ofNat] at t0 t1 t2 t3 t4 t5
      interval_cases j
      · have e0 : 2 ^ par.s * Rep.tcoef a b 0 = 2 ^ par.s * a / 1 := by
          unfold Rep.tcoef
          simp
        rw [e0]
        exact t0
      · have e0 : 2 ^ par.s * Rep.tcoef a b 1 = -(2 ^ par.s * b) / 1 := by
          unfold Rep.tcoef
          simp
        rw [e0]
        exact t1
      · have e0 : 2 ^ par.s * Rep.tcoef a b 2 = -(2 ^ par.s * a) / 2 := by
          unfold Rep.tcoef
          simp
          ring
        rw [e0]
        exact t2
      · have e0 : 2 ^ par.s * Rep.tcoef a b 3 = 2 ^ par.s * b / 6 := by
          unfold Rep.tcoef
          simp
          ring
        rw [e0]
        exact t3
      · have e0 : 2 ^ par.s * Rep.tcoef a b 4 = 2 ^ par.s * a / 24 := by
          unfold Rep.tcoef
          simp
          ring
        rw [e0]
        exact t4
      · have e0 : 2 ^ par.s * Rep.tcoef a b 5 = -(2 ^ par.s * b) / 120 := by
          unfold Rep.tcoef
          simp
          ring
        rw [e0]
        exact t5
    · rw [if_neg (fun h => hm h.1), if_neg hm]
      simp

end N14.Jet

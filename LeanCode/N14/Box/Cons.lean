module

public import CAP.Subdivision.BernSound
public import N14.Box.Kernel

/-!
# T7, the slack on a domain: the polynomials of the constraints

The checker forms the coefficients of the constraints from the parameters of a run (`gramPp`, `cutPp`). This
file proves that these numbers are the coefficients of `-2 ^ sg` times the Gram polynomial (`gram_poly`) and of
`-2 ^ sg` times the function of a cut (`cut_poly`), in the sense of `CAP.Bernstein.pEval`.

A polynomial that is given by a number is evaluated through the weighted sum `Phi` of the array of its slots
with the weights `x_a ^ k` (`pEval_Phi`); an array with one entry has the value of one monomial (`Phi_unitF`).
-/

@[expose] public section

namespace N14.Box

open CAP CAP.Bernstein Finset

/-- The weights `x_a ^ k` of the three coordinates. -/
def pw (x1 x2 x3 : ℝ) : ℕ → ℕ → ℝ := fun a k => (if a = 0 then x1 else if a = 1 then x2 else x3) ^ k

/-- The value of a polynomial that is given by a number, through weighted sums. -/
theorem pEval_Phi (P : Params) (Pp : ℕ) (x1 x2 x3 : ℝ) :
    pEval P Pp x1 x2 x3 = Phi (P.n + 1) (pw x1 x2 x3) (slot P.V Pp)
      - Phi (P.n + 1) (pw x1 x2 x3) (fun _ => 2 ^ (P.aH - 1)) := by
  unfold pEval
  rw [Phi_cube, Phi_cube, ← sum_sub_distrib]
  refine sum_congr rfl fun e3 _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun e2 _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun e1 _ => ?_
  unfold coef pw
  push_cast
  ring

/-- The value of a polynomial whose coefficients are the entries of an array, up to the bias. -/
theorem pEval_packSum (P : Params) (g : ℕ → ℕ)
    (hg : ∀ e, e < (P.n + 1) * (P.n + 1) * (P.n + 1) → g e < 2 ^ P.V) (x1 x2 x3 : ℝ) :
    pEval P (packSum P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) g) x1 x2 x3
      = Phi (P.n + 1) (pw x1 x2 x3) g - Phi (P.n + 1) (pw x1 x2 x3) (fun _ => 2 ^ (P.aH - 1)) := by
  rw [pEval_Phi]
  congr 1
  exact Phi_congr _ _ fun e he => slot_packSum P.V _ g hg e he

/-- The array with the entry `c` at the place `(a, b, d)`. -/
def unitF (m a b d c : ℕ) : ℕ → ℕ := fun e => if e = a + m * (b + m * d) then c else 0

theorem idx_lt (m a b d : ℕ) (ha : a < m) (hb : b < m) (hd : d < m) : a + m * (b + m * d) < m * m * m := by
  have h1 : b + m * d ≤ (m - 1) + m * (m - 1) := Nat.add_le_add (by omega) (Nat.mul_le_mul_left _ (by omega))
  have h2 : m * (b + m * d) ≤ m * ((m - 1) + m * (m - 1)) := Nat.mul_le_mul_left _ h1
  have h3 : m * ((m - 1) + m * (m - 1)) + m = m * m * m := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  omega

theorem Phi_unitF (m : ℕ) (ω : ℕ → ℕ → ℝ) (a b d c : ℕ) (ha : a < m) (hb : b < m) (hd : d < m) :
    Phi m ω (unitF m a b d c) = (c : ℝ) * (ω 0 a * ω 1 b * ω 2 d) := by
  unfold Phi
  rw [sum_eq_single (a + m * (b + m * d))]
  · unfold unitF
    rw [if_pos rfl, W3_at m ω a b d ha hb]
  · intro e _ he
    unfold unitF
    rw [if_neg he]
    simp
  · intro h
    exact absurd (mem_range.mpr (idx_lt m a b d ha hb hd)) h

theorem packSum_unitF (V m a b d c : ℕ) (ha : a < m) (hb : b < m) (hd : d < m) :
    packSum V (m * m * m) (unitF m a b d c) = c * 2 ^ (V * (a + m * (b + m * d))) :=
  packSum_single V (m * m * m) _ c (idx_lt m a b d ha hb hd)

theorem unitF_le (m a b d c e : ℕ) : unitF m a b d c e ≤ c := by
  unfold unitF
  split_ifs <;> omega

theorem unit3_eq (R : Run) (e1 e2 e3 : ℕ) :
    unit3 R e1 e2 e3 = 2 ^ (R.V * (e1 + (R.n + 1) * (e2 + (R.n + 1) * e3))) := by
  show 1 <<< (R.V * (e1 + (R.n + 1) * (e2 + (R.n + 1) * e3))) = _
  rw [Nat.one_shiftLeft]

theorem unit3_packSum (R : Run) (e1 e2 e3 : ℕ) (h1 : e1 ≤ R.n) (h2 : e2 ≤ R.n) (h3 : e3 ≤ R.n) :
    unit3 R e1 e2 e3 = packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1)) (unitF (R.n + 1) e1 e2 e3 1) := by
  rw [unit3_eq, packSum_unitF R.V (R.n + 1) e1 e2 e3 1 (by omega) (by omega) (by omega), one_mul]

theorem biasG_packSum (R : Run) (hV : 1 ≤ R.V) :
    biasG R = packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1)) (fun _ => 2 ^ (R.aG - 1)) := by
  show (1 <<< (R.aG - 1)) * ones R.V ((R.n + 1) * (R.n + 1) * (R.n + 1)) = _
  rw [Nat.one_shiftLeft, ones_eq R.V _ hV, ← packSum_const]

/-- The conditions on the parameters that the polynomials of the constraints need. -/
structure ConFit (R : Run) : Prop where
  hV : 1 ≤ R.V
  hn : 2 ≤ R.n
  hsg : R.sg + 2 < R.aG - 1
  haG : R.aG ≤ R.V

theorem ConFit.bias {R : Run} (h : ConFit R) : 4 * 2 ^ R.sg < 2 ^ (R.aG - 1) := by
  calc 4 * 2 ^ R.sg = 2 ^ (R.sg + 2) := by rw [pow_add]; ring
    _ < 2 ^ (R.aG - 1) := Nat.pow_lt_pow_right (by norm_num) h.hsg

theorem ConFit.top {R : Run} (h : ConFit R) : 2 * 2 ^ (R.aG - 1) ≤ 2 ^ R.V := by
  have h1 : R.aG - 1 + 1 ≤ R.V := by have := h.hsg; have := h.haG; omega
  calc 2 * 2 ^ (R.aG - 1) = 2 ^ (R.aG - 1 + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ R.V := Nat.pow_le_pow_right (by norm_num) h1

/-- The Gram polynomial. -/
def gram (x1 x2 x3 : ℝ) : ℝ := 1 + 2 * x1 * x2 * x3 - x1 ^ 2 - x2 ^ 2 - x3 ^ 2

/-- **The polynomial of the Gram inequality.** -/
theorem gram_poly (R : Run) (hf : ConFit R) (A i j k : ℕ) (x1 x2 x3 : ℝ) :
    pEval (boxP R R.aG A i j k) (gramPp R) x1 x2 x3 = -(2 : ℝ) ^ R.sg * gram x1 x2 x3 := by
  have hn := hf.hn
  have hb := hf.bias
  have ht := hf.top
  -- the number as the number of an array
  have e1 : gramPp R = packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1))
      (fun e => (2 ^ (R.aG - 1) + 2 ^ R.sg * (unitF (R.n + 1) 2 0 0 1 e + unitF (R.n + 1) 0 2 0 1 e
          + unitF (R.n + 1) 0 0 2 1 e))
        - 2 ^ R.sg * (unitF (R.n + 1) 0 0 0 1 e + 2 * unitF (R.n + 1) 1 1 1 1 e)) := by
    show (biasG R + (1 <<< R.sg) * (unit3 R 2 0 0 + unit3 R 0 2 0 + unit3 R 0 0 2))
        - (1 <<< R.sg) * (unit3 R 0 0 0 + 2 * unit3 R 1 1 1) = _
    rw [Nat.one_shiftLeft, biasG_packSum R hf.hV, unit3_packSum R 2 0 0 (by omega) (by omega) (by omega),
      unit3_packSum R 0 2 0 (by omega) (by omega) (by omega), unit3_packSum R 0 0 2 (by omega) (by omega) (by omega),
      unit3_packSum R 0 0 0 (by omega) (by omega) (by omega), unit3_packSum R 1 1 1 (by omega) (by omega) (by omega),
      ← packSum_add, ← packSum_add, ← packSum_mul, ← packSum_add, ← packSum_mul, ← packSum_add, ← packSum_mul,
      packSum_sub]
    intro e _
    have a1 := unitF_le (R.n + 1) 0 0 0 1 e
    have a2 := unitF_le (R.n + 1) 1 1 1 1 e
    have a3 : 2 ^ R.sg * (unitF (R.n + 1) 0 0 0 1 e + 2 * unitF (R.n + 1) 1 1 1 1 e) ≤ 2 ^ R.sg * 3 :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hle : ∀ e, e < (R.n + 1) * (R.n + 1) * (R.n + 1) →
      2 ^ R.sg * (unitF (R.n + 1) 0 0 0 1 e + 2 * unitF (R.n + 1) 1 1 1 1 e)
        ≤ 2 ^ (R.aG - 1) + 2 ^ R.sg * (unitF (R.n + 1) 2 0 0 1 e + unitF (R.n + 1) 0 2 0 1 e
          + unitF (R.n + 1) 0 0 2 1 e) := by
    intro e _
    have a1 := unitF_le (R.n + 1) 0 0 0 1 e
    have a2 := unitF_le (R.n + 1) 1 1 1 1 e
    have a3 : 2 ^ R.sg * (unitF (R.n + 1) 0 0 0 1 e + 2 * unitF (R.n + 1) 1 1 1 1 e) ≤ 2 ^ R.sg * 3 :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hlt : ∀ e, e < (R.n + 1) * (R.n + 1) * (R.n + 1) →
      (2 ^ (R.aG - 1) + 2 ^ R.sg * (unitF (R.n + 1) 2 0 0 1 e + unitF (R.n + 1) 0 2 0 1 e
          + unitF (R.n + 1) 0 0 2 1 e))
        - 2 ^ R.sg * (unitF (R.n + 1) 0 0 0 1 e + 2 * unitF (R.n + 1) 1 1 1 1 e) < 2 ^ R.V := by
    intro e _
    have a1 := unitF_le (R.n + 1) 2 0 0 1 e
    have a2 := unitF_le (R.n + 1) 0 2 0 1 e
    have a3 := unitF_le (R.n + 1) 0 0 2 1 e
    have a4 : 2 ^ R.sg * (unitF (R.n + 1) 2 0 0 1 e + unitF (R.n + 1) 0 2 0 1 e + unitF (R.n + 1) 0 0 2 1 e)
        ≤ 2 ^ R.sg * 3 := Nat.mul_le_mul_left _ (by omega)
    omega
  rw [e1]
  have hP : pEval (boxP R R.aG A i j k) (packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1)) _) x1 x2 x3 = _ :=
    pEval_packSum (boxP R R.aG A i j k) _ hlt x1 x2 x3
  rw [hP]
  show Phi (R.n + 1) (pw x1 x2 x3) _ - Phi (R.n + 1) (pw x1 x2 x3) (fun _ => 2 ^ (R.aG - 1)) = _
  rw [Phi_sub _ _ hle, Phi_add, Phi_smul, Phi_add, Phi_add, Phi_smul, Phi_add, Phi_smul,
    Phi_unitF _ _ 2 0 0 1 (by omega) (by omega) (by omega), Phi_unitF _ _ 0 2 0 1 (by omega) (by omega) (by omega),
    Phi_unitF _ _ 0 0 2 1 (by omega) (by omega) (by omega), Phi_unitF _ _ 0 0 0 1 (by omega) (by omega) (by omega),
    Phi_unitF _ _ 1 1 1 1 (by omega) (by omega) (by omega)]
  unfold gram pw
  push_cast
  simp
  ring

/-- The coordinate `a` of a point: the first one for `a = 0`, the second one for `a = 1`, the third one
otherwise. -/
def co (a : ℕ) (x1 x2 x3 : ℝ) : ℝ := if a = 0 then x1 else if a = 1 then x2 else x3

/-- The function `g` of the cut `g ≥ 0`. -/
noncomputable def cutVal (c : Cut) (x1 x2 x3 : ℝ) : ℝ :=
  if c.kind = 0 then co c.a x1 x2 x3 + 1 - (c.vn : ℝ) / c.vd
  else if c.kind = 1 then (c.vn : ℝ) / c.vd - co c.a x1 x2 x3 - 1
  else co c.a x1 x2 x3 - co c.b x1 x2 x3

/-- The unit of the exponent `1` of the coordinate `a` is the number of an array with one entry, whose value
is the coordinate. -/
theorem unitA_rep (R : Run) (hn : 2 ≤ R.n) (a : ℕ) :
    ∃ g : ℕ → ℕ, unitA R a 1 = packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1)) g ∧ (∀ e, g e ≤ 1) ∧
      ∀ x1 x2 x3 : ℝ, Phi (R.n + 1) (pw x1 x2 x3) g = co a x1 x2 x3 := by
  rcases a with _ | _ | a
  · refine ⟨unitF (R.n + 1) 1 0 0 1, unit3_packSum R 1 0 0 (by omega) (by omega) (by omega),
      fun e => unitF_le _ _ _ _ _ e, fun x1 x2 x3 => ?_⟩
    rw [Phi_unitF _ _ 1 0 0 1 (by omega) (by omega) (by omega)]
    simp [pw, co]
  · refine ⟨unitF (R.n + 1) 0 1 0 1, unit3_packSum R 0 1 0 (by omega) (by omega) (by omega),
      fun e => unitF_le _ _ _ _ _ e, fun x1 x2 x3 => ?_⟩
    rw [Phi_unitF _ _ 0 1 0 1 (by omega) (by omega) (by omega)]
    simp [pw, co]
  · refine ⟨unitF (R.n + 1) 0 0 1 1, unit3_packSum R 0 0 1 (by omega) (by omega) (by omega),
      fun e => unitF_le _ _ _ _ _ e, fun x1 x2 x3 => ?_⟩
    rw [Phi_unitF _ _ 0 0 1 1 (by omega) (by omega) (by omega)]
    simp [pw, co]

/-- The value of a polynomial whose coefficients are `bias + p e - q e`. -/
theorem pEval_diff (R : Run) (hf : ConFit R) (A i j k : ℕ) (p q : ℕ → ℕ) (Pp : ℕ)
    (hPp : Pp = packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1)) (fun e => 2 ^ (R.aG - 1) + p e)
      - packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1)) q)
    (hp : ∀ e, p e ≤ 2 * 2 ^ R.sg) (hq : ∀ e, q e ≤ 2 * 2 ^ R.sg) (x1 x2 x3 : ℝ) :
    pEval (boxP R R.aG A i j k) Pp x1 x2 x3
      = Phi (R.n + 1) (pw x1 x2 x3) p - Phi (R.n + 1) (pw x1 x2 x3) q := by
  have hb := hf.bias
  have ht := hf.top
  have hle : ∀ e, e < (R.n + 1) * (R.n + 1) * (R.n + 1) → q e ≤ 2 ^ (R.aG - 1) + p e := by
    intro e _
    have := hq e
    omega
  have hlt : ∀ e, e < (R.n + 1) * (R.n + 1) * (R.n + 1) → 2 ^ (R.aG - 1) + p e - q e < 2 ^ R.V := by
    intro e _
    have := hp e
    omega
  rw [hPp, packSum_sub _ _ _ _ hle]
  have hP : pEval (boxP R R.aG A i j k) (packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1)) _) x1 x2 x3 = _ :=
    pEval_packSum (boxP R R.aG A i j k) _ hlt x1 x2 x3
  rw [hP]
  show Phi (R.n + 1) (pw x1 x2 x3) _ - Phi (R.n + 1) (pw x1 x2 x3) (fun _ => 2 ^ (R.aG - 1)) = _
  rw [Phi_sub _ _ hle, Phi_add]
  ring

/-- **The polynomial of a cut.** -/
theorem cut_poly (R : Run) (hf : ConFit R) (c : Cut) (hc : cutFits R c = true) (A i j k : ℕ) (x1 x2 x3 : ℝ) :
    pEval (boxP R R.aG A i j k) (cutPp R c) x1 x2 x3 = -(2 : ℝ) ^ R.sg * cutVal c x1 x2 x3 := by
  have hn := hf.hn
  have hc' : (Nat.ble 1 c.vd
      && Nat.beq ((c.vn * (1 <<< R.sg)) / c.vd * c.vd) (c.vn * (1 <<< R.sg))
      && Nat.ble c.vn (2 * c.vd)) = true := hc
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq, Nat.one_shiftLeft] at hc'
  obtain ⟨⟨hvd, hdiv⟩, hvn⟩ := hc'
  have hdiv' : c.vn * 2 ^ R.sg / c.vd * c.vd = c.vn * 2 ^ R.sg := Nat.eq_of_beq_eq_true hdiv
  -- the value `vn * 2 ^ sg / vd`
  have hv : c.vn * 2 ^ R.sg / c.vd ≤ 2 * 2 ^ R.sg := by
    apply Nat.div_le_of_le_mul
    calc c.vn * 2 ^ R.sg ≤ 2 * c.vd * 2 ^ R.sg := Nat.mul_le_mul_right _ hvn
      _ = c.vd * (2 * 2 ^ R.sg) := by ring
  have hvR : ((c.vn * 2 ^ R.sg / c.vd : ℕ) : ℝ) = (2 : ℝ) ^ R.sg * ((c.vn : ℝ) / c.vd) := by
    have hd0 : (c.vd : ℝ) ≠ 0 := by
      have : 0 < c.vd := hvd
      positivity
    have h := congrArg (fun z : ℕ => (z : ℝ)) hdiv'
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
    have h2 : ((c.vn * 2 ^ R.sg / c.vd : ℕ) : ℝ) = (c.vn : ℝ) * 2 ^ R.sg / c.vd := by
      rw [eq_div_iff hd0]
      exact h
    rw [h2]
    ring
  obtain ⟨ga, ha1, ha2, ha3⟩ := unitA_rep R hn c.a
  obtain ⟨gb, hb1, hb2, hb3⟩ := unitA_rep R hn c.b
  have h0 := unit3_packSum R 0 0 0 (by omega) (by omega) (by omega)
  have hΦ0 : Phi (R.n + 1) (pw x1 x2 x3) (unitF (R.n + 1) 0 0 0 1) = 1 := by
    rw [Phi_unitF _ _ 0 0 0 1 (by omega) (by omega) (by omega)]
    simp [pw]
  have hu0 := unitF_le (R.n + 1) 0 0 0 1
  have hS : 0 < 2 ^ R.sg := Nat.two_pow_pos _
  rcases hk : c.kind with _ | _ | kk
  · -- `x_a + 1 ≥ vn / vd`
    have e1 : cutPp R c = packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1))
          (fun e => 2 ^ (R.aG - 1) + c.vn * 2 ^ R.sg / c.vd * unitF (R.n + 1) 0 0 0 1 e)
        - packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1))
          (fun e => 2 ^ R.sg * (unitF (R.n + 1) 0 0 0 1 e + ga e)) := by
      unfold cutPp
      rw [hk]
      show (biasG R + (c.vn * (1 <<< R.sg)) / c.vd * unit3 R 0 0 0)
          - (1 <<< R.sg) * (unit3 R 0 0 0 + unitA R c.a 1) = _
      rw [Nat.one_shiftLeft, biasG_packSum R hf.hV, h0, ha1, ← packSum_mul, ← packSum_add, ← packSum_add,
        ← packSum_mul]
    rw [pEval_diff R hf A i j k _ _ _ e1
      (fun e => by have := hu0 e; nlinarith) (fun e => by have := hu0 e; have := ha2 e; nlinarith),
      Phi_smul, Phi_smul, Phi_add, hΦ0, ha3, hvR]
    unfold cutVal
    rw [if_pos hk]
    push_cast
    ring
  · -- `x_a + 1 ≤ vn / vd`
    have e1 : cutPp R c = packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1))
          (fun e => 2 ^ (R.aG - 1) + 2 ^ R.sg * (unitF (R.n + 1) 0 0 0 1 e + ga e))
        - packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1))
          (fun e => c.vn * 2 ^ R.sg / c.vd * unitF (R.n + 1) 0 0 0 1 e) := by
      unfold cutPp
      rw [hk]
      show (biasG R + (1 <<< R.sg) * (unit3 R 0 0 0 + unitA R c.a 1))
          - (c.vn * (1 <<< R.sg)) / c.vd * unit3 R 0 0 0 = _
      rw [Nat.one_shiftLeft, biasG_packSum R hf.hV, h0, ha1, ← packSum_add, ← packSum_mul, ← packSum_add,
        ← packSum_mul]
    rw [pEval_diff R hf A i j k _ _ _ e1
      (fun e => by have := hu0 e; have := ha2 e; nlinarith) (fun e => by have := hu0 e; nlinarith),
      Phi_smul, Phi_smul, Phi_add, hΦ0, ha3, hvR]
    unfold cutVal
    rw [if_neg (by omega), if_pos hk]
    push_cast
    ring
  · -- `x_a ≥ x_b`
    have e1 : cutPp R c = packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1))
          (fun e => 2 ^ (R.aG - 1) + 2 ^ R.sg * gb e)
        - packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1)) (fun e => 2 ^ R.sg * ga e) := by
      unfold cutPp
      rw [hk]
      show (biasG R + (1 <<< R.sg) * unitA R c.b 1) - (1 <<< R.sg) * unitA R c.a 1 = _
      rw [Nat.one_shiftLeft, biasG_packSum R hf.hV, ha1, hb1, ← packSum_mul, ← packSum_add, ← packSum_mul]
    rw [pEval_diff R hf A i j k _ _ _ e1
      (fun e => by have := hb2 e; nlinarith) (fun e => by have := ha2 e; nlinarith),
      Phi_smul, Phi_smul, ha3, hb3]
    unfold cutVal
    rw [if_neg (by omega), if_neg (by omega)]
    push_cast
    ring

end N14.Box

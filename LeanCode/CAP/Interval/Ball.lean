module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import CAP.Interval.Kernel

/-!
# E6, interval arithmetic: the operations on balls

A real number `x` lies in the ball `(b, r)` for the precision `p` and the bias `B` if
`|x * 2 ^ p - (b - B)| ≤ r` (`Enc`). For each operation of `CAP/Interval/Kernel.lean` we prove:
if the arguments lie in their balls and the flag of the operation holds, then the result lies in
the ball that the operation returns. No statement requires a bound on the midpoints, and none
uses that the bias is a power of two.
-/

@[expose] public section

namespace CAP.Interval

/-- The real number `x` lies in the ball `(b, r)`. -/
def Enc (p B b r : ℕ) (x : ℝ) : Prop := |x * 2 ^ p - ((b : ℝ) - B)| ≤ r

/-! ## Elementary facts -/

theorem abs_add_le' (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  rw [abs_le]
  constructor <;> linarith [neg_abs_le a, le_abs_self a, neg_abs_le b, le_abs_self b]

theorem abs_mul_le_of {a b A C : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ C) : |a * b| ≤ A * C := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) (le_trans (abs_nonneg a) ha)

/-- The quotient of natural numbers and the real quotient. -/
theorem floor_div_bounds (a s : ℕ) (hs : 0 < s) :
    ((a / s : ℕ) : ℝ) * s ≤ a ∧ (a : ℝ) < (((a / s : ℕ) : ℝ) + 1) * s := by
  have h1 := Nat.div_add_mod a s
  have h2 := Nat.mod_lt a hs
  have h3 : s * (a / s) = a / s * s := Nat.mul_comm _ _
  constructor
  · have h : a / s * s ≤ a := by omega
    exact_mod_cast h
  · have h : a < (a / s + 1) * s := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    exact_mod_cast h

theorem div_lt_floor_add_one (a s : ℕ) (hs : 0 < s) : (a : ℝ) / s < ((a / s : ℕ) : ℝ) + 1 := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  rw [div_lt_iff₀ hs']
  exact (floor_div_bounds a s hs).2

/-- The midpoint is the difference of its positive and its negative part. -/
theorem cast_parts (B b : ℕ) : ((b - B : ℕ) : ℝ) - ((B - b : ℕ) : ℝ) = (b : ℝ) - B := by
  rcases le_total B b with h | h
  · rw [Nat.cast_sub h, Nat.sub_eq_zero_of_le h, Nat.cast_zero, sub_zero]
  · rw [Nat.cast_sub h, Nat.sub_eq_zero_of_le h, Nat.cast_zero, zero_sub, neg_sub]

theorem two_pow_pos' (p : ℕ) : (0 : ℝ) < 2 ^ p := by positivity

theorem abs_parts_le (a b : ℕ) : |(a : ℝ) - b| ≤ (a : ℝ) + b := by
  rw [abs_le]
  constructor <;> linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a), (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]

theorem abs_cast_sub (B b : ℕ) : |(b : ℝ) - B| = ((b - B : ℕ) : ℝ) + ((B - b : ℕ) : ℝ) := by
  rcases le_total B b with h | h
  · rw [Nat.cast_sub h, Nat.sub_eq_zero_of_le h, Nat.cast_zero, add_zero, abs_of_nonneg]
    exact sub_nonneg.mpr (by exact_mod_cast h)
  · rw [Nat.cast_sub h, Nat.sub_eq_zero_of_le h, Nat.cast_zero, zero_add, abs_sub_comm, abs_of_nonneg]
    exact sub_nonneg.mpr (by exact_mod_cast h)

theorem withFlag_ok {x : ℕ × ℕ × Bool} {g : Bool} (h : (withFlag x g).2.2 = true) :
    x.2.2 = true ∧ g = true := by
  have h' : (x.2.2 && g) = true := h
  rwa [Bool.and_eq_true] at h'

/-! ## Constants -/

theorem nat_sound (p B n : ℕ) : Enc p B (B + n * 2 ^ p) 0 (n : ℝ) := by
  unfold Enc
  push_cast
  rw [show (n : ℝ) * 2 ^ p - ((B : ℝ) + n * 2 ^ p - B) = 0 by ring]
  simp

theorem cst_sound (p B b : ℕ) : Enc p B b 0 (((b : ℝ) - B) / 2 ^ p) := by
  unfold Enc
  rw [div_mul_cancel₀ _ (two_pow_pos' p).ne', sub_self]
  simp

/-! ## Sum and difference -/

theorem addB_sound {p B b1 r1 b2 r2 : ℕ} {x y : ℝ} (hx : Enc p B b1 r1 x) (hy : Enc p B b2 r2 y)
    (hok : (addB B b1 r1 b2 r2).2.2 = true) :
    Enc p B (addB B b1 r1 b2 r2).1 (addB B b1 r1 b2 r2).2.1 (x + y) := by
  have hle : B ≤ b1 + b2 := Nat.le_of_ble_eq_true hok
  show |(x + y) * 2 ^ p - (((b1 + b2 - B : ℕ) : ℝ) - B)| ≤ ((r1 + r2 : ℕ) : ℝ)
  unfold Enc at hx hy
  rw [abs_le] at hx hy ⊢
  rw [Nat.cast_sub hle]
  push_cast
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem subB_sound {p B b1 r1 b2 r2 : ℕ} {x y : ℝ} (hx : Enc p B b1 r1 x) (hy : Enc p B b2 r2 y)
    (hok : (subB B b1 r1 b2 r2).2.2 = true) :
    Enc p B (subB B b1 r1 b2 r2).1 (subB B b1 r1 b2 r2).2.1 (x - y) := by
  have hle : b2 ≤ b1 + B := Nat.le_of_ble_eq_true hok
  show |(x - y) * 2 ^ p - (((b1 + B - b2 : ℕ) : ℝ) - B)| ≤ ((r1 + r2 : ℕ) : ℝ)
  unfold Enc at hx hy
  rw [abs_le] at hx hy ⊢
  rw [Nat.cast_sub hle]
  push_cast
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-! ## Product -/

theorem mulB_eq (p B b1 r1 b2 r2 : ℕ) : mulB p B b1 r1 b2 r2 =
    (B + ((b1 - B) * (b2 - B) + (B - b1) * (B - b2)) / 2 ^ p
        - ((b1 - B) * (B - b2) + (B - b1) * (b2 - B)) / 2 ^ p,
      (((b1 - B) + (B - b1)) * r2 + ((b2 - B) + (B - b2)) * r1 + r1 * r2) / 2 ^ p + 2,
      Nat.ble (((b1 - B) * (B - b2) + (B - b1) * (b2 - B)) / 2 ^ p)
        (B + ((b1 - B) * (b2 - B) + (B - b1) * (B - b2)) / 2 ^ p)) := by
  simp only [← Nat.shiftRight_eq_div_pow]
  rfl

theorem mulB_sound {p B b1 r1 b2 r2 : ℕ} {x y : ℝ} (hx : Enc p B b1 r1 x) (hy : Enc p B b2 r2 y)
    (hok : (mulB p B b1 r1 b2 r2).2.2 = true) :
    Enc p B (mulB p B b1 r1 b2 r2).1 (mulB p B b1 r1 b2 r2).2.1 (x * y) := by
  rw [mulB_eq] at hok ⊢
  have hle := Nat.le_of_ble_eq_true hok
  have hs : (0 : ℝ) < 2 ^ p := two_pow_pos' p
  have hsn : 0 < 2 ^ p := Nat.two_pow_pos p
  have e1 := cast_parts B b1
  have e2 := cast_parts B b2
  unfold Enc at hx hy
  rw [← e1] at hx
  rw [← e2] at hy
  obtain ⟨fp1, fp2⟩ := floor_div_bounds ((b1 - B) * (b2 - B) + (B - b1) * (B - b2)) (2 ^ p) hsn
  obtain ⟨fn1, fn2⟩ := floor_div_bounds ((b1 - B) * (B - b2) + (B - b1) * (b2 - B)) (2 ^ p) hsn
  obtain ⟨fr1, fr2⟩ := floor_div_bounds
    (((b1 - B) + (B - b1)) * r2 + ((b2 - B) + (B - b2)) * r1 + r1 * r2) (2 ^ p) hsn
  show |x * y * 2 ^ p - (((B + ((b1 - B) * (b2 - B) + (B - b1) * (B - b2)) / 2 ^ p
      - ((b1 - B) * (B - b2) + (B - b1) * (b2 - B)) / 2 ^ p : ℕ) : ℝ) - B)|
    ≤ (((((b1 - B) + (B - b1)) * r2 + ((b2 - B) + (B - b2)) * r1 + r1 * r2) / 2 ^ p + 2 : ℕ) : ℝ)
  rw [Nat.cast_sub hle]
  generalize ((b1 - B) * (b2 - B) + (B - b1) * (B - b2)) / 2 ^ p = fp at *
  generalize ((b1 - B) * (B - b2) + (B - b1) * (b2 - B)) / 2 ^ p = fn at *
  generalize (((b1 - B) + (B - b1)) * r2 + ((b2 - B) + (B - b2)) * r1 + r1 * r2) / 2 ^ p = fr at *
  generalize b1 - B = p1 at *
  generalize B - b1 = n1 at *
  generalize b2 - B = p2 at *
  generalize B - b2 = n2 at *
  push_cast at fp1 fp2 fn1 fn2 fr1 fr2 ⊢
  have key : |x * 2 ^ p * (y * 2 ^ p) - ((p1 : ℝ) - n1) * ((p2 : ℝ) - n2)|
      ≤ ((p1 : ℝ) + n1) * r2 + ((p2 : ℝ) + n2) * r1 + r1 * r2 := by
    have e : x * 2 ^ p * (y * 2 ^ p) - ((p1 : ℝ) - n1) * ((p2 : ℝ) - n2)
        = ((p1 : ℝ) - n1) * (y * 2 ^ p - ((p2 : ℝ) - n2))
          + ((p2 : ℝ) - n2) * (x * 2 ^ p - ((p1 : ℝ) - n1))
          + (x * 2 ^ p - ((p1 : ℝ) - n1)) * (y * 2 ^ p - ((p2 : ℝ) - n2)) := by ring
    rw [e]
    refine (abs_add_le' _ _).trans (add_le_add ((abs_add_le' _ _).trans (add_le_add ?_ ?_)) ?_)
    · exact abs_mul_le_of (abs_parts_le p1 n1) hy
    · exact abs_mul_le_of (abs_parts_le p2 n2) hx
    · exact abs_mul_le_of hx hy
  rw [abs_le] at key ⊢
  constructor
  · refine le_of_mul_le_mul_right ?_ hs
    linarith [key.1, fr2, fp1, fn2]
  · refine le_of_mul_le_mul_right ?_ hs
    linarith [key.2, fr2, fp2, fn1]

/-! ## Reciprocal -/

theorem invB_eq (p B b r : ℕ) : invB p B b r =
    (B + 2 ^ (2 * p) / (b - B) - 2 ^ (2 * p) / (B - b),
      2 ^ (2 * p) * r / (((b - B) + (B - b) - r) * ((b - B) + (B - b))) + 2,
      Nat.blt r ((b - B) + (B - b)) && Nat.ble (2 ^ (2 * p) / (B - b)) (B + 2 ^ (2 * p) / (b - B))) := by
  simp only [← Nat.one_shiftLeft]
  rfl

/-- The reciprocal of a positive number near the natural number `a`. -/
theorem inv_core (p a r : ℕ) (X : ℝ) (hr : r < a) (hX : |X - a| ≤ r) :
    |(2 : ℝ) ^ p * 2 ^ p / X - ((2 ^ (2 * p) / a : ℕ) : ℝ)|
      ≤ ((2 ^ (2 * p) * r / ((a - r) * a) : ℕ) : ℝ) + 2 := by
  have ha : 0 < a := by omega
  have har : 0 < a - r := by omega
  have hD : 0 < (a - r) * a := Nat.mul_pos har ha
  obtain ⟨q1, q2⟩ := floor_div_bounds (2 ^ (2 * p)) a ha
  have f2 := div_lt_floor_add_one (2 ^ (2 * p) * r) ((a - r) * a) hD
  generalize 2 ^ (2 * p) / a = q at *
  generalize 2 ^ (2 * p) * r / ((a - r) * a) = fr at *
  push_cast [Nat.cast_sub hr.le] at q1 q2 f2
  have hS : ((2 : ℝ) ^ (2 * p)) = 2 ^ p * 2 ^ p := by rw [two_mul, pow_add]
  rw [hS] at q1 q2 f2
  have hs0 : (0 : ℝ) < 2 ^ p * 2 ^ p := by positivity
  generalize (2 : ℝ) ^ p * 2 ^ p = s at *
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hrR : (r : ℝ) < a := by exact_mod_cast hr
  have harR : (0 : ℝ) < (a : ℝ) - r := by linarith
  rw [abs_le] at hX
  have hXlo : (a : ℝ) - r ≤ X := by linarith [hX.1]
  have hXpos : 0 < X := lt_of_lt_of_le harR hXlo
  have h1 : |s / X - s / a| ≤ s * r / (((a : ℝ) - r) * a) := by
    have e : s / X - s / a = s * (a - X) / (X * a) := by
      field_simp
    have hnum : |(a : ℝ) - X| ≤ r := by
      rw [abs_le]
      constructor <;> linarith [hX.1, hX.2]
    rw [e, abs_div, abs_mul, abs_of_pos hs0, abs_of_pos (mul_pos hXpos haR),
      div_le_iff₀ (mul_pos hXpos haR),
      show s * r / (((a : ℝ) - r) * a) * (X * a) = s * r * (X * a) / (((a : ℝ) - r) * a) by ring,
      le_div_iff₀ (mul_pos harR haR)]
    have h2 : |(a : ℝ) - X| * ((a : ℝ) - r) ≤ r * X :=
      calc |(a : ℝ) - X| * ((a : ℝ) - r) ≤ r * ((a : ℝ) - r) := mul_le_mul_of_nonneg_right hnum harR.le
        _ ≤ r * X := mul_le_mul_of_nonneg_left hXlo (Nat.cast_nonneg r)
    have h3 := mul_le_mul_of_nonneg_left h2 (mul_pos hs0 haR).le
    linarith [h3]
  have h2 : |s / a - q| ≤ 1 := by
    rw [abs_le]
    constructor
    · have : (q : ℝ) ≤ s / a := by
        rw [le_div_iff₀ haR]
        exact q1
      linarith
    · have : s / a < (q : ℝ) + 1 := by
        rw [div_lt_iff₀ haR]
        exact q2
      linarith
  have e : s / X - q = (s / X - s / a) + (s / a - q) := by ring
  rw [e]
  calc |s / X - s / a + (s / a - q)| ≤ |s / X - s / a| + |s / a - q| := abs_add_le' _ _
    _ ≤ s * r / (((a : ℝ) - r) * a) + 1 := add_le_add h1 h2
    _ ≤ fr + 2 := by linarith [f2]

theorem invB_sound {p B b r : ℕ} {x : ℝ} (hx : Enc p B b r x) (hok : (invB p B b r).2.2 = true) :
    Enc p B (invB p B b r).1 (invB p B b r).2.1 x⁻¹ := by
  rw [invB_eq] at hok ⊢
  rw [Bool.and_eq_true] at hok
  have hlt : r < (b - B) + (B - b) := by
    have := hok.1
    rwa [Nat.blt_eq] at this
  have hle := Nat.le_of_ble_eq_true hok.2
  have hs : (0 : ℝ) < 2 ^ p := two_pow_pos' p
  unfold Enc at hx
  show |x⁻¹ * 2 ^ p - (((B + 2 ^ (2 * p) / (b - B) - 2 ^ (2 * p) / (B - b) : ℕ) : ℝ) - B)|
    ≤ ((2 ^ (2 * p) * r / (((b - B) + (B - b) - r) * ((b - B) + (B - b))) + 2 : ℕ) : ℝ)
  rw [Nat.cast_sub hle]
  rcases le_total B b with h | h
  · -- positive midpoint
    have hz : B - b = 0 := Nat.sub_eq_zero_of_le h
    rw [hz, Nat.add_zero] at hlt ⊢
    rw [Nat.div_zero]
    have hX : |x * 2 ^ p - ((b - B : ℕ) : ℝ)| ≤ r := by
      rw [Nat.cast_sub h]
      exact hx
    have core := inv_core p (b - B) r (x * 2 ^ p) hlt hX
    have hxne : x ≠ 0 := by
      rintro rfl
      rw [zero_mul, zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)] at hX
      have : (b - B : ℕ) ≤ r := by exact_mod_cast hX
      omega
    have e : x⁻¹ * 2 ^ p = 2 ^ p * 2 ^ p / (x * 2 ^ p) := by
      field_simp
    rw [e]
    push_cast at core ⊢
    rw [show (B : ℝ) + ((2 ^ (2 * p) / (b - B) : ℕ) : ℝ) - 0 - B = ((2 ^ (2 * p) / (b - B) : ℕ) : ℝ) by ring]
    exact core
  · -- negative midpoint
    have hz : b - B = 0 := Nat.sub_eq_zero_of_le h
    rw [hz, Nat.zero_add] at hlt ⊢
    rw [Nat.div_zero]
    have hX : |-(x * 2 ^ p) - ((B - b : ℕ) : ℝ)| ≤ r := by
      rw [Nat.cast_sub h, show -(x * 2 ^ p) - ((B : ℝ) - b) = -(x * 2 ^ p - ((b : ℝ) - B)) by ring, abs_neg]
      exact hx
    have core := inv_core p (B - b) r (-(x * 2 ^ p)) hlt hX
    have hxne : x ≠ 0 := by
      rintro rfl
      rw [zero_mul, neg_zero, zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)] at hX
      have : (B - b : ℕ) ≤ r := by exact_mod_cast hX
      omega
    have e : x⁻¹ * 2 ^ p = -(2 ^ p * 2 ^ p / (-(x * 2 ^ p))) := by
      field_simp
    rw [e]
    push_cast at core ⊢
    rw [show -(2 ^ p * 2 ^ p / -(x * 2 ^ p)) - ((B : ℝ) + 0 - ((2 ^ (2 * p) / (B - b) : ℕ) : ℝ) - B)
        = -(2 ^ p * 2 ^ p / -(x * 2 ^ p) - ((2 ^ (2 * p) / (B - b) : ℕ) : ℝ)) by ring, abs_neg]
    exact core

/-! ## Square root -/

theorem sqrtB_eq (p B b r t : ℕ) : sqrtB p B b r t =
    (B + t, r * 2 ^ p / t + 2,
      Nat.blt r (b - B) && Nat.ble (t * t) ((b - B) * 2 ^ p) && Nat.blt ((b - B) * 2 ^ p) ((t + 1) * (t + 1))) := by
  simp only [← Nat.shiftLeft_eq]
  rfl

/-- The square root of a positive number near the natural number `a`, with the witness `t`. -/
theorem sqrt_core (p a r t : ℕ) (X : ℝ) (hr : r < a) (hX : |X - a| ≤ r)
    (ht1 : t * t ≤ a * 2 ^ p) (ht2 : a * 2 ^ p < (t + 1) * (t + 1)) :
    |Real.sqrt (X * 2 ^ p) - t| ≤ ((r * 2 ^ p / t : ℕ) : ℝ) + 2 := by
  have ha : 0 < a := by omega
  have hN : 0 < a * 2 ^ p := Nat.mul_pos ha (Nat.two_pow_pos p)
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h
      omega
    · exact h
  have f2 := div_lt_floor_add_one (r * 2 ^ p) t ht
  generalize r * 2 ^ p / t = fr at *
  push_cast at f2
  have hs : (0 : ℝ) < 2 ^ p := two_pow_pos' p
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hrR : (r : ℝ) < a := by exact_mod_cast hr
  have hN1 : (t : ℝ) * t ≤ a * 2 ^ p := by exact_mod_cast ht1
  have hN2 : (a : ℝ) * 2 ^ p < ((t : ℝ) + 1) * (t + 1) := by exact_mod_cast ht2
  rw [abs_le] at hX
  have hXpos : 0 < X := by linarith [hX.1]
  have hNpos : (0 : ℝ) < a * 2 ^ p := by positivity
  have hApos : 0 < X * 2 ^ p := by positivity
  have hAN : |X * 2 ^ p - a * 2 ^ p| ≤ r * 2 ^ p := by
    rw [show X * 2 ^ p - a * 2 ^ p = (X - a) * 2 ^ p by ring, abs_mul, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_right (abs_le.mpr hX) hs.le
  generalize (a : ℝ) * 2 ^ p = N at *
  generalize X * 2 ^ p = A at *
  have hsq1 : (t : ℝ) ≤ Real.sqrt N := by
    have h := Real.sqrt_le_sqrt hN1
    rwa [Real.sqrt_mul_self htR.le] at h
  have hsq2 : Real.sqrt N < t + 1 := by
    have h := Real.sqrt_lt_sqrt hNpos.le hN2
    rwa [Real.sqrt_mul_self (by linarith)] at h
  have hd : |Real.sqrt A - Real.sqrt N| * Real.sqrt N ≤ |A - N| := by
    have e : A - N = (Real.sqrt A - Real.sqrt N) * (Real.sqrt A + Real.sqrt N) := by
      have h1 := Real.mul_self_sqrt hApos.le
      have h2 := Real.mul_self_sqrt hNpos.le
      have h3 : (Real.sqrt A - Real.sqrt N) * (Real.sqrt A + Real.sqrt N)
          = Real.sqrt A * Real.sqrt A - Real.sqrt N * Real.sqrt N := by ring
      rw [h3, h1, h2]
    have h3 : Real.sqrt N ≤ |Real.sqrt A + Real.sqrt N| := by
      rw [abs_of_nonneg (add_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg N))]
      linarith [Real.sqrt_nonneg A]
    rw [e, abs_mul]
    exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  have h1 : |Real.sqrt A - Real.sqrt N| ≤ r * 2 ^ p / t := by
    rw [le_div_iff₀ htR]
    calc |Real.sqrt A - Real.sqrt N| * t ≤ |Real.sqrt A - Real.sqrt N| * Real.sqrt N :=
          mul_le_mul_of_nonneg_left hsq1 (abs_nonneg _)
      _ ≤ |A - N| := hd
      _ ≤ r * 2 ^ p := hAN
  have h2 : |Real.sqrt N - t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have e : Real.sqrt A - t = (Real.sqrt A - Real.sqrt N) + (Real.sqrt N - t) := by ring
  rw [e]
  calc |Real.sqrt A - Real.sqrt N + (Real.sqrt N - t)|
      ≤ |Real.sqrt A - Real.sqrt N| + |Real.sqrt N - t| := abs_add_le' _ _
    _ ≤ r * 2 ^ p / t + 1 := add_le_add h1 h2
    _ ≤ fr + 2 := by linarith [f2]

theorem sqrtB_sound {p B b r t : ℕ} {x : ℝ} (hx : Enc p B b r x) (hok : (sqrtB p B b r t).2.2 = true) :
    Enc p B (sqrtB p B b r t).1 (sqrtB p B b r t).2.1 (Real.sqrt x) := by
  rw [sqrtB_eq] at hok ⊢
  rw [Bool.and_eq_true, Bool.and_eq_true] at hok
  have hlt : r < b - B := by
    have := hok.1.1
    rwa [Nat.blt_eq] at this
  have ht1 := Nat.le_of_ble_eq_true hok.1.2
  have ht2 : (b - B) * 2 ^ p < (t + 1) * (t + 1) := by
    have := hok.2
    rwa [Nat.blt_eq] at this
  have hs : (0 : ℝ) < 2 ^ p := two_pow_pos' p
  have hB : B ≤ b := by omega
  unfold Enc at hx
  have hX : |x * 2 ^ p - ((b - B : ℕ) : ℝ)| ≤ r := by
    rw [Nat.cast_sub hB]
    exact hx
  have core := sqrt_core p (b - B) r t (x * 2 ^ p) hlt hX ht1 ht2
  have hx0 : 0 ≤ x := by
    rw [abs_le] at hX
    have h1 : (r : ℝ) < ((b - B : ℕ) : ℝ) := by exact_mod_cast hlt
    have h2 : 0 < x * 2 ^ p := by linarith [hX.1]
    exact le_of_lt (pos_of_mul_pos_left h2 hs.le)
  have e : Real.sqrt x * 2 ^ p = Real.sqrt (x * 2 ^ p * 2 ^ p) := by
    rw [mul_assoc, Real.sqrt_mul hx0, Real.sqrt_mul_self hs.le]
  show |Real.sqrt x * 2 ^ p - (((B + t : ℕ) : ℝ) - B)| ≤ ((r * 2 ^ p / t + 2 : ℕ) : ℝ)
  rw [e]
  push_cast at core ⊢
  rw [show (B : ℝ) + t - B = t by ring]
  exact core

/-! ## Facts about the arguments of an accepted reciprocal and of an accepted square root -/

theorem invB_ne_zero {p B b r : ℕ} {x : ℝ} (hx : Enc p B b r x) (hok : (invB p B b r).2.2 = true) :
    x ≠ 0 := by
  rw [invB_eq, Bool.and_eq_true] at hok
  have hlt : r < (b - B) + (B - b) := by
    have := hok.1
    rwa [Nat.blt_eq] at this
  rintro rfl
  unfold Enc at hx
  rw [zero_mul, zero_sub, abs_neg, abs_cast_sub] at hx
  have : (b - B) + (B - b) ≤ r := by exact_mod_cast hx
  omega

theorem sqrtB_pos {p B b r t : ℕ} {x : ℝ} (hx : Enc p B b r x) (hok : (sqrtB p B b r t).2.2 = true) :
    0 < x := by
  rw [sqrtB_eq, Bool.and_eq_true, Bool.and_eq_true] at hok
  have hlt : r < b - B := by
    have := hok.1.1
    rwa [Nat.blt_eq] at this
  have hB : B ≤ b := by omega
  unfold Enc at hx
  rw [abs_le, ← Nat.cast_sub hB] at hx
  have h1 : (r : ℝ) < ((b - B : ℕ) : ℝ) := by exact_mod_cast hlt
  have h2 : 0 < x * 2 ^ p := by linarith [hx.1]
  exact pos_of_mul_pos_left h2 (two_pow_pos' p).le

/-! ## Balls with flags -/

/-- The real number `v` lies in the ball `x`, provided that the flag of `x` holds. -/
def FEnc (p B : ℕ) (x : ℕ × ℕ × Bool) (v : ℝ) : Prop := x.2.2 = true → Enc p B x.1 x.2.1 v

theorem FEnc.of_enc {p B b r : ℕ} {v : ℝ} (h : Enc p B b r v) : FEnc p B (b, r, true) v := fun _ => h

theorem fadd_sound {p B : ℕ} {x y : ℕ × ℕ × Bool} {a b : ℝ} (hx : FEnc p B x a) (hy : FEnc p B y b) :
    FEnc p B (fadd B x y) (a + b) := by
  intro h
  obtain ⟨h1, h2⟩ := withFlag_ok h
  rw [Bool.and_eq_true] at h2
  exact addB_sound (hx h2.1) (hy h2.2) h1

theorem fsub_sound {p B : ℕ} {x y : ℕ × ℕ × Bool} {a b : ℝ} (hx : FEnc p B x a) (hy : FEnc p B y b) :
    FEnc p B (fsub B x y) (a - b) := by
  intro h
  obtain ⟨h1, h2⟩ := withFlag_ok h
  rw [Bool.and_eq_true] at h2
  exact subB_sound (hx h2.1) (hy h2.2) h1

theorem fmul_sound {p B : ℕ} {x y : ℕ × ℕ × Bool} {a b : ℝ} (hx : FEnc p B x a) (hy : FEnc p B y b) :
    FEnc p B (fmul p B x y) (a * b) := by
  intro h
  obtain ⟨h1, h2⟩ := withFlag_ok h
  rw [Bool.and_eq_true] at h2
  exact mulB_sound (hx h2.1) (hy h2.2) h1

theorem finv_sound {p B : ℕ} {x : ℕ × ℕ × Bool} {a : ℝ} (hx : FEnc p B x a) :
    FEnc p B (finv p B x) a⁻¹ := by
  intro h
  obtain ⟨h1, h2⟩ := withFlag_ok h
  exact invB_sound (hx h2) h1

theorem finv_ne_zero {p B : ℕ} {x : ℕ × ℕ × Bool} {a : ℝ} (hx : FEnc p B x a)
    (h : (finv p B x).2.2 = true) : a ≠ 0 := by
  obtain ⟨h1, h2⟩ := withFlag_ok h
  exact invB_ne_zero (hx h2) h1

theorem fsqrt_sound {p B t : ℕ} {x : ℕ × ℕ × Bool} {a : ℝ} (hx : FEnc p B x a) :
    FEnc p B (fsqrt p B x t) (Real.sqrt a) := by
  intro h
  obtain ⟨h1, h2⟩ := withFlag_ok h
  exact sqrtB_sound (hx h2) h1

theorem fsqrt_pos {p B t : ℕ} {x : ℕ × ℕ × Bool} {a : ℝ} (hx : FEnc p B x a)
    (h : (fsqrt p B x t).2.2 = true) : 0 < a := by
  obtain ⟨h1, h2⟩ := withFlag_ok h
  exact sqrtB_pos (hx h2) h1

/-- The flag of an operation with flags implies the flags of its arguments. -/
theorem fadd_flag {B : ℕ} {x y : ℕ × ℕ × Bool} (h : (fadd B x y).2.2 = true) :
    x.2.2 = true ∧ y.2.2 = true := by
  have h2 := (withFlag_ok h).2
  rwa [Bool.and_eq_true] at h2

theorem fsub_flag {B : ℕ} {x y : ℕ × ℕ × Bool} (h : (fsub B x y).2.2 = true) :
    x.2.2 = true ∧ y.2.2 = true := by
  have h2 := (withFlag_ok h).2
  rwa [Bool.and_eq_true] at h2

theorem fmul_flag {p B : ℕ} {x y : ℕ × ℕ × Bool} (h : (fmul p B x y).2.2 = true) :
    x.2.2 = true ∧ y.2.2 = true := by
  have h2 := (withFlag_ok h).2
  rwa [Bool.and_eq_true] at h2

/-- The ball of the number `1`. -/
theorem fenc_one (p B : ℕ) : FEnc p B (B + 1 <<< p, 0, true) 1 := by
  intro _
  show |(1 : ℝ) * 2 ^ p - (((B + 1 <<< p : ℕ) : ℝ) - B)| ≤ ((0 : ℕ) : ℝ)
  rw [Nat.one_shiftLeft]
  push_cast
  rw [show (1 : ℝ) * 2 ^ p - ((B : ℝ) + 2 ^ p - B) = 0 by ring]
  simp

end CAP.Interval

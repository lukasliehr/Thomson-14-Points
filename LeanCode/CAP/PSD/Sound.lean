module

public import Mathlib.Tactic.Zify
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.BigOperators.Fin
public import CAP.Core.PackedLemmas
public import CAP.Core.Triangular
public import CAP.PSD.Kernel
public import CAP.PSD.Dominant

/-!
# E2, positive definiteness: soundness of the checker

**Theorem** (`CAP.PSD.check_sound`). If `CAP.PSD.check P rows cols = true`, then the symmetric
integer matrix `gram P rows` that is stored in `rows` is positive definite as a real matrix.

The proof follows the checker.

1. `rowGo` runs `rowOk` on every row (`rowOk_of_check`). Row `i` and column `i` are the packed
   vectors `triRow P.w P.n rows i` and `triRow P.w P.n cols i`, with the slots `triEnt P.w P.n rows i s` and
   `triEnt P.w P.n cols i s`, `s < n - i`.
2. The first two conditions of `rowOk` bound the slots (`data_bounds`).
3. `colGo` computes the packed vectors `U` and `V` with the slots `uSlot` and `vSlot`
   (`colGo_row`). Hence `A` and `B` are packed vectors with the slots `aSlot` and `bSlot`, up to
   the second copy of the diagonal entry, and all slots are below `2 ^ (w - 2)` (`slot_bounds`).
4. The last two conditions of `rowOk` are inequalities between these slots (`row_arith`,
   `row_sound`).
5. In the integers, `aSlot - bSlot` is the entry of `2 ^ p2 • G - L * Lᵀ` (`resid_eq`). The
   statement follows from `posDef_of_witness`.
-/

@[expose] public section

namespace CAP.PSD

open Finset

/-! ## The decoded matrices -/

/-- The entry `X i j`, `i ≤ j`, of the data. -/
def dataEntry (P : Params) (rows i j : ℕ) : ℤ := (triEnt P.w P.n rows i (j - i) : ℤ) - 2 ^ (P.a - 1)

/-- The entry `L j k` of the factor: zero above the diagonal. -/
def factorEntry (P : Params) (cols j k : ℕ) : ℤ :=
  if k ≤ j then (triEnt P.w P.n cols k (j - k) : ℤ) - 2 ^ (P.aL - 1) else 0

/-- The symmetric integer matrix `G` of the statement: `G i i = 2 * X i i` and
`G i j = X i j` for `i < j`. -/
def gram (P : Params) (rows : ℕ) : Matrix (Fin P.n) (Fin P.n) ℤ := fun i j =>
  if i = j then 2 * dataEntry P rows i i
  else if i < j then dataEntry P rows i j else dataEntry P rows j i

/-- The lower triangular integer matrix `L` of the witness. -/
def factor (P : Params) (cols : ℕ) : Matrix (Fin P.n) (Fin P.n) ℤ := fun j k =>
  factorEntry P cols j k

theorem gram_symm (P : Params) (rows : ℕ) (i j : Fin P.n) : gram P rows i j = gram P rows j i := by
  unfold gram
  rcases lt_trichotomy i j with h | h | h
  · rw [if_neg h.ne, if_pos h, if_neg h.ne', if_neg h.asymm]
  · subst h; rfl
  · rw [if_neg h.ne', if_neg h.asymm, if_neg h.ne, if_pos h]

/-! ## The parameters and the constants -/

/-- The inequalities that `paramsOk` tests. -/
structure Ok (P : Params) : Prop where
  hn : P.n < 2 ^ P.nb
  ha : 1 ≤ P.a
  haL : 1 ≤ P.aL
  hw1 : P.p2 + P.a + 4 ≤ P.w
  hw2 : 2 * P.aL + P.nb + 4 ≤ P.w
  hw3 : P.e + 3 ≤ P.w

theorem ok_of_paramsOk (P : Params) (h : paramsOk P = true) : Ok P := by
  simp only [paramsOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  exact ⟨by rw [← Nat.one_shiftLeft]; exact h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

section consts
variable (P : Params)

theorem c_mw : (mkConsts P).mw = 2 ^ P.w - 1 := mask_eq P.w
theorem c_onN : (mkConsts P).onN = ones P.w P.n := rfl
theorem c_H : (mkConsts P).H = 2 ^ (P.w - 1) := Nat.one_shiftLeft _
theorem c_sbeta : (mkConsts P).sbeta = 2 ^ (P.p2 + (P.a - 1)) := Nat.one_shiftLeft _
theorem c_betaL : (mkConsts P).betaL = 2 ^ (P.aL - 1) := Nat.one_shiftLeft _
theorem c_betaL2 : (mkConsts P).betaL2 = 2 ^ (2 * (P.aL - 1)) := Nat.one_shiftLeft _

theorem c_hiA : (mkConsts P).hiA = 2 ^ P.w - 2 ^ P.a := by
  show (1 <<< P.w) - (1 <<< P.a) = _
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft]

theorem c_hiL : (mkConsts P).hiL = 2 ^ P.w - 2 ^ P.aL := by
  show (1 <<< P.w) - (1 <<< P.aL) = _
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft]

theorem c_hiE : (mkConsts P).hiE = 2 ^ P.w - 2 ^ (P.e + 1) := by
  show (1 <<< P.w) - (1 <<< (P.e + 1)) = _
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft]

theorem c_He : (mkConsts P).He = 2 ^ (P.w - 1) + 2 ^ P.e := by
  show (1 <<< (P.w - 1)) + (1 <<< P.e) = _
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft]

theorem c_dg : (mkConsts P).dg = (P.n - 1) * 2 ^ P.e + 1 := by
  show ((P.n - 1) <<< P.e) + 1 = _
  rw [Nat.shiftLeft_eq]

end consts

theorem raw_land (a b : ℕ) : Nat.land a b = a &&& b := rfl
theorem raw_shiftRight (a b : ℕ) : Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow a b
theorem raw_shiftLeft (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

/-! ## The loop over the rows -/

/-- The columns `i - 1, …, 0`: the stack of the checker before row `i`. -/
def stk (P : Params) (cols : ℕ) : ℕ → List ℕ
  | 0 => []
  | i + 1 => triRow P.w P.n cols i :: stk P cols i

theorem rowGo_succ_true {P : Params} {c : Consts} {cnt R C : ℕ} {stack : List ℕ} {i : ℕ}
    (h : rowGo P c (cnt + 1) R C stack i = true) :
    rowOk P c (R % 2 ^ (P.w * (P.n - i))) (C % 2 ^ (P.w * (P.n - i)))
        (C % 2 ^ (P.w * (P.n - i)) :: stack) i = true ∧
      rowGo P c cnt (R / 2 ^ (P.w * (P.n - i))) (C / 2 ^ (P.w * (P.n - i)))
        (C % 2 ^ (P.w * (P.n - i)) :: stack) (i + 1) = true := by
  have e1 : ∀ x : ℕ, Nat.land x (mask (Nat.mul P.w (Nat.sub P.n i))) = x % 2 ^ (P.w * (P.n - i)) := by
    intro x
    show x &&& mask (P.w * (P.n - i)) = _
    rw [mask_eq, Nat.and_two_pow_sub_one_eq_mod]
  have e2 : ∀ x : ℕ, Nat.shiftRight x (Nat.mul P.w (Nat.sub P.n i)) = x / 2 ^ (P.w * (P.n - i)) :=
    fun x => Nat.shiftRight_eq_div_pow x _
  have h' : (Bool.rec (motive := fun _ => Bool) false
      (rowGo P c cnt (R / 2 ^ (P.w * (P.n - i))) (C / 2 ^ (P.w * (P.n - i)))
        (C % 2 ^ (P.w * (P.n - i)) :: stack) (i + 1))
      (rowOk P c (R % 2 ^ (P.w * (P.n - i))) (C % 2 ^ (P.w * (P.n - i)))
        (C % 2 ^ (P.w * (P.n - i)) :: stack) i)) = true := by
    rw [← e1 R, ← e1 C, ← e2 R, ← e2 C]
    exact h
  cases hb : rowOk P c (R % 2 ^ (P.w * (P.n - i))) (C % 2 ^ (P.w * (P.n - i)))
      (C % 2 ^ (P.w * (P.n - i)) :: stack) i with
  | false =>
    rw [hb] at h'
    exact absurd h' Bool.false_ne_true
  | true =>
    rw [hb] at h'
    exact ⟨rfl, h'⟩

/-- If `rowGo` accepts, then `rowOk` accepts every row. -/
theorem rowGo_rows (P : Params) (c : Consts) (rows cols : ℕ) : ∀ (cnt i : ℕ),
    rowGo P c cnt (rows / 2 ^ (P.w * triOff P.n i)) (cols / 2 ^ (P.w * triOff P.n i)) (stk P cols i) i = true →
    ∀ t, t < cnt →
      rowOk P c (triRow P.w P.n rows (i + t)) (triRow P.w P.n cols (i + t)) (stk P cols (i + t + 1)) (i + t) = true
  | 0, _, _, t, ht => absurd ht (Nat.not_lt_zero t)
  | cnt + 1, i, h, t, ht => by
    obtain ⟨h1, h2⟩ := rowGo_succ_true h
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← pow_add, ← mul_add, ← triOff_succ] at h2
    rcases t with _ | t
    · exact h1
    · have h3 := rowGo_rows P c rows cols cnt (i + 1) h2 t (Nat.lt_of_succ_lt_succ ht)
      have e : i + 1 + t = i + (t + 1) := by omega
      rw [e] at h3
      exact h3

theorem rowOk_of_check (P : Params) (rows cols : ℕ) (h : check P rows cols = true) :
    paramsOk P = true ∧ ∀ i, i < P.n →
      rowOk P (mkConsts P) (triRow P.w P.n rows i) (triRow P.w P.n cols i) (stk P cols (i + 1)) i = true := by
  have h' : paramsOk P = true ∧ rowGo P (mkConsts P) P.n rows cols List.nil 0 = true := by
    unfold check at h
    exact Bool.and_eq_true_iff.mp h
  refine ⟨h'.1, fun i hi => ?_⟩
  have h0 : rowGo P (mkConsts P) P.n (rows / 2 ^ (P.w * triOff P.n 0)) (cols / 2 ^ (P.w * triOff P.n 0))
      (stk P cols 0) 0 = true := by
    rw [triOff_zero, mul_zero, pow_zero, Nat.div_one, Nat.div_one]
    exact h'.2
  have h2 := rowGo_rows P (mkConsts P) rows cols P.n 0 h0 i hi
  rw [zero_add] at h2
  exact h2

/-! ## The columns -/

theorem colGo_nil (w mw sh U V : ℕ) : colGo w mw [] sh U V = (U, V) := rfl

theorem colGo_cons (w lam : ℕ) (l : List ℕ) (sh U V : ℕ) :
    colGo w (2 ^ w - 1) (lam :: l) sh U V =
      colGo w (2 ^ w - 1) l (sh + w) (U + lam / 2 ^ sh % 2 ^ w * (lam / 2 ^ sh)) (V + lam / 2 ^ sh) := by
  rw [← Nat.and_two_pow_sub_one_eq_mod, ← Nat.shiftRight_eq_div_pow]
  rfl

/-- The value of `colGo` on the columns `i - 1, …, 0`, where column `k` is shifted by `r - k`
slots. -/
theorem colGo_stk (P : Params) (cols r : ℕ) : ∀ (i : ℕ), i ≤ r + 1 → ∀ (U V : ℕ),
    colGo P.w (2 ^ P.w - 1) (stk P cols i) (P.w * (r + 1 - i)) U V =
      (U + ∑ k ∈ range i, triRow P.w P.n cols k / 2 ^ (P.w * (r - k)) % 2 ^ P.w
            * (triRow P.w P.n cols k / 2 ^ (P.w * (r - k))),
       V + ∑ k ∈ range i, triRow P.w P.n cols k / 2 ^ (P.w * (r - k)))
  | 0, _, U, V => by simp [stk, colGo_nil]
  | i + 1, hi, U, V => by
    have e1 : P.w * (r + 1 - (i + 1)) + P.w = P.w * (r + 1 - i) := by
      have : r + 1 - i = (r + 1 - (i + 1)) + 1 := by omega
      rw [this]
      ring
    have e2 : r + 1 - (i + 1) = r - i := by omega
    rw [stk, colGo_cons, e1, colGo_stk P cols r i (by omega), sum_range_succ, sum_range_succ, e2]
    congr 1 <;> ring

/-- Column `k ≤ i` without its first `i - k` slots. -/
theorem part_div (P : Params) (cols : ℕ) {i k : ℕ} (hk : k ≤ i) (hi : i ≤ P.n) :
    triRow P.w P.n cols k / 2 ^ (P.w * (i - k))
      = packSum P.w (P.n - i) (fun s => triEnt P.w P.n cols k (s + (i - k))) := by
  rw [triRow_eq, packSum_div P.w (i - k) (P.n - k) _ (by omega) (fun s _ => triEnt_lt P.w P.n cols k s)]
  congr 1
  omega

/-- Slot `s` of `U` in row `i`. -/
def uSlot (P : Params) (cols i s : ℕ) : ℕ :=
  ∑ k ∈ range (i + 1), triEnt P.w P.n cols k (i - k) * triEnt P.w P.n cols k (s + (i - k))

/-- Slot `s` of `V` in row `i`. -/
def vSlot (P : Params) (cols i s : ℕ) : ℕ := ∑ k ∈ range (i + 1), triEnt P.w P.n cols k (s + (i - k))

theorem colGo_row (P : Params) (cols : ℕ) {i : ℕ} (hi : i < P.n) :
    colGo P.w (2 ^ P.w - 1) (stk P cols (i + 1)) 0 0 0 =
      (packSum P.w (P.n - i) (uSlot P cols i), packSum P.w (P.n - i) (vSlot P cols i)) := by
  have h := colGo_stk P cols i (i + 1) le_rfl 0 0
  rw [Nat.sub_self, mul_zero, zero_add, zero_add] at h
  rw [h]
  obtain ⟨m', hm⟩ : ∃ m', P.n - i = m' + 1 := ⟨P.n - i - 1, by omega⟩
  have hτ : ∀ k ∈ range (i + 1), triRow P.w P.n cols k / 2 ^ (P.w * (i - k)) =
      packSum P.w (P.n - i) (fun s => triEnt P.w P.n cols k (s + (i - k))) :=
    fun k hk => part_div P cols (Nat.lt_succ_iff.mp (mem_range.mp hk)) hi.le
  have hℓ : ∀ k ∈ range (i + 1),
      triRow P.w P.n cols k / 2 ^ (P.w * (i - k)) % 2 ^ P.w = triEnt P.w P.n cols k (i - k) := by
    intro k hk
    rw [hτ k hk, hm]
    have h0 := packSum_succ_mod P.w m' (fun s => triEnt P.w P.n cols k (s + (i - k))) (triEnt_lt P.w P.n cols k _)
    simpa using h0
  congr 1
  · have hu : uSlot P cols i
        = fun s => ∑ k ∈ range (i + 1), triEnt P.w P.n cols k (i - k) * triEnt P.w P.n cols k (s + (i - k)) := rfl
    rw [hu, packSum_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [hℓ k hk, hτ k hk, packSum_mul]
  · have hv : vSlot P cols i = fun s => ∑ k ∈ range (i + 1), triEnt P.w P.n cols k (s + (i - k)) := rfl
    rw [hv, packSum_sum]
    exact sum_congr rfl fun k hk => hτ k hk

/-! ## The conditions of a row -/

/-- The four conditions of `rowOk` in the usual notation. -/
theorem rowOk_spec (P : Params) (rho lam : ℕ) (stack : List ℕ) (i Up Vp on A B : ℕ)
    (hUV : colGo P.w (2 ^ P.w - 1) stack 0 0 0 = (Up, Vp))
    (hon : on = ones P.w P.n / 2 ^ (P.w * i))
    (hA : A = rho * 2 ^ P.p2 + 2 ^ (P.aL - 1) * Vp + 2 ^ (P.aL - 1) * (Vp % 2 ^ P.w) * on
      + rho % 2 ^ P.w * 2 ^ P.p2)
    (hB : B = Up + ((i + 1) * 2 ^ (2 * (P.aL - 1)) + 2 ^ (P.p2 + (P.a - 1))) * on
      + 2 ^ (P.p2 + (P.a - 1)))
    (h : rowOk P (mkConsts P) rho lam stack i = true) :
    rho &&& ((2 ^ P.w - 2 ^ P.a) * on) = 0 ∧ lam &&& ((2 ^ P.w - 2 ^ P.aL) * on) = 0 ∧
    B % 2 ^ P.w + ((P.n - 1) * 2 ^ P.e + 1) ≤ A % 2 ^ P.w ∧
    (A / 2 ^ P.w + (2 ^ (P.w - 1) + 2 ^ P.e) * (on / 2 ^ P.w) - B / 2 ^ P.w)
        &&& ((2 ^ P.w - 2 ^ (P.e + 1)) * (on / 2 ^ P.w)) = 2 ^ (P.w - 1) * (on / 2 ^ P.w) := by
  subst hon hA hB
  unfold rowOk at h
  simp only [hUV, c_mw, c_onN, c_H, c_sbeta, c_betaL, c_betaL2, c_hiA, c_hiL, c_hiE, c_He, c_dg,
    Bool.and_eq_true, Nat.ble_eq, raw_land, raw_shiftRight, raw_shiftLeft,
    Nat.add_eq, Nat.mul_eq, Nat.sub_eq, Nat.succ_eq_add_one, Nat.and_two_pow_sub_one_eq_mod] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1.1.1, Nat.eq_of_beq_eq_true h.1.1.2, h.1.2,
    Nat.eq_of_beq_eq_true h.2⟩

/-- The first two conditions of `rowOk`: the slots of row `i` of the data are below `2 ^ a`, and
the slots of column `i` of the factor are below `2 ^ aL`. -/
theorem data_bounds (P : Params) (hP : Ok P) (rows cols : ℕ) {i : ℕ} (hi : i < P.n)
    (hrow : rowOk P (mkConsts P) (triRow P.w P.n rows i) (triRow P.w P.n cols i) (stk P cols (i + 1)) i = true) :
    (∀ s, s < P.n - i → triEnt P.w P.n rows i s < 2 ^ P.a) ∧
      (∀ s, s < P.n - i → triEnt P.w P.n cols i s < 2 ^ P.aL) := by
  have hw : 0 < P.w := by have := hP.hw3; omega
  have hon := ones_div P.w P.n i hw hi.le
  rcases hUV : colGo P.w (2 ^ P.w - 1) (stk P cols (i + 1)) 0 0 0 with ⟨Up, Vp⟩
  obtain ⟨h1, h2, -, -⟩ := rowOk_spec P _ _ _ i Up Vp _ _ _ hUV rfl rfl rfl hrow
  rw [hon, triRow_eq] at h1 h2
  exact ⟨slots_lt_of_and_hi P.w P.a (P.n - i) _ (by have := hP.hw1; omega)
      (fun s _ => triEnt_lt P.w P.n rows i s) h1,
    slots_lt_of_and_hi P.w P.aL (P.n - i) _ (by have := hP.hw2; omega)
      (fun s _ => triEnt_lt P.w P.n cols i s) h2⟩

/-- Slot `s` of `A` in row `i`, without the second copy of the diagonal entry. -/
def aSlot (P : Params) (rows cols i s : ℕ) : ℕ :=
  2 ^ P.p2 * triEnt P.w P.n rows i s + 2 ^ (P.aL - 1) * vSlot P cols i s + 2 ^ (P.aL - 1) * vSlot P cols i 0

/-- Slot `s` of `B` in row `i`, without the second copy of the bias. -/
def bSlot (P : Params) (cols i s : ℕ) : ℕ :=
  uSlot P cols i s + ((i + 1) * 2 ^ (2 * (P.aL - 1)) + 2 ^ (P.p2 + (P.a - 1)))

theorem vSlot_le (P : Params) (cols : ℕ) {i : ℕ} (hi : i < P.n)
    (hL : ∀ k, k ≤ i → ∀ s, s < P.n - k → triEnt P.w P.n cols k s < 2 ^ P.aL) {s : ℕ} (hs : s < P.n - i) :
    vSlot P cols i s ≤ (i + 1) * 2 ^ P.aL := by
  unfold vSlot
  have h := Finset.sum_le_card_nsmul (range (i + 1)) (fun k => triEnt P.w P.n cols k (s + (i - k))) (2 ^ P.aL)
    (fun k hk => by
      have hk' := Nat.lt_succ_iff.mp (mem_range.mp hk)
      exact (hL k hk' _ (by omega)).le)
  simpa using h

theorem uSlot_le (P : Params) (cols : ℕ) {i : ℕ} (hi : i < P.n)
    (hL : ∀ k, k ≤ i → ∀ s, s < P.n - k → triEnt P.w P.n cols k s < 2 ^ P.aL) {s : ℕ} (hs : s < P.n - i) :
    uSlot P cols i s ≤ (i + 1) * (2 ^ P.aL * 2 ^ P.aL) := by
  unfold uSlot
  have h := Finset.sum_le_card_nsmul (range (i + 1))
    (fun k => triEnt P.w P.n cols k (i - k) * triEnt P.w P.n cols k (s + (i - k))) (2 ^ P.aL * 2 ^ P.aL)
    (fun k hk => by
      have hk' := Nat.lt_succ_iff.mp (mem_range.mp hk)
      exact Nat.mul_le_mul (hL k hk' _ (by omega)).le (hL k hk' _ (by omega)).le)
  simpa using h

/-- All slots of `A` and `B` are below `2 ^ (w - 2)`. -/
theorem slot_bounds (P : Params) (hP : Ok P) (rows cols : ℕ) {i : ℕ} (hi : i < P.n)
    (hX : ∀ s, s < P.n - i → triEnt P.w P.n rows i s < 2 ^ P.a)
    (hL : ∀ k, k ≤ i → ∀ s, s < P.n - k → triEnt P.w P.n cols k s < 2 ^ P.aL) :
    ∀ s, s < P.n - i →
      4 * (aSlot P rows cols i s + triEnt P.w P.n rows i 0 * 2 ^ P.p2) < 2 ^ P.w ∧
      4 * (bSlot P cols i s + 2 ^ (P.p2 + (P.a - 1))) < 2 ^ P.w ∧
      vSlot P cols i s < 2 ^ P.w := by
  intro s hs
  have h0 : 0 < P.n - i := by omega
  have hWpos := Nat.two_pow_pos P.w
  -- powers of two
  have e1 : 2 ^ P.aL = 2 * 2 ^ (P.aL - 1) := two_pow_pred hP.haL
  have e2 : 2 ^ P.a = 2 * 2 ^ (P.a - 1) := two_pow_pred hP.ha
  have e3 : 2 ^ (2 * (P.aL - 1)) = 2 ^ (P.aL - 1) * 2 ^ (P.aL - 1) := by rw [two_mul, pow_add]
  have e4 : 2 ^ (P.p2 + (P.a - 1)) = 2 ^ P.p2 * 2 ^ (P.a - 1) := pow_add _ _ _
  have hT : 32 * 2 ^ (P.p2 + (P.a - 1)) ≤ 2 ^ P.w := by
    calc 32 * 2 ^ (P.p2 + (P.a - 1)) = 2 ^ (P.p2 + (P.a - 1) + 5) := by ring
      _ ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) (by have := hP.ha; have := hP.hw1; omega)
  have hM : 64 * ((i + 1) * 2 ^ (2 * (P.aL - 1))) ≤ 2 ^ P.w := by
    have hn := hP.hn
    calc 64 * ((i + 1) * 2 ^ (2 * (P.aL - 1))) ≤ 64 * (2 ^ P.nb * 2 ^ (2 * (P.aL - 1))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ = 2 ^ (P.nb + 2 * (P.aL - 1) + 6) := by ring
      _ ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) (by have := hP.haL; have := hP.hw2; omega)
  -- the terms of the slots
  have hx : 2 ^ P.p2 * triEnt P.w P.n rows i s ≤ 2 * 2 ^ (P.p2 + (P.a - 1)) := by
    rw [e4]
    calc 2 ^ P.p2 * triEnt P.w P.n rows i s ≤ 2 ^ P.p2 * 2 ^ P.a := Nat.mul_le_mul_left _ (hX s hs).le
      _ = 2 * (2 ^ P.p2 * 2 ^ (P.a - 1)) := by rw [e2]; ring
  have hx0 : triEnt P.w P.n rows i 0 * 2 ^ P.p2 ≤ 2 * 2 ^ (P.p2 + (P.a - 1)) := by
    rw [e4]
    calc triEnt P.w P.n rows i 0 * 2 ^ P.p2 ≤ 2 ^ P.a * 2 ^ P.p2 := Nat.mul_le_mul_right _ (hX 0 h0).le
      _ = 2 * (2 ^ P.p2 * 2 ^ (P.a - 1)) := by rw [e2]; ring
  have hv : ∀ t, t < P.n - i →
      2 ^ (P.aL - 1) * vSlot P cols i t ≤ 2 * ((i + 1) * 2 ^ (2 * (P.aL - 1))) := by
    intro t ht
    calc 2 ^ (P.aL - 1) * vSlot P cols i t ≤ 2 ^ (P.aL - 1) * ((i + 1) * 2 ^ P.aL) :=
          Nat.mul_le_mul_left _ (vSlot_le P cols hi hL ht)
      _ = 2 * ((i + 1) * 2 ^ (2 * (P.aL - 1))) := by rw [e1, e3]; ring
  have hu : uSlot P cols i s ≤ 4 * ((i + 1) * 2 ^ (2 * (P.aL - 1))) := by
    calc uSlot P cols i s ≤ (i + 1) * (2 ^ P.aL * 2 ^ P.aL) := uSlot_le P cols hi hL hs
      _ = 4 * ((i + 1) * 2 ^ (2 * (P.aL - 1))) := by rw [e1, e3]; ring
  have hvs : vSlot P cols i s ≤ 2 * ((i + 1) * 2 ^ (2 * (P.aL - 1))) := by
    have h1 : 1 ≤ 2 ^ (P.aL - 1) := Nat.one_le_two_pow
    calc vSlot P cols i s = 1 * vSlot P cols i s := (one_mul _).symm
      _ ≤ 2 ^ (P.aL - 1) * vSlot P cols i s := Nat.mul_le_mul_right _ h1
      _ ≤ 2 * ((i + 1) * 2 ^ (2 * (P.aL - 1))) := hv s hs
  have hv0 := hv 0 h0
  have hvs' := hv s hs
  unfold aSlot bSlot
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- The packed vector `A` of a row. -/
theorem A_eq (w m S bL : ℕ) (ρ V : ℕ → ℕ) (hρ : ρ 0 < 2 ^ w) (hV : V 0 < 2 ^ w) :
    packSum w (m + 1) ρ * S + bL * packSum w (m + 1) V
        + bL * (packSum w (m + 1) V % 2 ^ w) * packSum w (m + 1) (fun _ => 1)
        + packSum w (m + 1) ρ % 2 ^ w * S
      = packSum w (m + 1) (fun s => S * ρ s + bL * V s + bL * V 0) + ρ 0 * S := by
  have h1 : packSum w (m + 1) (fun s => S * ρ s + bL * V s + bL * V 0)
      = S * packSum w (m + 1) ρ + bL * packSum w (m + 1) V
        + bL * V 0 * packSum w (m + 1) (fun _ => 1) := by
    rw [packSum_add_const, packSum_add, packSum_mul, packSum_mul]
  rw [h1, packSum_succ_mod w m ρ hρ, packSum_succ_mod w m V hV]
  ring

/-- The packed vector `B` of a row. -/
theorem B_eq (w m c d : ℕ) (U : ℕ → ℕ) :
    packSum w (m + 1) U + c * packSum w (m + 1) (fun _ => 1) + d
      = packSum w (m + 1) (fun s => U s + c) + d := by
  rw [packSum_add_const]

/-- The last two conditions of `rowOk` for packed vectors `A = pack fA + x` and
`B = pack fB + y` whose slots are below `2 ^ (w - 2)`: an inequality between the lowest slots,
and two-sided bounds for the differences of the other slots. -/
theorem row_arith (w m k e g Hh x y : ℕ) (fA fB : ℕ → ℕ)
    (hA : ∀ s, s < m + 1 → 4 * (fA s + x) < 2 ^ w) (hB : ∀ s, s < m + 1 → 4 * (fB s + y) < 2 ^ w)
    (hH : 2 ^ w = 2 * Hh) (hE : 8 * 2 ^ e ≤ 2 ^ w) (hk : k ≤ w)
    (hd : (packSum w (m + 1) fB + y) % 2 ^ w + g ≤ (packSum w (m + 1) fA + x) % 2 ^ w)
    (ho : ((packSum w (m + 1) fA + x) / 2 ^ w + (Hh + 2 ^ e) * packSum w m (fun _ => 1)
          - (packSum w (m + 1) fB + y) / 2 ^ w) &&& ((2 ^ w - 2 ^ k) * packSum w m (fun _ => 1))
        = Hh * packSum w m (fun _ => 1)) :
    fB 0 + y + g ≤ fA 0 + x ∧
    ∀ s, s < m → Hh + fB (s + 1) ≤ fA (s + 1) + (Hh + 2 ^ e) ∧
      fA (s + 1) + (Hh + 2 ^ e) < Hh + 2 ^ k + fB (s + 1) := by
  have hWpos := Nat.two_pow_pos w
  have hx0 := hA 0 (Nat.succ_pos m)
  have hy0 := hB 0 (Nat.succ_pos m)
  have hA0 : (packSum w (m + 1) fA + x) % 2 ^ w = fA 0 + x := by
    rw [packSum_succ, add_right_comm, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hA1 : (packSum w (m + 1) fA + x) / 2 ^ w = packSum w m (fun s => fA (s + 1)) := by
    rw [packSum_succ, add_right_comm, Nat.add_mul_div_left _ _ hWpos, Nat.div_eq_of_lt (by omega),
      zero_add]
  have hB0 : (packSum w (m + 1) fB + y) % 2 ^ w = fB 0 + y := by
    rw [packSum_succ, add_right_comm, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hB1 : (packSum w (m + 1) fB + y) / 2 ^ w = packSum w m (fun s => fB (s + 1)) := by
    rw [packSum_succ, add_right_comm, Nat.add_mul_div_left _ _ hWpos, Nat.div_eq_of_lt (by omega),
      zero_add]
  rw [hA0, hB0] at hd
  refine ⟨hd, ?_⟩
  have hZ : packSum w m (fun s => fA (s + 1)) + (Hh + 2 ^ e) * packSum w m (fun _ => 1)
        - packSum w m (fun s => fB (s + 1))
      = packSum w m (fun s => fA (s + 1) + (Hh + 2 ^ e) - fB (s + 1)) := by
    rw [← packSum_add_const]
    exact packSum_sub w m _ _ (fun j hj => by
      have := hB (j + 1) (Nat.succ_lt_succ hj)
      show fB (j + 1) ≤ fA (j + 1) + (Hh + 2 ^ e)
      omega)
  rw [hA1, hB1, hZ] at ho
  intro s hs
  have hZlt : ∀ j, j < m → fA (j + 1) + (Hh + 2 ^ e) - fB (j + 1) < 2 ^ w := by
    intro j hj
    have := hA (j + 1) (Nat.succ_lt_succ hj)
    omega
  have hHlt : Hh < 2 ^ w := by omega
  have h1 := slots_bounds_of_and_hi w k m Hh (fun s => fA (s + 1) + (Hh + 2 ^ e) - fB (s + 1))
    hk hHlt hZlt ho s hs
  have hBs := hB (s + 1) (Nat.succ_lt_succ hs)
  obtain ⟨h2, h3⟩ := h1
  constructor <;> omega

/-- The last two conditions of `rowOk` as inequalities between the slots of `A` and `B`. -/
theorem row_sound (P : Params) (hP : Ok P) (rows cols : ℕ) {i : ℕ} (hi : i < P.n)
    (hX : ∀ s, s < P.n - i → triEnt P.w P.n rows i s < 2 ^ P.a)
    (hL : ∀ k, k ≤ i → ∀ s, s < P.n - k → triEnt P.w P.n cols k s < 2 ^ P.aL)
    (hrow : rowOk P (mkConsts P) (triRow P.w P.n rows i) (triRow P.w P.n cols i) (stk P cols (i + 1)) i = true) :
    bSlot P cols i 0 + 2 ^ (P.p2 + (P.a - 1)) + ((P.n - 1) * 2 ^ P.e + 1)
        ≤ aSlot P rows cols i 0 + triEnt P.w P.n rows i 0 * 2 ^ P.p2 ∧
    ∀ s, s < P.n - i - 1 →
      2 ^ (P.w - 1) + bSlot P cols i (s + 1)
          ≤ aSlot P rows cols i (s + 1) + (2 ^ (P.w - 1) + 2 ^ P.e) ∧
        aSlot P rows cols i (s + 1) + (2 ^ (P.w - 1) + 2 ^ P.e)
          < 2 ^ (P.w - 1) + 2 ^ (P.e + 1) + bSlot P cols i (s + 1) := by
  obtain ⟨m', hm⟩ : ∃ m', P.n - i = m' + 1 := ⟨P.n - i - 1, by omega⟩
  have hm' : P.n - i - 1 = m' := by omega
  have hw : 0 < P.w := by have := hP.hw3; omega
  have hb := slot_bounds P hP rows cols hi hX hL
  rw [hm] at hb
  -- the packed vectors of the row
  have hrho : triRow P.w P.n rows i = packSum P.w (m' + 1) (triEnt P.w P.n rows i) := by rw [triRow_eq, hm]
  have hUV := colGo_row P cols hi
  have hon := ones_div P.w P.n i hw hi.le
  rw [hm] at hUV hon
  have hone : packSum P.w (m' + 1) (fun _ => 1) / 2 ^ P.w = packSum P.w m' (fun _ => 1) :=
    packSum_succ_div P.w m' _ (Nat.one_lt_two_pow hw.ne')
  have hρ0 : triEnt P.w P.n rows i 0 < 2 ^ P.w := triEnt_lt _ _ _ _ _
  have hV0 : vSlot P cols i 0 < 2 ^ P.w := (hb 0 (Nat.succ_pos m')).2.2
  -- the conditions of the checker
  obtain ⟨-, -, hd, ho⟩ := rowOk_spec P _ _ _ i _ _ _ _ _ hUV rfl rfl rfl hrow
  rw [hon, hrho, A_eq P.w m' (2 ^ P.p2) (2 ^ (P.aL - 1)) (triEnt P.w P.n rows i) (vSlot P cols i) hρ0 hV0,
    B_eq P.w m' _ _ (uSlot P cols i)] at hd
  rw [hon, hrho, A_eq P.w m' (2 ^ P.p2) (2 ^ (P.aL - 1)) (triEnt P.w P.n rows i) (vSlot P cols i) hρ0 hV0,
    B_eq P.w m' _ _ (uSlot P cols i), hone] at ho
  have hE : 8 * 2 ^ P.e ≤ 2 ^ P.w := by
    calc 8 * 2 ^ P.e = 2 ^ (P.e + 3) := by ring
      _ ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) hP.hw3
  have h := row_arith P.w m' (P.e + 1) P.e ((P.n - 1) * 2 ^ P.e + 1) (2 ^ (P.w - 1))
    (triEnt P.w P.n rows i 0 * 2 ^ P.p2) (2 ^ (P.p2 + (P.a - 1))) (aSlot P rows cols i) (bSlot P cols i)
    (fun s hs => (hb s hs).1) (fun s hs => (hb s hs).2.1) (two_pow_pred hw)
    hE (by have := hP.hw3; omega) hd ho
  rw [hm']
  exact h

/-! ## The residual in the integers -/

/-- `∑ k ≤ i, L i k * L (i + s) k` for the decoded factor. -/
def lsum (P : Params) (cols i s : ℕ) : ℤ :=
  ∑ k ∈ range (i + 1), ((triEnt P.w P.n cols k (i - k) : ℤ) - 2 ^ (P.aL - 1))
    * ((triEnt P.w P.n cols k (s + (i - k)) : ℤ) - 2 ^ (P.aL - 1))

theorem lsum_eq (P : Params) (cols i s : ℕ) :
    lsum P cols i s = (uSlot P cols i s : ℤ) - 2 ^ (P.aL - 1) * vSlot P cols i 0
      - 2 ^ (P.aL - 1) * vSlot P cols i s + (i + 1) * 2 ^ (2 * (P.aL - 1)) := by
  have hterm : ∀ k : ℕ, ((triEnt P.w P.n cols k (i - k) : ℤ) - 2 ^ (P.aL - 1))
        * ((triEnt P.w P.n cols k (s + (i - k)) : ℤ) - 2 ^ (P.aL - 1))
      = (triEnt P.w P.n cols k (i - k) : ℤ) * triEnt P.w P.n cols k (s + (i - k))
        - 2 ^ (P.aL - 1) * triEnt P.w P.n cols k (0 + (i - k))
        - 2 ^ (P.aL - 1) * triEnt P.w P.n cols k (s + (i - k)) + 2 ^ (2 * (P.aL - 1)) := by
    intro k
    rw [zero_add]
    ring
  unfold lsum uSlot vSlot
  simp only [hterm, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_range,
    nsmul_eq_mul]
  push_cast
  ring

/-- In the integers, the difference of the slots of `A` and `B` is the entry of
`2 ^ p2 • X - L * Lᵀ`. -/
theorem resid_eq (P : Params) (rows cols i s : ℕ) :
    2 ^ P.p2 * ((triEnt P.w P.n rows i s : ℤ) - 2 ^ (P.a - 1)) - lsum P cols i s
      = (aSlot P rows cols i s : ℤ) - bSlot P cols i s := by
  rw [lsum_eq]
  unfold aSlot bSlot
  push_cast
  ring

/-- The sum over the columns of the factor is the sum over `k ≤ i`. -/
theorem factor_sum (P : Params) (cols : ℕ) {i j : ℕ} (hij : i ≤ j) (hj : j < P.n) :
    ∑ k : Fin P.n, factorEntry P cols i k * factorEntry P cols j k = lsum P cols i (j - i) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => factorEntry P cols i k * factorEntry P cols j k) P.n]
  have hsub : range (i + 1) ⊆ range P.n := range_subset_range.mpr (by omega)
  have h0 : ∀ k ∈ range P.n, k ∉ range (i + 1) →
      factorEntry P cols i k * factorEntry P cols j k = 0 := by
    intro k _ hk
    have hk' : ¬ k ≤ i := fun h => hk (mem_range.mpr (Nat.lt_succ_of_le h))
    unfold factorEntry
    rw [if_neg hk', zero_mul]
  rw [← Finset.sum_subset hsub h0]
  unfold lsum
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ i := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have e : j - k = j - i + (i - k) := by omega
  unfold factorEntry
  rw [if_pos hk', if_pos (hk'.trans hij), e]

/-! ## The theorem -/

/-- **Soundness of the checker of E2.** If `check P rows cols = true`, then the symmetric integer
matrix stored in `rows` is positive definite. -/
theorem check_sound (P : Params) (rows cols : ℕ) (h : check P rows cols = true) :
    ((gram P rows).map (Int.cast : ℤ → ℝ)).PosDef := by
  obtain ⟨hpar, hrows⟩ := rowOk_of_check P rows cols h
  have hP := ok_of_paramsOk P hpar
  have hdata := fun i (hi : i < P.n) => data_bounds P hP rows cols hi (hrows i hi)
  have hrow := fun i (hi : i < P.n) => row_sound P hP rows cols hi (hdata i hi).1
    (fun k hk => (hdata k (lt_of_le_of_lt hk hi)).2) (hrows i hi)
  -- the entries above the diagonal
  have hoff : ∀ i j : ℕ, i < j → j < P.n →
      |(2 : ℤ) ^ P.p2 * dataEntry P rows i j - lsum P cols i (j - i)| ≤ 2 ^ P.e := by
    intro i j hij hj
    obtain ⟨h2, h3⟩ := (hrow i (hij.trans hj)).2 (j - i - 1) (by omega)
    have e : j - i - 1 + 1 = j - i := by omega
    rw [e] at h2 h3
    have hr := resid_eq P rows cols i (j - i)
    unfold dataEntry
    rw [hr, abs_le]
    zify at h2 h3
    have hE : (2 : ℤ) ^ (P.e + 1) = 2 * 2 ^ P.e := by ring
    constructor <;> linarith
  -- the diagonal entries
  have hdiag : ∀ i : ℕ, i < P.n →
      ((P.n : ℤ) - 1) * 2 ^ P.e < (2 : ℤ) ^ P.p2 * (2 * dataEntry P rows i i) - lsum P cols i 0 := by
    intro i hi
    have hd := (hrow i hi).1
    have hr := resid_eq P rows cols i 0
    have h1n : 1 ≤ P.n := by omega
    zify [h1n] at hd
    have e0 : dataEntry P rows i i = (triEnt P.w P.n rows i 0 : ℤ) - 2 ^ (P.a - 1) := by
      unfold dataEntry
      rw [Nat.sub_self]
    have e1 : (2 : ℤ) ^ (P.p2 + (P.a - 1)) = 2 ^ P.p2 * 2 ^ (P.a - 1) := pow_add _ _ _
    rw [e0]
    linarith
  refine posDef_of_witness (gram P rows) (factor P cols) P.p2 P.e (gram_symm P rows) ?_ ?_
  · have key : ∀ i j : Fin P.n, i < j →
        |(2 : ℤ) ^ P.p2 * gram P rows i j - ∑ k, factor P cols i k * factor P cols j k|
          ≤ 2 ^ P.e := by
      intro i j hlt
      have hlt' : (i : ℕ) < j := Fin.lt_def.mp hlt
      have h1 := hoff i j hlt' j.isLt
      have h2 : gram P rows i j = dataEntry P rows i j := by
        unfold gram
        rw [if_neg hlt.ne, if_pos hlt]
      have h3 : ∑ k, factor P cols i k * factor P cols j k = lsum P cols i (j - i) :=
        factor_sum P cols hlt'.le j.isLt
      rw [h2, h3]
      exact h1
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact key i j hlt
    · have h1 := key j i hgt
      have h3 : ∑ k, factor P cols i k * factor P cols j k
          = ∑ k, factor P cols j k * factor P cols i k :=
        Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [gram_symm P rows i j, h3]
      exact h1
  · intro i
    have h1 := hdiag i i.isLt
    have h2 : gram P rows i i = 2 * dataEntry P rows i i := by
      unfold gram
      rw [if_pos rfl]
    have h3 : ∑ k, factor P cols i k * factor P cols i k = lsum P cols i 0 := by
      have := factor_sum P cols (le_refl (i : ℕ)) i.isLt
      rwa [Nat.sub_self] at this
    rw [h2, h3]
    exact h1

end CAP.PSD

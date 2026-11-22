module

public import CAP.Schema.ThreePoint.Bounds

/-!
# Schema S2, soundness: reading the digits

General statements for the last step of the checker.

* `loop3_true`: the three nested loops test `orbitOk` for all `e1 ≤ e2 ≤ e3` below the bound
  whose sum is at most `d2`.
* `slot_Dd`: if `Fp` and `Fn` are polynomials with natural coefficients below `2 ^ (W - 1)` and
  exponents below `q`, the slot of `Fp (X, …) + 2 ^ (W - 1) * (1, …, 1) - Fn (X, …)` at the position
  of a monomial is the difference of the two coefficients plus `2 ^ (W - 1)`.
* `orb_of_sorted`: a sum over the six permutations of three arguments that is known for sorted
  arguments is known for all arguments.
* The substitutions `(u, u, 1)`, `(u, 1, u)`, `(1, u, u)` and polynomials in `u` alone.
-/

@[expose] public section

namespace CAP.ThreePoint

open MvPolynomial Finset

/-! ## The loops -/

theorem loop1_succ (W q Dd B6 d2 e3 e2 cnt : ℕ) :
    loop1 W q Dd B6 d2 e3 e2 (cnt + 1) = (loop1 W q Dd B6 d2 e3 e2 cnt &&
      Bool.rec (motive := fun _ => Bool) (orbitOk W q Dd B6 cnt e2 e3) true (Nat.blt d2 (cnt + e2 + e3))) :=
  rfl

theorem loop1_true (W q Dd B6 d2 e3 e2 : ℕ) : ∀ cnt, loop1 W q Dd B6 d2 e3 e2 cnt = true →
    ∀ e1, e1 < cnt → e1 + e2 + e3 ≤ d2 → orbitOk W q Dd B6 e1 e2 e3 = true
  | 0, _, e1, h1, _ => absurd h1 (Nat.not_lt_zero e1)
  | cnt + 1, h, e1, h1, hd => by
    rw [loop1_succ, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with hlt | rfl
    · exact loop1_true W q Dd B6 d2 e3 e2 cnt h.1 e1 hlt hd
    · have h2 := h.2
      cases hb : Nat.blt d2 (e1 + e2 + e3) with
      | true =>
        have : d2 < e1 + e2 + e3 := by rwa [Nat.blt_eq] at hb
        omega
      | false =>
        rw [hb] at h2
        exact h2

theorem loop2_succ (W q Dd B6 d2 e3 cnt : ℕ) :
    loop2 W q Dd B6 d2 e3 (cnt + 1) = (loop2 W q Dd B6 d2 e3 cnt && loop1 W q Dd B6 d2 e3 cnt (cnt + 1)) :=
  rfl

theorem loop2_true (W q Dd B6 d2 e3 : ℕ) : ∀ cnt, loop2 W q Dd B6 d2 e3 cnt = true →
    ∀ e2, e2 < cnt → ∀ e1, e1 ≤ e2 → e1 + e2 + e3 ≤ d2 → orbitOk W q Dd B6 e1 e2 e3 = true
  | 0, _, e2, h2, _, _, _ => absurd h2 (Nat.not_lt_zero e2)
  | cnt + 1, h, e2, h2, e1, h1, hd => by
    rw [loop2_succ, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with hlt | rfl
    · exact loop2_true W q Dd B6 d2 e3 cnt h.1 e2 hlt e1 h1 hd
    · exact loop1_true W q Dd B6 d2 e3 e2 (e2 + 1) h.2 e1 (Nat.lt_succ_of_le h1) hd

theorem loop3_succ (W q Dd B6 d2 cnt : ℕ) :
    loop3 W q Dd B6 d2 (cnt + 1) = (loop3 W q Dd B6 d2 cnt && loop2 W q Dd B6 d2 cnt (cnt + 1)) := rfl

/-- The loops test `orbitOk` for all `e1 ≤ e2 ≤ e3 < cnt` with `e1 + e2 + e3 ≤ d2`. -/
theorem loop3_true (W q Dd B6 d2 : ℕ) : ∀ cnt, loop3 W q Dd B6 d2 cnt = true →
    ∀ e3, e3 < cnt → ∀ e2, e2 ≤ e3 → ∀ e1, e1 ≤ e2 → e1 + e2 + e3 ≤ d2 →
      orbitOk W q Dd B6 e1 e2 e3 = true
  | 0, _, e3, h3, _, _, _, _, _ => absurd h3 (Nat.not_lt_zero e3)
  | cnt + 1, h, e3, h3, e2, h2, e1, h1, hd => by
    rw [loop3_succ, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h3 with hlt | rfl
    · exact loop3_true W q Dd B6 d2 cnt h.1 e3 hlt e2 h2 e1 h1 hd
    · exact loop2_true W q Dd B6 d2 e3 (e3 + 1) h.2 e2 (Nat.lt_succ_of_le h2) e1 h1 hd

theorem slotAt_eq (W q Dd x y z : ℕ) : slotAt W q Dd x y z = slot W Dd (x + q * (y + q * z)) := rfl

theorem orbitOk_true {W q Dd B6 e1 e2 e3 : ℕ} (h : orbitOk W q Dd B6 e1 e2 e3 = true) :
    slotAt W q Dd e1 e2 e3 + slotAt W q Dd e1 e3 e2 + slotAt W q Dd e2 e1 e3 + slotAt W q Dd e2 e3 e1
      + slotAt W q Dd e3 e1 e2 + slotAt W q Dd e3 e2 e1 = B6 :=
  Nat.eq_of_beq_eq_true h

/-! ## The digits of the difference -/

/-- The slot of `Fp (X, …) + 2 ^ (W - 1) * (1, …, 1) - Fn (X, …)` at the position of the monomial
`u ^ x * v ^ y * t ^ z`. -/
theorem slot_Dd (W q : ℕ) (hW : 0 < W) (Fp Fn : Poly) (hp : ∀ m ∈ Fp.support, ∀ i, m i < q)
    (hn : ∀ m ∈ Fn.support, ∀ i, m i < q) (cp : ∀ m, coeff m Fp < 2 ^ (W - 1))
    (cn : ∀ m, coeff m Fn < 2 ^ (W - 1)) {x y z : ℕ} (hx : x < q) (hy : y < q) (hz : z < q) :
    slot W (eval (kpt W q) Fp + 2 ^ (W - 1) * ones W (q * (q * q)) - eval (kpt W q) Fn)
        (x + q * (y + q * z))
      = coeff (expo x y z) Fp + 2 ^ (W - 1) - coeff (expo x y z) Fn := by
  have h2 : 2 ^ W = 2 * 2 ^ (W - 1) := two_pow_pred hW
  have e1 : eval (kpt W q) Fp + 2 ^ (W - 1) * ones W (q * (q * q)) =
      packSum W (q * (q * q)) (fun p => coeff (unpos q p) Fp + 2 ^ (W - 1)) := by
    rw [eval_kpt W q Fp hp, ones_eq W _ hW, ← packSum_add_const]
  have e2 : packSum W (q * (q * q)) (fun p => coeff (unpos q p) Fp + 2 ^ (W - 1)) - eval (kpt W q) Fn =
      packSum W (q * (q * q)) (fun p => coeff (unpos q p) Fp + 2 ^ (W - 1) - coeff (unpos q p) Fn) := by
    rw [eval_kpt W q Fn hn]
    exact packSum_sub W _ _ _ (fun p _ => by
      have := cn (unpos q p)
      show coeff (unpos q p) Fn ≤ coeff (unpos q p) Fp + 2 ^ (W - 1)
      omega)
  rw [e1, e2, slot_packSum W _ _ (fun p _ => by
      have := cp (unpos q p)
      show coeff (unpos q p) Fp + 2 ^ (W - 1) - coeff (unpos q p) Fn < 2 ^ W
      omega) _ (digit_lt hx (digit_lt hy hz)), unpos_digits hx hy hz]

/-! ## Sums over the six permutations -/

/-- The sum of `c` over the six permutations of `(x, y, z)`. -/
def orb (c : ℕ → ℕ → ℕ → ℕ) (x y z : ℕ) : ℕ :=
  c x y z + c x z y + c y x z + c y z x + c z x y + c z y x

/-- If two such sums agree for sorted arguments, they agree for all arguments. -/
theorem orb_of_sorted (cp cn : ℕ → ℕ → ℕ → ℕ) (d : ℕ)
    (H : ∀ e1 e2 e3, e1 ≤ e2 → e2 ≤ e3 → e1 + e2 + e3 ≤ d → orb cp e1 e2 e3 = orb cn e1 e2 e3)
    (x y z : ℕ) (h : x + y + z ≤ d) : orb cp x y z = orb cn x y z := by
  rcases le_total x y with hxy | hxy <;> rcases le_total y z with hyz | hyz <;>
    rcases le_total x z with hxz | hxz
  · exact H x y z hxy hyz h
  · exact H x y z hxy hyz h
  · have := H x z y hxz hyz (by omega)
    unfold orb at *
    omega
  · have := H z x y hxz hxy (by omega)
    unfold orb at *
    omega
  · have := H y x z hxy hxz (by omega)
    unfold orb at *
    omega
  · have := H y z x hyz hxz (by omega)
    unfold orb at *
    omega
  · have := H z y x hyz hxy (by omega)
    unfold orb at *
    omega
  · have := H z y x hyz hxy (by omega)
    unfold orb at *
    omega

/-! ## Degrees and exponents -/

theorem expo_degree (x y z : ℕ) : ∑ i ∈ (expo x y z).support, expo x y z i = x + y + z := by
  have h := Finsupp.sum_fintype (expo x y z) (fun _ e => e) (fun _ => rfl)
  unfold Finsupp.sum at h
  rw [h, Fin.sum_univ_three, expo_zero, expo_one, expo_two]

/-- The coefficient of a monomial whose degree exceeds the total degree vanishes. -/
theorem coeff_expo_eq_zero (F : Poly) {d x y z : ℕ} (hF : F.totalDegree ≤ d) (h : d < x + y + z) :
    coeff (expo x y z) F = 0 :=
  coeff_eq_zero_of_totalDegree_lt (by rw [expo_degree]; omega)

/-- Every exponent of a polynomial is at most its total degree. -/
theorem exponent_le (F : Poly) {d : ℕ} (hF : F.totalDegree ≤ d) (m : Fin 3 →₀ ℕ) (hm : m ∈ F.support)
    (i : Fin 3) : m i ≤ d := by
  have h1 : coeff m F ≠ 0 := mem_support_iff.mp hm
  have h2 : m 0 + m 1 + m 2 ≤ d := by
    by_contra hlt
    exact h1 (by
      have := coeff_expo_eq_zero F (x := m 0) (y := m 1) (z := m 2) hF (by omega)
      rwa [expo_eta] at this)
  fin_cases i <;> simp <;> omega

/-! ## The three substitutions and polynomials in `u` -/

/-- The substitution `(u, v, t) ↦ (u, u, 1)`. -/
noncomputable def sub1 : Poly →ₐ[ℕ] Poly := bind₁ ![X 0, X 0, 1]

/-- The substitution `(u, v, t) ↦ (u, 1, u)`. -/
noncomputable def sub2 : Poly →ₐ[ℕ] Poly := bind₁ ![X 0, 1, X 0]

/-- The substitution `(u, v, t) ↦ (1, u, u)`. -/
noncomputable def sub3 : Poly →ₐ[ℕ] Poly := bind₁ ![1, X 0, X 0]

theorem eval_bind₁' (x : Fin 3 → ℕ) (g : Fin 3 → Poly) (F : Poly) :
    eval x (bind₁ g F) = eval (fun i => eval x (g i)) F :=
  eval₂Hom_bind₁ (RingHom.id ℕ) x g F

/-- A substitution of the variables by polynomials of degree at most one does not raise the
total degree. -/
theorem totalDegree_bind₁_le (g : Fin 3 → Poly) (hg : ∀ i, (g i).totalDegree ≤ 1) (F : Poly) :
    (bind₁ g F).totalDegree ≤ F.totalDegree := by
  have h : bind₁ g F = ∑ d ∈ F.support, C (coeff d F) * ∏ i, g i ^ d i := by
    show aeval g F = _
    rw [aeval_def, eval₂_eq']
    rfl
  rw [h]
  refine totalDegree_sum_le _ _ _ fun d hd => ?_
  refine (totalDegree_C_mul_le _ _).trans ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  have h1 : ∀ i : Fin 3, (g i ^ d i).totalDegree ≤ d i := fun i =>
    (totalDegree_pow _ _).trans (by
      have := hg i
      nlinarith)
  refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
  have h2 := le_totalDegree hd
  have h3 := Finsupp.sum_fintype d (fun _ e => e) (fun _ => rfl)
  rw [h3] at h2
  exact h2

/-- The polynomial `∑ d < q, c d • u ^ d`. -/
noncomputable def uPoly (q : ℕ) (c : ℕ → ℕ) : Poly := ∑ d ∈ range q, C (c d) * X 0 ^ d

theorem totalDegree_uPoly (q : ℕ) (c : ℕ → ℕ) : (uPoly q c).totalDegree ≤ q - 1 := by
  refine totalDegree_sum_le _ _ _ fun d hd => ?_
  refine (totalDegree_C_mul_le _ _).trans ?_
  rw [totalDegree_X_pow]
  have := mem_range.mp hd
  omega

theorem csum_uPoly (q : ℕ) (c : ℕ → ℕ) : csum (uPoly q c) = ∑ d ∈ range q, c d := by
  simp [uPoly, csum_X]

end CAP.ThreePoint

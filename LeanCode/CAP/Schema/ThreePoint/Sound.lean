module

public import CAP.Schema.ThreePoint.Semantics

/-!
# Schema S2: soundness of the checker of the three-point identity

**Theorem** (`CAP.ThreePoint.check_sound`). If `CAP.ThreePoint.check P mrows sos Hp cp = true`,
then the polynomial `Z = ZZ P mrows sos Hp cp` in `ℤ[u, v, t]` satisfies

  `∑_σ Z ∘ σ = 0`,

where `σ` runs over the six permutations of the variables (`symm6`). Here

  `Z = (N - 1) * Qh + 9 * (N - 1) * Sh + 9 * x₀ - 9 * (N - 1) * Ĥ(u) + 9 * (N - 1) * ĉ`

with `Qh = 9 * (N - 2) * ∑ₖ φₖ * Qₖ + ∑_B f_B * G_B`, `Sh = M (u, u, 1) + M (u, 1, u) + M (1, u, u)` for
`M = ∑ₖ φₖ * Qₖ`, `x₀` the sum of the entries of the first moment block, `Ĥ(u) = ∑_d Hh d • u ^ d`
and `ĉ = cp`. The polynomials `φₖ`, `Qₖ`, `G_B` are defined in `Semantics.lean`.

The proof combines `check_orbits` (the sums of the coefficients of the two parts of `Z` over the
permutations of a monomial agree) with the comparison of the pairs with these polynomials.
-/

@[expose] public section

namespace CAP.ThreePoint

open MvPolynomial Finset

/-! ## The sum over the six permutations of the variables -/

/-- `∑_σ F ∘ σ` over the six permutations `σ` of the three variables. -/
noncomputable def symm6 {R : Type*} [CommSemiring R] (F : MvPolynomial (Fin 3) R) : MvPolynomial (Fin 3) R :=
  F + rename (Equiv.swap (1 : Fin 3) 2) F + rename (Equiv.swap (0 : Fin 3) 1) F
    + rename (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) F
    + rename (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1) F + rename (Equiv.swap (0 : Fin 3) 2) F

/-- The coefficients of a polynomial whose variables are permuted. -/
theorem coeff_rename_perm {R : Type*} [CommSemiring R] (σ : Equiv.Perm (Fin 3)) (F : MvPolynomial (Fin 3) R)
    (m : Fin 3 →₀ ℕ) : coeff m (rename σ F) = coeff (expo (m (σ 0)) (m (σ 1)) (m (σ 2))) F := by
  have e : Finsupp.mapDomain σ (expo (m (σ 0)) (m (σ 1)) (m (σ 2))) = m := by
    ext i
    rw [Finsupp.mapDomain_equiv_apply]
    obtain ⟨j, rfl⟩ : ∃ j, i = σ j := ⟨σ.symm i, (Equiv.apply_symm_apply σ i).symm⟩
    rw [Equiv.symm_apply_apply]
    fin_cases j <;> simp
  have h := coeff_rename_mapDomain (σ : Fin 3 → Fin 3) σ.injective F (expo (m (σ 0)) (m (σ 1)) (m (σ 2)))
  rw [e] at h
  exact h

/-- The coefficient of `symm6 F` at a monomial is the sum of the coefficients of `F` at the six
permutations of the monomial. -/
theorem coeff_symm6 (F : Poly) (m : Fin 3 →₀ ℕ) : coeff m (symm6 F) = orb (cf F) (m 0) (m 1) (m 2) := by
  have a1 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
  have a2 : (Equiv.swap (1 : Fin 3) 2) 1 = 2 := by decide
  have a3 : (Equiv.swap (1 : Fin 3) 2) 2 = 1 := by decide
  have b1 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
  have b2 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
  have b3 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  have c1 : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) 0 = 1 := by decide
  have c2 : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) 1 = 2 := by decide
  have c3 : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) 2 = 0 := by decide
  have d1 : (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1) 0 = 2 := by decide
  have d2 : (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
  have d3 : (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1) 2 = 1 := by decide
  have e1 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := by decide
  have e2 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
  have e3 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := by decide
  unfold symm6 orb cf
  simp only [coeff_add, coeff_rename_perm, a1, a2, a3, b1, b2, b3, c1, c2, c3, d1, d2, d3, e1, e2, e3]
  rw [expo_eta]

theorem map_symm6 {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (F : MvPolynomial (Fin 3) R) :
    map f (symm6 F) = symm6 (map f F) := by
  unfold symm6
  simp only [map_add, map_rename]

theorem symm6_sub (F G : PolyZ) : symm6 (F - G) = symm6 F - symm6 G := by
  unfold symm6
  simp only [map_sub]
  ring

/-! ## The polynomial `Z` -/

/-- The substitution `(u, v, t) ↦ (u, u, 1)`. -/
noncomputable def s1Z : PolyZ →ₐ[ℤ] PolyZ := bind₁ ![X 0, X 0, 1]

/-- The substitution `(u, v, t) ↦ (u, 1, u)`. -/
noncomputable def s2Z : PolyZ →ₐ[ℤ] PolyZ := bind₁ ![X 0, 1, X 0]

/-- The substitution `(u, v, t) ↦ (1, u, u)`. -/
noncomputable def s3Z : PolyZ →ₐ[ℤ] PolyZ := bind₁ ![1, X 0, X 0]

theorem toZ_sub1 (F : Poly) : toZ (sub1 F) = s1Z (toZ F) := by
  have h : (fun i => map (Nat.castRingHom ℤ) ((![X 0, X 0, 1] : Fin 3 → Poly) i)) = ![X 0, X 0, 1] := by
    funext i
    fin_cases i <;> simp
  show map (Nat.castRingHom ℤ) (bind₁ ![X 0, X 0, 1] F) = bind₁ ![X 0, X 0, 1] (map (Nat.castRingHom ℤ) F)
  rw [map_bind₁, h]

theorem toZ_sub2 (F : Poly) : toZ (sub2 F) = s2Z (toZ F) := by
  have h : (fun i => map (Nat.castRingHom ℤ) ((![X 0, 1, X 0] : Fin 3 → Poly) i)) = ![X 0, 1, X 0] := by
    funext i
    fin_cases i <;> simp
  show map (Nat.castRingHom ℤ) (bind₁ ![X 0, 1, X 0] F) = bind₁ ![X 0, 1, X 0] (map (Nat.castRingHom ℤ) F)
  rw [map_bind₁, h]

theorem toZ_sub3 (F : Poly) : toZ (sub3 F) = s3Z (toZ F) := by
  have h : (fun i => map (Nat.castRingHom ℤ) ((![1, X 0, X 0] : Fin 3 → Poly) i)) = ![1, X 0, X 0] := by
    funext i
    fin_cases i <;> simp
  show map (Nat.castRingHom ℤ) (bind₁ ![1, X 0, X 0] F) = bind₁ ![1, X 0, X 0] (map (Nat.castRingHom ℤ) F)
  rw [map_bind₁, h]

/-- `Ĥ(u) = ∑ d < q, Hh d • u ^ d`, where `Hh d` is slot `d` of `Hp` minus the bias `2 ^ (aH - 1)`. -/
noncomputable def HZ (P : Params) (Hp : ℕ) : PolyZ :=
  ∑ d ∈ range (qOf P), C ((slot P.W Hp d : ℤ) - 2 ^ (P.aH - 1)) * X 0 ^ d

/-- The sum of the entries of the block of order `D + 1` stored in `rows`. -/
def x0Z (P : Params) (rows : ℕ) : ℤ :=
  ∑ i ∈ range (P.D + 1), ∑ s ∈ range (P.D + 1 - i), entZ P (P.D + 1) rows i s

/-- The polynomial `Z` of the statement. -/
noncomputable def ZZ (P : Params) (mrows : List ℕ) (sos : List Sos) (Hp cp : ℕ) : PolyZ :=
  C ((P.N : ℤ) - 1) * (C (9 * ((P.N : ℤ) - 2)) * momentZ P mrows 0 + sosSumZ P sos)
    + C (9 * ((P.N : ℤ) - 1))
      * (s1Z (momentZ P mrows 0) + s2Z (momentZ P mrows 0) + s3Z (momentZ P mrows 0))
    + C (9 * x0Z P (hdNat mrows))
    - C (9 * ((P.N : ℤ) - 1)) * HZ P Hp
    + C (9 * ((P.N : ℤ) - 1) * (cp : ℤ))

theorem csum_phiP (P : Params) (n rows : ℕ) :
    csum (phiP P n rows).1 = ∑ i ∈ range n, ∑ s ∈ range (n - i), triEnt P.w n rows i s ∧
      csum (phiP P n rows).2 = ∑ i ∈ range n, ∑ _s ∈ range (n - i), 2 ^ (P.a - 1) := by
  have h2 : csum 2 = 2 := map_ofNat csum 2
  constructor <;> simp [phiP, csum_X, h2]

theorem toZ_uPoly (q : ℕ) (c : ℕ → ℕ) : toZ (uPoly q c) = ∑ d ∈ range q, C (c d : ℤ) * X 0 ^ d := by
  simp [uPoly, toZ_X]

/-- `Z` is the difference of the two polynomials with natural coefficients. -/
theorem val_Z (P : Params) (mrows : List ℕ) (sos : List Sos) (Hp cp : ℕ) (hN : 3 ≤ P.N) (heb : 2 ≤ P.eb)
    (hcb : 1 ≤ P.cb) : toZ (ZpP P mrows sos cp) - toZ (ZnP P mrows sos Hp) = ZZ P mrows sos Hp cp := by
  have hM : toZ (momentP P mrows).1 - toZ (momentP P mrows).2 = momentZ P mrows 0 :=
    val_momentFrom P heb hcb mrows 0
  have hS : toZ (sosSum P sos).1 - toZ (sosSum P sos).2 = sosSumZ P sos := val_sosSum P sos
  have h1 : toZ (sub1 (momentP P mrows).1) - toZ (sub1 (momentP P mrows).2) = s1Z (momentZ P mrows 0) := by
    rw [toZ_sub1, toZ_sub1, ← map_sub, hM]
  have h2 : toZ (sub2 (momentP P mrows).1) - toZ (sub2 (momentP P mrows).2) = s2Z (momentZ P mrows 0) := by
    rw [toZ_sub2, toZ_sub2, ← map_sub, hM]
  have h3 : toZ (sub3 (momentP P mrows).1) - toZ (sub3 (momentP P mrows).2) = s3Z (momentZ P mrows 0) := by
    rw [toZ_sub3, toZ_sub3, ← map_sub, hM]
  have hx : (C ((9 * csum (phiP P (P.D + 1) (hdNat mrows)).1 : ℕ) : ℤ) : PolyZ)
      - C ((9 * csum (phiP P (P.D + 1) (hdNat mrows)).2 : ℕ) : ℤ) = C (9 * x0Z P (hdNat mrows)) := by
    rw [(csum_phiP P (P.D + 1) (hdNat mrows)).1, (csum_phiP P (P.D + 1) (hdNat mrows)).2, ← map_sub]
    congr 1
    unfold x0Z entZ
    push_cast
    simp only [sum_sub_distrib]
    ring
  have hH : toZ (uPoly (qOf P) (fun _ => 9 * (P.N - 1) * 2 ^ (P.aH - 1)))
      - C ((9 * (P.N - 1) : ℕ) : ℤ) * toZ (uPoly (qOf P) (slot P.W Hp))
      = - (C (9 * ((P.N : ℤ) - 1)) * HZ P Hp) := by
    have hN1 : 1 ≤ P.N := by omega
    rw [toZ_uPoly, toZ_uPoly]
    unfold HZ
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_neg_distrib]
    refine sum_congr rfl fun d _ => ?_
    push_cast [Nat.cast_sub hN1]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    ring
  have hN1 : 1 ≤ P.N := by omega
  have hN2 : 2 ≤ P.N := by omega
  unfold ZpP ZnP ZZ
  simp only [map_add, map_mul, toZ_C]
  push_cast [Nat.cast_sub hN1, Nat.cast_sub hN2] at hx hH ⊢
  simp only [map_mul] at hx hH ⊢
  linear_combination (C ((P.N : ℤ) - 1) * (C 9 * C ((P.N : ℤ) - 2))) * hM + C ((P.N : ℤ) - 1) * hS
    + (C 9 * C ((P.N : ℤ) - 1)) * (h1 + h2 + h3) + hx + hH

/-! ## The theorem -/

/-- **Soundness of the checker of the three-point identity.** If the checker accepts, the sum of
`Z ∘ σ` over the six permutations `σ` of the variables vanishes. -/
theorem check_sound (P : Params) (mrows : List ℕ) (sos : List Sos) (Hp cp : ℕ)
    (h : check P mrows sos Hp cp = true) : symm6 (ZZ P mrows sos Hp cp) = 0 := by
  have F := facts_of_check h
  have hpair : symm6 (ZpP P mrows sos cp) = symm6 (ZnP P mrows sos Hp) := by
    ext m
    rw [coeff_symm6, coeff_symm6]
    exact check_orbits P mrows sos Hp cp h (m 0) (m 1) (m 2)
  rw [← val_Z P mrows sos Hp cp F.hN F.heb F.hcb, symm6_sub]
  show symm6 (map (Nat.castRingHom ℤ) (ZpP P mrows sos cp)) - symm6 (map (Nat.castRingHom ℤ) (ZnP P mrows sos Hp)) = 0
  rw [← map_symm6, ← map_symm6, hpair, sub_self]

end CAP.ThreePoint

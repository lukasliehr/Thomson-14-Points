module

public import N14.Energy.Typed
public import N14.Energy.Pair

/-!
# T7, the certificate of the cap: from a lower bound of the slacks to the energy

The slack functions of the runs of the cap are the slacks of the source minus the threshold of the global runs,
and the slack of the source is nonnegative on the domains, so the slack functions are at least a number `-D`.

* `far_pair_bound`: for three unit vectors with `⟨p, q⟩ ≤ U < 0` and `⟨q, r⟩ ≤ T`, the Gram inequality gives
  `⟨p, r⟩ ≥ L`, if `1 - U² < (L + T)²` and `L + T ≤ 0`. In the cap this is the cut `≥ -0.9416` of the patterns
  `PPR` and `PRR`, which the source states as a consequence of `⟨p, q⟩ ≤ -0.99` and of the bound `0.8` for all
  inner products.
* `dsum_const`: the number of ordered triples of distinct points.
* `TCert.slackOf_ge`: the slacks of all triples are at least `-cM * δ` if the slack functions of the three runs
  are at least `-δ` at the triples of their patterns.
* **`TCert.energy_ge_shift`**: then the energy is at least `en / ed - c1 * δ * N (N - 1) (N - 2) / (6 fS)`; with
  `δ` a natural number `D` this number is `e'n / e'd`, by an equation between natural numbers.
-/

@[expose] public section

namespace N14.Energy

open CAP CAP.ThreePoint N14.Box N14.Ident Finset

/-- **A consequence of the Gram inequality.** -/
theorem far_pair_bound (u a b U T L : ℝ) (hu1 : -1 ≤ u) (hu2 : u ≤ U) (hU : U ≤ 0) (hb2 : b ≤ T)
    (hT : 0 ≤ T) (hLT : L + T ≤ 0) (hnum : 1 - U ^ 2 < (L + T) ^ 2) (hG : 0 ≤ gram u a b) : L ≤ a := by
  by_contra h
  have ha : a < L := not_le.mp h
  have e : gram u a b = (1 - u ^ 2) * (1 - b ^ 2) - (a - u * b) ^ 2 := by
    unfold gram
    ring
  have h1 : (a - u * b) ^ 2 ≤ (1 - u ^ 2) * (1 - b ^ 2) := by linarith
  have hub : -T ≤ u * b := by
    rcases le_total 0 b with hb0 | hb0
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ u + 1) hb0]
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -u) (by linarith : (0 : ℝ) ≤ -b)]
  have h2 : a - u * b < L + T := by linarith
  have h3 : (L + T) ^ 2 < (a - u * b) ^ 2 := by nlinarith
  have hu0 : 0 ≤ 1 - u ^ 2 := by nlinarith
  have h4 : (1 - u ^ 2) * (1 - b ^ 2) ≤ 1 - U ^ 2 := by
    have h5 : (1 - u ^ 2) * (1 - b ^ 2) ≤ 1 - u ^ 2 := by nlinarith [mul_nonneg hu0 (sq_nonneg b)]
    have h6 : U ^ 2 ≤ u ^ 2 := by nlinarith
    linarith
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sum of a constant over the ordered triples of distinct points. -/
theorem dsum_const (c : ℝ) :
    dsum (fun (_ _ _ : ι) => c)
      = c * ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2)) := by
  unfold dsum
  rw [sum3_pairs (fun _ _ => c)]
  have h : (∑ i : ι, ∑ j : ι, if i ≠ j then c else 0) = c * ∑ i : ι, ∑ j : ι, if i ≠ j then (1 : ℝ) else 0 := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [h, sum_ne_one]
  ring

namespace TCert

omit [Fintype ι] in
/-- **A lower bound for the slacks of all triples of a configuration**, from lower bounds of the slack functions
of the three runs at the triples of their patterns. -/
theorem slackOf_ge (C : TCert) (hC : C.Ok) (δ : ℝ) (x : ι → EuclideanSpace ℝ (Fin 3)) (p q : ι)
    (hppr : ∀ k, k ≠ p → k ≠ q → -δ ≤ C.ppr.lam (ip x p q) (ip x p k) (ip x q k))
    (hprr : ∀ i j k, (i = p ∨ i = q) → j ≠ p → j ≠ q → k ≠ p → k ≠ q → j ≠ k →
      -δ ≤ C.prr.lam (ip x i j) (ip x i k) (ip x j k))
    (hrrr : ∀ i j k, i ≠ p → i ≠ q → j ≠ p → j ≠ q → k ≠ p → k ≠ q → Distinct3 i j k →
      -δ ≤ C.rrr.lam (ip x i j) (ip x i k) (ip x j k))
    (i j k : ι) (hd : Distinct3 i j k) :
    -((C.cM : ℝ) * δ) ≤ slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x i j k := by
  have hcM : (0 : ℝ) ≤ C.cM := Nat.cast_nonneg _
  have s12 := slackOf_swap12 C.P C.blk (C.cK : ℝ) C.psi C.psi_symm (tau p q) x
  have s23 := slackOf_swap23 C.P C.blk (C.cK : ℝ) C.psi C.psi_symm (tau p q) x
  have key : ∀ y : ℝ, -δ ≤ y → -((C.cM : ℝ) * δ) ≤ (C.cM : ℝ) * y := fun y hy => by
    have := mul_le_mul_of_nonneg_left hy hcM
    linarith
  have a001 : ∀ i j k, tau p q i = 0 → tau p q j = 0 → tau p q k = 1 → i ≠ j →
      -((C.cM : ℝ) * δ) ≤ slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x i j k := by
    intro i j k hi hj hk hij
    have hk' := tau_one hk
    rcases tau_zero hi with rfl | rfl <;> rcases tau_zero hj with rfl | rfl
    · exact absurd rfl hij
    · rw [C.slackOf_ppr hC _ x _ _ k hi hj hk]
      exact key _ (hppr k hk'.1 hk'.2)
    · rw [s12, C.slackOf_ppr hC _ x _ _ k hj hi hk]
      exact key _ (hppr k hk'.1 hk'.2)
    · exact absurd rfl hij
  have a011 : ∀ i j k, tau p q i = 0 → tau p q j = 1 → tau p q k = 1 → j ≠ k →
      -((C.cM : ℝ) * δ) ≤ slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x i j k := by
    intro i j k hi hj hk hjk
    rw [C.slackOf_prr hC _ x i j k hi hj hk]
    exact key _ (hprr i j k (tau_zero hi) (tau_one hj).1 (tau_one hj).2 (tau_one hk).1 (tau_one hk).2 hjk)
  obtain ⟨hij, hik, hjk⟩ := hd
  rcases tau_cases p q i with hi | hi <;> rcases tau_cases p q j with hj | hj <;>
    rcases tau_cases p q k with hk | hk
  · exact absurd (not_three_of_two (tau_zero hi) (tau_zero hj) (tau_zero hk) ⟨hij, hik, hjk⟩) id
  · exact a001 i j k hi hj hk hij
  · rw [s23]
    exact a001 i k j hi hk hj hik
  · exact a011 i j k hi hj hk hjk
  · rw [s12, s23]
    exact a001 j k i hj hk hi hjk
  · rw [s12]
    exact a011 j i k hj hi hk hik
  · rw [s23, s12]
    exact a011 k i j hk hi hj hij
  · rw [C.slackOf_rrr hC _ x i j k hi hj hk]
    exact key _ (hrrr i j k (tau_one hi).1 (tau_one hi).2 (tau_one hj).1 (tau_one hj).2 (tau_one hk).1
      (tau_one hk).2 ⟨hij, hik, hjk⟩)

/-- **The bound for the energy from a lower bound of the slacks.** If the slack of every triple is at least
`-cM * D`, the energy is at least `e'n / e'd`, the number `en / ed - c1 * D * N (N - 1) (N - 2) / (6 fS)`; the
last hypothesis before the configuration is this equation between natural numbers. -/
theorem energy_ge_shift (C : TCert) (hC : C.Ok) (a1 a2 b1 b2 en ed : ℕ)
    (hz0 : kern C.P ⟨0, 0, 0⟩ 0 C.blocks0 = (a1, a2)) (hz1 : kern C.P ⟨0, 0, 0⟩ 2 C.blocks1 = (b1, b2))
    (hed : 0 < ed) (hfS : 0 < C.fS)
    (hconst : en * (6 * C.cM * C.fS)
        + (2 * C.k00p + 2 * (C.N - 2) * C.k01p + (C.N - 2) * (C.N - 3) * C.k11p
          + 6 * C.c1 * C.cK * (2 * a1 + (C.N - 2) * b1)) * ed
      = (2 * C.k00n + 2 * (C.N - 2) * C.k01n + (C.N - 2) * (C.N - 3) * C.k11n
          + 6 * C.c1 * C.cK * (2 * a2 + (C.N - 2) * b2)) * ed)
    (D e'n e'd : ℕ) (he'd : 0 < e'd)
    (hshift : e'n * (ed * (6 * C.fS)) + C.c1 * D * (C.N * (C.N - 1) * (C.N - 2)) * (e'd * ed)
      = en * (e'd * (6 * C.fS)))
    (x : Fin C.N → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1) (p q : Fin C.N) (hpq : p ≠ q)
    (h : ∀ i j k, Distinct3 i j k →
      -((C.cM : ℝ) * D) ≤ slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x i j k) :
    (e'n : ℝ) / e'd ≤ ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / dist (x i) (x j) := by
  have hmain := C.energy_ge hC a1 a2 b1 b2 en ed hz0 hz1 hed hfS hconst x hx p q hpq
  have hN := hC.hN
  have hN1 : ((C.N - 1 : ℕ) : ℝ) = (C.N : ℝ) - 1 := by exact_mod_cast cast_sub_of_le (by omega : 1 ≤ C.N)
  have hN2 : ((C.N - 2 : ℕ) : ℝ) = (C.N : ℝ) - 2 := by exact_mod_cast cast_sub_of_le (by omega : 2 ≤ C.N)
  have hcard : (Fintype.card (Fin C.N) : ℝ) = C.N := by simp
  -- the sum of the slacks
  have hsum : -((C.cM : ℝ) * D) * ((C.N : ℝ) * ((C.N : ℝ) - 1) * ((C.N : ℝ) - 2))
      ≤ dsum (slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x) := by
    have h1 := dsum_le_dsum (F := fun (_ _ _ : Fin C.N) => -((C.cM : ℝ) * D))
      (G := slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x) (fun i j k hd => h i j k hd)
    rw [dsum_const, hcard] at h1
    exact h1
  have hs := congrArg (Nat.cast (R := ℝ)) hshift
  push_cast at hs
  rw [hN1, hN2] at hs
  have hc1 : (0 : ℝ) ≤ C.c1 := Nat.cast_nonneg _
  have hcM : (0 : ℝ) < C.cM := by exact_mod_cast hC.hcM
  have hfS' : (0 : ℝ) < C.fS := by exact_mod_cast hfS
  have hed' : (0 : ℝ) < ed := by exact_mod_cast hed
  have he'd' : (0 : ℝ) < e'd := by exact_mod_cast he'd
  set K : ℝ := (C.N : ℝ) * ((C.N : ℝ) - 1) * ((C.N : ℝ) - 2) with hK
  set S := dsum (slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x) with hS
  set E := ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / dist (x i) (x j) with hE
  -- the term of the slacks in the bound
  have hterm : -((C.c1 : ℝ) * D * K / (6 * (C.fS : ℝ))) ≤ (C.c1 : ℝ) * S / (6 * (C.cM : ℝ) * (C.fS : ℝ)) := by
    have e1 : -((C.c1 : ℝ) * D * K / (6 * (C.fS : ℝ)))
        = (C.c1 : ℝ) * (-((C.cM : ℝ) * D) * K) / (6 * (C.cM : ℝ) * (C.fS : ℝ)) := by
      field_simp
    rw [e1]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hc1) (by positivity)
  -- the number
  have hnum : (e'n : ℝ) / e'd = (en : ℝ) / ed - (C.c1 : ℝ) * D * K / (6 * (C.fS : ℝ)) := by
    rw [div_eq_iff he'd'.ne']
    field_simp
    linarith
  rw [hnum]
  linarith

end TCert

end N14.Energy

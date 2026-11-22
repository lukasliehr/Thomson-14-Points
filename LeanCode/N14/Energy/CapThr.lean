module

public import N14.Energy.Cap

/-!
# T7, the certificate of the cap: triples with a larger slack

The statements (7.2) and (7.3) of the source give a larger lower bound for the slack of a triple that is far
from the nodes. For a configuration this raises the bound for the energy:

* `dsum_prod3`, `dsum_triple_ge`: a function on the ordered triples of distinct indices that is nonnegative, and
  at least `δ ≥ 0` at the six orders of one triple, has a sum of at least `6 δ`;
* `perm3_of`: a symmetric property of triples that holds for a triple holds for its six orders;
* `TCert.slackOf_ge_on`: the lower bound of `TCert.slackOf_ge` for the triples with a symmetric property `S`,
  from lower bounds of the slack functions of the three runs at the triples of their patterns with `S`;
* **`TCert.energy_ge_gain`**: if the slacks of all triples are at least `-cM * D` and the sum of the slacks plus
  `cM * D` is at least `m * (cM * G)`, the energy is at least `e'n / e'd`, the number
  `en / ed - c1 * D * N (N - 1) (N - 2) / (6 fS) + c1 * G * m / (6 fS)`; the hypothesis `hshift` is this equation
  between natural numbers. With `m = 6` this is the statement for one triple (`energy_far` of the cap), with
  `m = 6 (N - 2)` the statement for the triples through a pair (`dsum_pair_ge`; `energy_loc` of the cap).
-/

@[expose] public section

namespace N14.Energy

open CAP CAP.ThreePoint N14.Box N14.Ident Finset

section counting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sum over the ordered triples of distinct indices of a product of three functions with disjoint
supports. -/
theorem dsum_prod3 (a b c : ι → ℝ) (hab : ∀ i, a i * b i = 0) (hac : ∀ i, a i * c i = 0)
    (hbc : ∀ i, b i * c i = 0) :
    dsum (fun i j k => a i * b j * c k) = (∑ i, a i) * (∑ i, b i) * (∑ i, c i) := by
  unfold dsum
  have e : ∀ i j k, (if Distinct3 i j k then a i * b j * c k else 0) = a i * b j * c k := by
    intro i j k
    by_cases hd : Distinct3 i j k
    · rw [if_pos hd]
    · rw [if_neg hd]
      by_cases h1 : i = j
      · subst h1
        rw [hab i, zero_mul]
      · by_cases h2 : i = k
        · subst h2
          linear_combination (-(b j)) * hac i
        · have h3 : j = k := by
            by_contra h3
            exact hd ⟨h1, h2, h3⟩
          subst h3
          linear_combination (-(a i)) * hbc j
  rw [sum3_congr e]
  unfold sum3
  have e1 : ∀ i j, ∑ k, a i * b j * c k = a i * b j * ∑ k, c k := fun i j => (Finset.mul_sum _ _ _).symm
  simp only [e1]
  have e2 : ∀ i, ∑ j, a i * b j * ∑ k, c k = a i * (∑ j, b j) * ∑ k, c k := fun i => by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp only [e2]
  rw [← Finset.sum_mul, ← Finset.sum_mul]

omit [Fintype ι] in
theorem ind3_le_one (i0 i j k : ι) (hd : Distinct3 i j k) :
    (if i = i0 then (1 : ℝ) else 0) + (if j = i0 then 1 else 0) + (if k = i0 then 1 else 0) ≤ 1 := by
  obtain ⟨hij, hik, hjk⟩ := hd
  by_cases h1 : i = i0
  · have h2 : ¬ j = i0 := fun h2 => hij (h1.trans h2.symm)
    have h3 : ¬ k = i0 := fun h3 => hik (h1.trans h3.symm)
    rw [if_pos h1, if_neg h2, if_neg h3]
    norm_num
  · by_cases h2 : j = i0
    · have h3 : ¬ k = i0 := fun h3 => hjk (h2.trans h3.symm)
      rw [if_neg h1, if_pos h2, if_neg h3]
      norm_num
    · rw [if_neg h1, if_neg h2]
      split_ifs <;> norm_num

omit [Fintype ι] in
theorem ind3_nonneg (i0 i j k : ι) :
    (0 : ℝ) ≤ (if i = i0 then (1 : ℝ) else 0) + (if j = i0 then 1 else 0) + (if k = i0 then 1 else 0) := by
  split_ifs <;> norm_num

omit [Fintype ι] in
theorem ind3_zero (i0 i j k : ι) (h : ¬ (i = i0 ∨ j = i0 ∨ k = i0)) :
    (if i = i0 then (1 : ℝ) else 0) + (if j = i0 then 1 else 0) + (if k = i0 then 1 else 0) = 0 := by
  push Not at h
  rw [if_neg h.1, if_neg h.2.1, if_neg h.2.2]
  norm_num

/-- **The six orders of a triple.** -/
theorem dsum_triple_ge (F : ι → ι → ι → ℝ) (i0 j0 k0 : ι) (hd0 : Distinct3 i0 j0 k0) (δ : ℝ) (hδ : 0 ≤ δ)
    (h0 : ∀ i j k, Distinct3 i j k → 0 ≤ F i j k)
    (h1 : ∀ i j k, Distinct3 i j k → (i = i0 ∨ j = i0 ∨ k = i0) → (i = j0 ∨ j = j0 ∨ k = j0) →
      (i = k0 ∨ j = k0 ∨ k = k0) → δ ≤ F i j k) :
    6 * δ ≤ dsum F := by
  obtain ⟨hij0, hik0, hjk0⟩ := hd0
  set a : ι → ℝ := fun i => if i = i0 then 1 else 0 with ha
  set b : ι → ℝ := fun i => if i = j0 then 1 else 0 with hb
  set c : ι → ℝ := fun i => if i = k0 then 1 else 0 with hc
  have ab : ∀ i, a i * b i = 0 := fun i => by
    by_cases hi : i = i0
    · have hj : ¬ i = j0 := fun hj => hij0 (hi.symm.trans hj)
      simp [hb, hj]
    · simp [ha, hi]
  have ac : ∀ i, a i * c i = 0 := fun i => by
    by_cases hi : i = i0
    · have hj : ¬ i = k0 := fun hj => hik0 (hi.symm.trans hj)
      simp [hc, hj]
    · simp [ha, hi]
  have bc : ∀ i, b i * c i = 0 := fun i => by
    by_cases hi : i = j0
    · have hj : ¬ i = k0 := fun hj => hjk0 (hi.symm.trans hj)
      simp [hc, hj]
    · simp [hb, hi]
  have ba : ∀ i, b i * a i = 0 := fun i => by rw [mul_comm]; exact ab i
  have ca : ∀ i, c i * a i = 0 := fun i => by rw [mul_comm]; exact ac i
  have cb : ∀ i, c i * b i = 0 := fun i => by rw [mul_comm]; exact bc i
  have s1 : ∑ i, a i = 1 := by simp [ha]
  have s2 : ∑ i, b i = 1 := by simp [hb]
  have s3 : ∑ i, c i = 1 := by simp [hc]
  -- the weight of a triple: the product of the three numbers of hits
  have hw : ∀ i j k, (a i + a j + a k) * (b i + b j + b k) * (c i + c j + c k)
      = a i * b j * c k + a i * c j * b k + b i * a j * c k + c i * a j * b k + b i * c j * a k
        + c i * b j * a k := by
    intro i j k
    linear_combination (c i + c j + c k) * (ab i + ab j + ab k) + (b j + b k) * ac i + (b i + b k) * ac j
      + (b i + b j) * ac k + (a j + a k) * bc i + (a i + a k) * bc j + (a i + a j) * bc k
  have hcount : dsum (fun i j k => δ * ((a i + a j + a k) * (b i + b j + b k) * (c i + c j + c k))) = 6 * δ := by
    rw [dsum_smul]
    have e : (fun i j k => (a i + a j + a k) * (b i + b j + b k) * (c i + c j + c k))
        = fun i j k => ((((a i * b j * c k + a i * c j * b k) + b i * a j * c k) + c i * a j * b k)
          + b i * c j * a k) + c i * b j * a k := by
      funext i j k
      rw [hw]
    rw [e, dsum_add, dsum_add, dsum_add, dsum_add, dsum_add, dsum_prod3 a b c ab ac bc,
      dsum_prod3 a c b ac ab cb, dsum_prod3 b a c ba bc ac, dsum_prod3 c a b ca cb ab,
      dsum_prod3 b c a bc ba ca, dsum_prod3 c b a cb ca ba, s1, s2, s3]
    ring
  have hle : dsum (fun i j k => δ * ((a i + a j + a k) * (b i + b j + b k) * (c i + c j + c k))) ≤ dsum F := by
    refine dsum_le_dsum fun i j k hd => ?_
    have hA0 := ind3_nonneg i0 i j k
    have hB0 := ind3_nonneg j0 i j k
    have hC0 := ind3_nonneg k0 i j k
    have hA1 := ind3_le_one i0 i j k hd
    have hB1 := ind3_le_one j0 i j k hd
    have hC1 := ind3_le_one k0 i j k hd
    show δ * ((a i + a j + a k) * (b i + b j + b k) * (c i + c j + c k)) ≤ F i j k
    by_cases c1 : i = i0 ∨ j = i0 ∨ k = i0
    · by_cases c2 : i = j0 ∨ j = j0 ∨ k = j0
      · by_cases c3 : i = k0 ∨ j = k0 ∨ k = k0
        · have hF := h1 i j k hd c1 c2 c3
          have hp : (a i + a j + a k) * (b i + b j + b k) * (c i + c j + c k) ≤ 1 := by
            have h2 : (a i + a j + a k) * (b i + b j + b k) ≤ 1 := by
              calc (a i + a j + a k) * (b i + b j + b k) ≤ 1 * 1 := mul_le_mul hA1 hB1 hB0 (by norm_num)
                _ = 1 := by norm_num
            calc (a i + a j + a k) * (b i + b j + b k) * (c i + c j + c k) ≤ 1 * 1 :=
                  mul_le_mul h2 hC1 hC0 (by norm_num)
              _ = 1 := by norm_num
          calc δ * ((a i + a j + a k) * (b i + b j + b k) * (c i + c j + c k)) ≤ δ * 1 :=
                mul_le_mul_of_nonneg_left hp hδ
            _ ≤ F i j k := by
              rw [mul_one]
              exact hF
        · have z : c i + c j + c k = 0 := ind3_zero k0 i j k c3
          rw [z, mul_zero, mul_zero]
          exact h0 i j k hd
      · have z : b i + b j + b k = 0 := ind3_zero j0 i j k c2
        rw [z, mul_zero, zero_mul, mul_zero]
        exact h0 i j k hd
    · have z : a i + a j + a k = 0 := ind3_zero i0 i j k c1
      rw [z, zero_mul, zero_mul, mul_zero]
      exact h0 i j k hd
  rw [hcount] at hle
  exact hle

omit [Fintype ι] [DecidableEq ι] in
/-- A symmetric property of triples that holds for a triple of distinct indices holds for its six orders. -/
theorem perm3_of (S : ι → ι → ι → Prop) (hS12 : ∀ i j k, S i j k → S j i k) (hS23 : ∀ i j k, S i j k → S i k j)
    (i0 j0 k0 : ι) (hd0 : Distinct3 i0 j0 k0) (hS : S i0 j0 k0) (i j k : ι)
    (c1 : i = i0 ∨ j = i0 ∨ k = i0) (c2 : i = j0 ∨ j = j0 ∨ k = j0) (c3 : i = k0 ∨ j = k0 ∨ k = k0) :
    S i j k := by
  obtain ⟨hij0, hik0, hjk0⟩ := hd0
  rcases c1 with rfl | rfl | rfl <;> rcases c2 with rfl | rfl | rfl <;> rcases c3 with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hij0
    | exact absurd rfl hik0
    | exact absurd rfl hjk0
    | exact hS
    | exact hS12 _ _ _ hS
    | exact hS23 _ _ _ hS
    | exact hS12 _ _ _ (hS23 _ _ _ hS)
    | exact hS23 _ _ _ (hS12 _ _ _ hS)
    | exact hS12 _ _ _ (hS23 _ _ _ (hS12 _ _ _ hS))

end counting

namespace TCert

variable {ι : Type*} [DecidableEq ι]

/-- **A lower bound for the slacks of the triples with a symmetric property `S`**, from lower bounds of the slack
functions of the three runs at the triples of their patterns with this property. -/
theorem slackOf_ge_on (C : TCert) (hC : C.Ok) (γ : ℝ) (x : ι → EuclideanSpace ℝ (Fin 3)) (p q : ι)
    (S : ι → ι → ι → Prop) (hS12 : ∀ i j k, S i j k → S j i k) (hS23 : ∀ i j k, S i j k → S i k j)
    (hppr : ∀ k, k ≠ p → k ≠ q → S p q k → -γ ≤ C.ppr.lam (ip x p q) (ip x p k) (ip x q k))
    (hprr : ∀ i j k, (i = p ∨ i = q) → j ≠ p → j ≠ q → k ≠ p → k ≠ q → j ≠ k → S i j k →
      -γ ≤ C.prr.lam (ip x i j) (ip x i k) (ip x j k))
    (hrrr : ∀ i j k, i ≠ p → i ≠ q → j ≠ p → j ≠ q → k ≠ p → k ≠ q → Distinct3 i j k → S i j k →
      -γ ≤ C.rrr.lam (ip x i j) (ip x i k) (ip x j k))
    (i j k : ι) (hd : Distinct3 i j k) (hS : S i j k) :
    -((C.cM : ℝ) * γ) ≤ slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x i j k := by
  have hcM : (0 : ℝ) ≤ C.cM := Nat.cast_nonneg _
  have s12 := slackOf_swap12 C.P C.blk (C.cK : ℝ) C.psi C.psi_symm (tau p q) x
  have s23 := slackOf_swap23 C.P C.blk (C.cK : ℝ) C.psi C.psi_symm (tau p q) x
  have key : ∀ y : ℝ, -γ ≤ y → -((C.cM : ℝ) * γ) ≤ (C.cM : ℝ) * y := fun y hy => by
    have := mul_le_mul_of_nonneg_left hy hcM
    linarith
  have a001 : ∀ i j k, tau p q i = 0 → tau p q j = 0 → tau p q k = 1 → i ≠ j → S i j k →
      -((C.cM : ℝ) * γ) ≤ slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x i j k := by
    intro i j k hi hj hk hij hS'
    have hk' := tau_one hk
    rcases tau_zero hi with rfl | rfl <;> rcases tau_zero hj with rfl | rfl
    · exact absurd rfl hij
    · rw [C.slackOf_ppr hC _ x _ _ k hi hj hk]
      exact key _ (hppr k hk'.1 hk'.2 hS')
    · rw [s12, C.slackOf_ppr hC _ x _ _ k hj hi hk]
      exact key _ (hppr k hk'.1 hk'.2 (hS12 _ _ _ hS'))
    · exact absurd rfl hij
  have a011 : ∀ i j k, tau p q i = 0 → tau p q j = 1 → tau p q k = 1 → j ≠ k → S i j k →
      -((C.cM : ℝ) * γ) ≤ slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x i j k := by
    intro i j k hi hj hk hjk hS'
    rw [C.slackOf_prr hC _ x i j k hi hj hk]
    exact key _ (hprr i j k (tau_zero hi) (tau_one hj).1 (tau_one hj).2 (tau_one hk).1 (tau_one hk).2 hjk hS')
  obtain ⟨hij, hik, hjk⟩ := hd
  rcases tau_cases p q i with hi | hi <;> rcases tau_cases p q j with hj | hj <;>
    rcases tau_cases p q k with hk | hk
  · exact absurd (not_three_of_two (tau_zero hi) (tau_zero hj) (tau_zero hk) ⟨hij, hik, hjk⟩) id
  · exact a001 i j k hi hj hk hij hS
  · rw [s23]
    exact a001 i k j hi hk hj hik (hS23 _ _ _ hS)
  · exact a011 i j k hi hj hk hjk hS
  · rw [s12, s23]
    exact a001 j k i hj hk hi hjk (hS23 _ _ _ (hS12 _ _ _ hS))
  · rw [s12]
    exact a011 j i k hj hi hk hik (hS12 _ _ _ hS)
  · rw [s23, s12]
    exact a011 k i j hk hi hj hij (hS12 _ _ _ (hS23 _ _ _ hS))
  · rw [C.slackOf_rrr hC _ x i j k hi hj hk]
    exact key _ (hrrr i j k (tau_one hi).1 (tau_one hi).2 (tau_one hj).1 (tau_one hj).2 (tau_one hk).1
      (tau_one hk).2 ⟨hij, hik, hjk⟩ hS)

/-- **The bound for the energy with a gain.** If the sum of the slacks plus `cM * D`, over the ordered triples
of distinct points, is at least `m * (cM * G)`, the energy is at least `e'n / e'd`, the number
`en / ed - c1 * D * N (N - 1) (N - 2) / (6 fS) + c1 * G * m / (6 fS)`. -/
theorem energy_ge_gain (C : TCert) (hC : C.Ok) (a1 a2 b1 b2 en ed : ℕ)
    (hz0 : kern C.P ⟨0, 0, 0⟩ 0 C.blocks0 = (a1, a2)) (hz1 : kern C.P ⟨0, 0, 0⟩ 2 C.blocks1 = (b1, b2))
    (hed : 0 < ed) (hfS : 0 < C.fS)
    (hconst : en * (6 * C.cM * C.fS)
        + (2 * C.k00p + 2 * (C.N - 2) * C.k01p + (C.N - 2) * (C.N - 3) * C.k11p
          + 6 * C.c1 * C.cK * (2 * a1 + (C.N - 2) * b1)) * ed
      = (2 * C.k00n + 2 * (C.N - 2) * C.k01n + (C.N - 2) * (C.N - 3) * C.k11n
          + 6 * C.c1 * C.cK * (2 * a2 + (C.N - 2) * b2)) * ed)
    (D G m e'n e'd : ℕ) (he'd : 0 < e'd)
    (hshift : e'n * (ed * (6 * C.fS)) + C.c1 * D * (C.N * (C.N - 1) * (C.N - 2)) * (e'd * ed)
      = en * (e'd * (6 * C.fS)) + C.c1 * G * m * (e'd * ed))
    (x : Fin C.N → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1) (p q : Fin C.N) (hpq : p ≠ q)
    (hgain : (m : ℝ) * ((C.cM : ℝ) * G)
      ≤ dsum (fun i j k => slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x i j k + (C.cM : ℝ) * D)) :
    (e'n : ℝ) / e'd ≤ ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / dist (x i) (x j) := by
  have hmain := C.energy_ge hC a1 a2 b1 b2 en ed hz0 hz1 hed hfS hconst x hx p q hpq
  have hN := hC.hN
  have hN1 : ((C.N - 1 : ℕ) : ℝ) = (C.N : ℝ) - 1 := by exact_mod_cast cast_sub_of_le (by omega : 1 ≤ C.N)
  have hN2 : ((C.N - 2 : ℕ) : ℝ) = (C.N : ℝ) - 2 := by exact_mod_cast cast_sub_of_le (by omega : 2 ≤ C.N)
  have hcard : (Fintype.card (Fin C.N) : ℝ) = C.N := by simp
  set K : ℝ := (C.N : ℝ) * ((C.N : ℝ) - 1) * ((C.N : ℝ) - 2) with hK
  set S := dsum (slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x) with hS
  set E := ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / dist (x i) (x j) with hE
  have hsum : (m : ℝ) * ((C.cM : ℝ) * G) ≤ S + (C.cM : ℝ) * D * K := by
    have e : dsum (fun i j k => slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x i j k + (C.cM : ℝ) * D)
        = S + (C.cM : ℝ) * D * K := by
      rw [dsum_add (slackOf C.P C.blk (C.cK : ℝ) C.psi (tau p q) x) (fun _ _ _ => (C.cM : ℝ) * D),
        dsum_const, hcard]
    rw [e] at hgain
    exact hgain
  have hs := congrArg (Nat.cast (R := ℝ)) hshift
  push_cast at hs
  rw [hN1, hN2] at hs
  have hc1 : (0 : ℝ) ≤ C.c1 := Nat.cast_nonneg _
  have hcM : (0 : ℝ) < C.cM := by exact_mod_cast hC.hcM
  have hfS' : (0 : ℝ) < C.fS := by exact_mod_cast hfS
  have hed' : (0 : ℝ) < ed := by exact_mod_cast hed
  have he'd' : (0 : ℝ) < e'd := by exact_mod_cast he'd
  have hterm : (C.c1 : ℝ) * ((m : ℝ) * G - D * K) / (6 * (C.fS : ℝ))
      ≤ (C.c1 : ℝ) * S / (6 * (C.cM : ℝ) * (C.fS : ℝ)) := by
    have e1 : (C.c1 : ℝ) * ((m : ℝ) * G - D * K) / (6 * (C.fS : ℝ))
        = (C.c1 : ℝ) * ((m : ℝ) * ((C.cM : ℝ) * G) - (C.cM : ℝ) * D * K) / (6 * (C.cM : ℝ) * (C.fS : ℝ)) := by
      field_simp
    rw [e1]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hc1) (by positivity)
  have hnum : (e'n : ℝ) / e'd = (en : ℝ) / ed + (C.c1 : ℝ) * ((m : ℝ) * G - D * K) / (6 * (C.fS : ℝ)) := by
    rw [div_eq_iff he'd'.ne']
    field_simp
    linarith
  rw [hnum]
  linarith

end TCert

end N14.Energy

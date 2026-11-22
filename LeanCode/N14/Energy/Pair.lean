module

public import N14.Energy.Untyped

/-!
# T7, a displaced pair: twelve triples share the excess of the energy

The certificate of Case 0 (and, with types, of Case III) is used through a counting argument: if the inner
product of one pair of points lies in a region where the slack is at least `δ`, then each of the `N - 2` triples
through this pair has a slack of at least `δ`, and all other slacks are nonnegative.

* `dsum_pair_ge`: a function on the ordered triples of distinct indices that is nonnegative, and at least
  `δ ≥ 0` at the triples that contain two given indices, has a sum of at least `6 * (N - 2) * δ`.
* `UCert.lam_sub`: two certificates with the same kernels (two runs of one certificate of the source, with
  different thresholds) have slack functions that differ by a constant, which the two pair identities give.
* `UCert.energy_pair`: the bound for the energy of a configuration with a pair in the region of the second run.
-/

@[expose] public section

namespace N14.Energy

open CAP CAP.ThreePoint N14.Box N14.Ident Finset

section counting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sum over the ordered triples of distinct indices of a function of the three pairs of a triple. -/
theorem dsum_three_pairs (p : ι → ι → ℝ) :
    dsum (fun i j k => p i j + p i k + p j k)
      = 3 * (((Fintype.card ι : ℝ) - 2) * ∑ i, ∑ j, if i ≠ j then p i j else 0) := by
  have e1 : dsum (fun i j k => p i k) = dsum (fun i j _ => p i j) := dsum_swap23 (fun i j _ => p i j)
  have e2 : dsum (fun i j k => p j k) = dsum (fun i j _ => p i j) := dsum_perm231 (fun i j _ => p i j)
  have e3 : dsum (fun i j _ => p i j) = ((Fintype.card ι : ℝ) - 2) * ∑ i, ∑ j, if i ≠ j then p i j else 0 :=
    sum3_pairs p
  rw [dsum_add (fun i j k => p i j + p i k) (fun i j k => p j k),
    dsum_add (fun i j _ => p i j) (fun i j k => p i k), e1, e2, e3]
  ring

/-- A sum over triples is monotone on the triples of distinct indices. -/
theorem dsum_le_dsum {F G : ι → ι → ι → ℝ} (h : ∀ i j k, Distinct3 i j k → F i j k ≤ G i j k) : dsum F ≤ dsum G := by
  unfold dsum sum3
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun k _ => ?_
  show (if Distinct3 i j k then F i j k else 0) ≤ (if Distinct3 i j k then G i j k else 0)
  split_ifs with hd
  · exact h i j k hd
  · exact le_refl 0

/-- **Twelve triples through a pair.** -/
theorem dsum_pair_ge (F : ι → ι → ι → ℝ) (i0 j0 : ι) (h : i0 ≠ j0) (δ : ℝ) (hδ : 0 ≤ δ)
    (h0 : ∀ i j k, Distinct3 i j k → 0 ≤ F i j k)
    (h1 : ∀ i j k, Distinct3 i j k → (i = i0 ∨ j = i0 ∨ k = i0) → (i = j0 ∨ j = j0 ∨ k = j0) → δ ≤ F i j k) :
    6 * ((Fintype.card ι : ℝ) - 2) * δ ≤ dsum F := by
  -- the indicators of the two indices
  set a : ι → ℝ := fun i => if i = i0 then 1 else 0 with ha
  set b : ι → ℝ := fun i => if i = j0 then 1 else 0 with hb
  have a01 : ∀ i, a i = 0 ∨ a i = 1 := fun i => by
    by_cases hi : i = i0
    · exact Or.inr (if_pos hi)
    · exact Or.inl (if_neg hi)
  have b01 : ∀ i, b i = 0 ∨ b i = 1 := fun i => by
    by_cases hi : i = j0
    · exact Or.inr (if_pos hi)
    · exact Or.inl (if_neg hi)
  have aa : ∀ i j, i ≠ j → a i * a j = 0 := fun i j hij => by
    by_cases hi : i = i0
    · have hj : ¬ j = i0 := fun hj => hij (hi.trans hj.symm)
      simp [ha, hj]
    · simp [ha, hi]
  have bb : ∀ i j, i ≠ j → b i * b j = 0 := fun i j hij => by
    by_cases hi : i = j0
    · have hj : ¬ j = j0 := fun hj => hij (hi.trans hj.symm)
      simp [hb, hj]
    · simp [hb, hi]
  have ab : ∀ i, a i * b i = 0 := fun i => by
    by_cases hi : i = i0
    · have hj : ¬ i = j0 := fun hj => h (hi.symm.trans hj)
      simp [hb, hj]
    · simp [ha, hi]
  -- the pairs
  have hsum : (∑ i, ∑ j, if i ≠ j then δ * (a i * b j + b i * a j) else 0) = 2 * δ := by
    have e : ∀ i j, (if i ≠ j then δ * (a i * b j + b i * a j) else 0)
        = δ * (a i * b j) + δ * (b i * a j) := by
      intro i j
      by_cases hij : i = j
      · subst hij
        rw [if_neg (fun hh => hh rfl), ab i, mul_comm (b i) (a i), ab i]
        ring
      · rw [if_pos hij]
        ring
    simp only [e, sum_add_distrib, ← mul_sum]
    have s1 : ∑ i, a i = 1 := by simp [ha]
    have s2 : ∑ i, b i = 1 := by simp [hb]
    have t1 : ∑ i, ∑ j, a i * b j = 1 := by
      rw [← sum_mul_sum, s1, s2, one_mul]
    have t2 : ∑ i, ∑ j, b i * a j = 1 := by
      rw [← sum_mul_sum, s1, s2, one_mul]
    simp only [← mul_sum] at t1 t2 ⊢
    rw [t1, t2]
    ring
  have hle : dsum (fun i j k => δ * (a i * b j + b i * a j) + δ * (a i * b k + b i * a k)
      + δ * (a j * b k + b j * a k)) ≤ dsum F := by
    refine dsum_le_dsum fun i j k hd => ?_
    obtain ⟨hij, hik, hjk⟩ := hd
    -- the sum of the three pairs is the product of the two numbers of hits
    have hs : (a i * b j + b i * a j) + (a i * b k + b i * a k) + (a j * b k + b j * a k)
        = (a i + a j + a k) * (b i + b j + b k) := by
      have := ab i
      have := ab j
      have := ab k
      nlinarith
    have sq : ∀ (c : ι → ℝ), (∀ i, c i = 0 ∨ c i = 1) → ∀ i, c i * c i = c i := fun c hc i => by
      rcases hc i with x | x <;> simp [x]
    have nn : ∀ (c : ι → ℝ), (∀ i, c i = 0 ∨ c i = 1) → ∀ i, 0 ≤ c i := fun c hc i => by
      rcases hc i with x | x <;> simp [x]
    have hA : (a i + a j + a k) * (a i + a j + a k) = a i + a j + a k := by
      linear_combination sq a a01 i + sq a a01 j + sq a a01 k + 2 * aa i j hij + 2 * aa i k hik + 2 * aa j k hjk
    have hB : (b i + b j + b k) * (b i + b j + b k) = b i + b j + b k := by
      linear_combination sq b b01 i + sq b b01 j + sq b b01 k + 2 * bb i j hij + 2 * bb i k hik + 2 * bb j k hjk
    have hAn : 0 ≤ a i + a j + a k := by
      have := nn a a01 i
      have := nn a a01 j
      have := nn a a01 k
      linarith
    have hBn : 0 ≤ b i + b j + b k := by
      have := nn b b01 i
      have := nn b b01 j
      have := nn b b01 k
      linarith
    have hA1 : a i + a j + a k ≤ 1 := by nlinarith
    have hB1 : b i + b j + b k ≤ 1 := by nlinarith
    have e : δ * (a i * b j + b i * a j) + δ * (a i * b k + b i * a k) + δ * (a j * b k + b j * a k)
        = δ * ((a i + a j + a k) * (b i + b j + b k)) := by
      rw [← hs]
      ring
    rw [e]
    by_cases c1 : i = i0 ∨ j = i0 ∨ k = i0
    · by_cases c2 : i = j0 ∨ j = j0 ∨ k = j0
      · have hF := h1 i j k ⟨hij, hik, hjk⟩ c1 c2
        have hp : (a i + a j + a k) * (b i + b j + b k) ≤ 1 := by nlinarith
        nlinarith
      · push Not at c2
        have z : b i + b j + b k = 0 := by simp [hb, c2.1, c2.2.1, c2.2.2]
        rw [z, mul_zero, mul_zero]
        exact h0 i j k ⟨hij, hik, hjk⟩
    · push Not at c1
      have z : a i + a j + a k = 0 := by simp [ha, c1.1, c1.2.1, c1.2.2]
      rw [z, zero_mul, mul_zero]
      exact h0 i j k ⟨hij, hik, hjk⟩
  have hcount := dsum_three_pairs (fun i j => δ * (a i * b j + b i * a j))
  rw [hsum] at hcount
  rw [hcount] at hle
  linarith

end counting

namespace UCert

/-- **Two runs of one certificate.** If two certificates have the same kernels, factors, number of points and
Coulomb weights, their slack functions differ by a constant. -/
theorem lam_sub (C C' : UCert) (hC : C.Ok) (hC' : C'.Ok) (hP : C'.P = C.P) (hb : C'.blocks = C.blocks)
    (hcM : C'.cM = C.cM) (hcK : C'.cK = C.cK) (hN : C'.N = C.N) (hc1 : C'.U1.c1 = C.U1.c1) (hfS : C'.fS = C.fS)
    (u v t : ℝ) :
    (C.cM : ℝ) * (C.lam u v t - C'.lam u v t)
      = (((C.kp : ℝ) - C.kn) - ((C'.kp : ℝ) - C'.kn)) / (C.U1.c1 : ℝ) / ((C.N : ℝ) - 2) := by
  have hN2 : (0 : ℝ) < (C.N : ℝ) - 2 := by
    have : (3 : ℝ) ≤ (C.N : ℝ) := by exact_mod_cast hC.hN
    linarith
  have hk : ∀ a b c : ℝ, C'.ker a b c = C.ker a b c := fun a b c => by
    unfold ker
    rw [hP, hb]
  -- the functions of one variable differ by a constant
  have hpsi : ∀ s : ℝ, C.psi s - C'.psi s
      = (((C.kp : ℝ) - C.kn) - ((C'.kp : ℝ) - C'.kn)) / (C.U1.c1 : ℝ) / ((C.N : ℝ) - 2) / 3 := by
    intro s
    have h1 := C.pair_eq hC s
    have h2 := C'.pair_eq hC' s
    rw [hk, hk, hk, hcM, hcK, hN, hc1, hfS] at h2
    have e : 3 * (((C.N : ℝ) - 2) * (C.psi s - C'.psi s))
        = ((C.kp : ℝ) - C.kn) / (C.U1.c1 : ℝ) - ((C'.kp : ℝ) - C'.kn) / (C.U1.c1 : ℝ) := by
      linear_combination h1 - h2
    field_simp
    field_simp at e
    linear_combination e
  have s1 := C.slack_eq hC u v t
  have s2 := C'.slack_eq hC' u v t
  rw [hk, hk, hk, hk, hk, hk, hcM, hcK] at s2
  have e : (C.cM : ℝ) * (C.lam u v t - C'.lam u v t)
      = (C.psi u - C'.psi u) + (C.psi v - C'.psi v) + (C.psi t - C'.psi t) := by
    linear_combination s1 - s2
  rw [e, hpsi, hpsi, hpsi]
  ring

/-- **The bound for the energy of a configuration with a displaced pair.** `C` and `C'` are two runs of one
certificate: the slack function of `C` is nonnegative at all triples, and that of `C'` (the same function minus
a threshold) at the triples through the pair `i0`, `j0`. The number `tn / td` is the offset `en / ed` of `C` plus
`N - 2` times the threshold, in the units of the energy; both are given by equations between natural numbers. -/
theorem energy_pair (C C' : UCert) (hC : C.Ok) (hC' : C'.Ok) (hP : C'.P = C.P) (hb : C'.blocks = C.blocks)
    (hcM : C'.cM = C.cM) (hcK : C'.cK = C.cK) (hN : C'.N = C.N) (hc1 : C'.U1.c1 = C.U1.c1) (hfS : C'.fS = C.fS)
    (z1 z2 en ed tn td : ℕ) (hz : kern C.P ⟨0, 0, 0⟩ 0 C.blocks = (z1, z2)) (hed : 0 < ed) (htd : 0 < td)
    (hfSpos : 0 < C.fS)
    (hconst : en * (6 * C.cM * C.fS) + (C.N * (C.N - 1) * C.kp + 6 * C.U1.c1 * C.cK * C.N * z1) * ed
      = (C.N * (C.N - 1) * C.kn + 6 * C.U1.c1 * C.cK * C.N * z2) * ed)
    (hδ : C.kn + C'.kp ≤ C.kp + C'.kn)
    (hfinal : tn * (ed * (C.cM * C.fS)) + (C.kn + C'.kp) * (ed * td)
      = en * (td * (C.cM * C.fS)) + (C.kp + C'.kn) * (ed * td))
    (x : Fin C.N → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1) (i0 j0 : Fin C.N) (h : i0 ≠ j0)
    (h0 : ∀ i j k, Distinct3 i j k → 0 ≤ C.lam (ip x i j) (ip x i k) (ip x j k))
    (h1 : ∀ i j k, Distinct3 i j k → (i = i0 ∨ j = i0 ∨ k = i0) → (i = j0 ∨ j = j0 ∨ k = j0) →
      0 ≤ C'.lam (ip x i j) (ip x i k) (ip x j k)) :
    (tn : ℝ) / td ≤ ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / dist (x i) (x j) := by
  have hc1' : (0 : ℝ) < C.U1.c1 := by exact_mod_cast hC.hc1
  have hcM' : (0 : ℝ) < C.cM := by exact_mod_cast hC.hcM
  have hfS' : (0 : ℝ) < C.fS := by exact_mod_cast hfSpos
  have hed' : (0 : ℝ) < ed := by exact_mod_cast hed
  have htd' : (0 : ℝ) < td := by exact_mod_cast htd
  have hN2 : (0 : ℝ) < (C.N : ℝ) - 2 := by
    have : (3 : ℝ) ≤ (C.N : ℝ) := by exact_mod_cast hC.hN
    linarith
  -- the constant by which the two slack functions differ
  set K : ℝ := ((C.kp : ℝ) - C.kn) - ((C'.kp : ℝ) - C'.kn) with hK
  have hK0 : 0 ≤ K := by
    have := (Nat.cast_le (α := ℝ)).mpr hδ
    push_cast at this
    rw [hK]
    linarith
  set δ : ℝ := K / (C.U1.c1 : ℝ) / ((C.N : ℝ) - 2) / (C.cM : ℝ) with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hlam : ∀ u v t : ℝ, C.lam u v t = C'.lam u v t + δ := by
    intro u v t
    have hs := lam_sub C C' hC hC' hP hb hcM hcK hN hc1 hfS u v t
    rw [hδdef, hK]
    field_simp
    field_simp at hs
    linear_combination hs
  have hD := dsum_pair_ge (fun i j k => C.lam (ip x i j) (ip x i k) (ip x j k)) i0 j0 h δ hδ0 h0
    (fun i j k hd c1 c2 => by
      show δ ≤ C.lam (ip x i j) (ip x i k) (ip x j k)
      rw [hlam]
      have := h1 i j k hd c1 c2
      linarith)
  have hcard : (Fintype.card (Fin C.N) : ℝ) = C.N := by simp
  rw [hcard] at hD
  have hge := C.energy_ge hC z1 z2 en ed hz hed hfSpos hconst x hx
  -- the number `tn / td`
  have hf := congrArg (Nat.cast (R := ℝ)) hfinal
  push_cast at hf
  have etn : (tn : ℝ) / td = (en : ℝ) / ed + K / ((C.cM : ℝ) * (C.fS : ℝ)) := by
    rw [hK]
    field_simp
    linear_combination hf
  have hstep : K / ((C.cM : ℝ) * (C.fS : ℝ))
      ≤ (C.U1.c1 : ℝ) * dsum (fun i j k => C.lam (ip x i j) (ip x i k) (ip x j k)) / (6 * (C.fS : ℝ)) := by
    have e : K / ((C.cM : ℝ) * (C.fS : ℝ)) = (C.U1.c1 : ℝ) * (6 * ((C.N : ℝ) - 2) * δ) / (6 * (C.fS : ℝ)) := by
      rw [hδdef]
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hD hc1'.le) (by positivity)
  rw [etn]
  linarith

end UCert

end N14.Energy

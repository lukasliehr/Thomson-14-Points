module

public import N14.Energy.Link

/-!
# T7, a certificate with one type of points: the bound for the energy from its slack function

**Data** (`UCert`). The blocks of the kernel, a run of `N14.Box` with the tables of its three coordinates, the
number `N` of points, and the numbers of the two identities: the factors `cM`, `cK`, one polynomial `B` of one
variable for all three slots, the constant `cp - cn` of the run, the constant `kp - kn` of the pair identity and
the sum `fS` of the numerators of the Coulomb terms. `UCert.id3` and `UCert.id1` are the data of the two checkers
of `N14.Ident` for it: the identity of the run with the six kernels of a triple, and the identity of a pair with
the multiplicity `N - 2`.

**Theorems.** If both checkers accept, the blocks are positive definite and the three tables have the same
function (`UCert.Ok`), then

* `UCert.slack_eq`: `cM * λ (u, v, t) = ψ (u) + ψ (v) + ψ (t) - cK * (the six kernels)` for the slack function
  `λ = slackFn` of the run, at all real points;
* `UCert.lam_swap12`, `UCert.lam_swap23`: `λ` is symmetric in its three arguments;
* **`UCert.energy`**: for `N` points of the unit sphere of `ℝ³`,

    `cM * ∑ λ ≤ (3 * cM * fS / c1) * ∑_{i ≠ j} (2 - 2 ⟨x i, x j⟩) ^ (-1/2) + N * (N - 1) * (kp - kn) / c1`
        `+ 6 * cK * N * K (1, 1, 1)`,

  where the first sum runs over the ordered triples of distinct points.

`ge_of_sorted` reduces a lower bound for a symmetric function to arguments in increasing order.
-/

@[expose] public section

namespace N14.Energy

open CAP CAP.ThreePoint N14.Box N14.Ident Finset

/-- The six kernels that contain the three points of a triple, for one type of points: the kernel with the
three variables in all orders. -/
def six (blocks : List Blk) : List Term :=
  [⟨blocks, 0, 0, 1, 2⟩, ⟨blocks, 0, 1, 0, 2⟩, ⟨blocks, 0, 0, 2, 1⟩, ⟨blocks, 0, 2, 0, 1⟩, ⟨blocks, 0, 1, 2, 0⟩,
    ⟨blocks, 0, 2, 1, 0⟩]

/-- The data of a certificate with one type of points. -/
structure UCert where
  P : ThreePoint.Params
  blocks : List Blk
  R : Run
  U1 : Tab
  U2 : Tab
  U3 : Tab
  N : ℕ
  cM : ℕ
  cK : ℕ
  wB : ℕ
  aB : ℕ
  B : ℕ
  cp : ℕ
  cn : ℕ
  kp : ℕ
  kn : ℕ
  fS : ℕ

namespace UCert

/-- The data of the identity of the run. -/
def id3 (C : UCert) : Id3 :=
  { n := C.R.n, aH := C.R.aH, PpM := C.R.PpM, cM := C.cM, cK := C.cK, terms := six C.blocks, wB := C.wB,
    aB := C.aB, B0 := C.B, B1 := C.B, B2 := C.B, cp := C.cp, cn := C.cn }

/-- The slot of a pair: every pair has `N - 2` third points. -/
def slot (C : UCert) : Slot := ⟨C.N - 2, C.U1, C.B, C.cp, C.cn⟩

/-- The data of the identity of a pair. -/
def id1 (C : UCert) : Id1 :=
  { n := C.R.n, wB := C.wB, aB := C.aB, cM := C.cM, cK := C.cK, c1 := C.U1.c1, shares := [C.slot.share],
    terms := [⟨C.blocks, 0, 0⟩, ⟨C.blocks, 0, 1⟩, ⟨C.blocks, 0, 2⟩], kp := C.kp, kn := C.kn, fS := C.fS }

/-- What the kernel verifies for the certificate, and what the statement module supplies. -/
structure Ok (C : UCert) : Prop where
  h3 : id3Ok C.P C.id3 = true
  h1 : id1Ok C.P C.id1 = true
  hW : C.P.W = C.R.V
  hPD : BlkPD C.P C.blocks
  hc1 : 0 < C.U1.c1
  hcM : 0 < C.cM
  hN : 3 ≤ C.N
  hT2 : ∀ s, tabFn C.U2 s = tabFn C.U1 s
  hT3 : ∀ s, tabFn C.U3 s = tabFn C.U1 s

/-- The slack function of the certificate, in the units of the run. -/
noncomputable def lam (C : UCert) (u v t : ℝ) : ℝ := slackFn C.R C.U1 C.U2 C.U3 u v t

/-- The function of one variable of the three slots. -/
noncomputable def psi (C : UCert) (s : ℝ) : ℝ := psiOf C.cM C.wB C.aB C.R.n C.U1 C.B C.cp C.cn s

/-- The kernel. -/
noncomputable def ker (C : UCert) (u v t : ℝ) : ℝ := kerR C.P C.blocks 0 0 0 u v t

theorem blocks_n0 (C : UCert) (hC : C.Ok) : ∀ B ∈ C.blocks, B.n0 ≤ B.N := by
  have F := facts3_of_ok hC.h3
  have h : termsOk (C.R.n + 1) (six C.blocks) = true := F.hterms
  unfold six at h
  rw [termsOk_cons] at h
  simp only [Bool.and_eq_true] at h
  exact blocksOk_n0 _ _ 0 h.1.1.1.1.1.1.1

theorem ker_eq (C : UCert) (hC : C.Ok) (u v t : ℝ) : C.ker u v t = evR u v t (kernZ C.P 0 C.blocks) := by
  unfold ker
  rw [kerR_eq C.P 0 0 u v t C.blocks 0 (C.blocks_n0 hC), if_neg (fun h => h.1 rfl)]
  rfl

/-- **The slack function is the functions of one variable minus the six kernels.** -/
theorem slack_eq (C : UCert) (hC : C.Ok) (u v t : ℝ) :
    (C.cM : ℝ) * C.lam u v t = C.psi u + C.psi v + C.psi t
      - (C.cK : ℝ) * (C.ker u v t + C.ker v u t + C.ker u t v + C.ker t u v + C.ker v t u + C.ker t v u) := by
  have h := slack_id3 C.P C.R C.U1 C.U2 C.U3 C.id3 hC.h3 hC.hW rfl rfl rfl u v t
  have e2 : psiOf C.id3.cM C.id3.wB C.id3.aB C.id3.n C.U2 C.id3.B1 C.id3.cp C.id3.cn v = C.psi v := by
    unfold psiOf psi psiOf
    rw [hC.hT2]
    rfl
  have e3 : psiOf C.id3.cM C.id3.wB C.id3.aB C.id3.n C.U3 C.id3.B2 C.id3.cp C.id3.cn t = C.psi t := by
    unfold psiOf psi psiOf
    rw [hC.hT3]
    rfl
  have e1 : psiOf C.id3.cM C.id3.wB C.id3.aB C.id3.n C.U1 C.id3.B0 C.id3.cp C.id3.cn u = C.psi u := rfl
  have et : termsR C.P C.id3.terms u v t
      = C.ker u v t + C.ker v u t + C.ker u t v + C.ker t u v + C.ker v t u + C.ker t v u := by
    rw [C.ker_eq hC, C.ker_eq hC, C.ker_eq hC, C.ker_eq hC, C.ker_eq hC, C.ker_eq hC]
    show termsR C.P (six C.blocks) u v t = _
    simp only [six, termsR, termR, pick]
    norm_num
    ring
  rw [e1, e2, e3, et] at h
  exact h

theorem lam_swap12 (C : UCert) (hC : C.Ok) (u v t : ℝ) : C.lam u v t = C.lam v u t := by
  have h1 := C.slack_eq hC u v t
  have h2 := C.slack_eq hC v u t
  have hc : (C.cM : ℝ) ≠ 0 := by exact_mod_cast hC.hcM.ne'
  have e : (C.cM : ℝ) * C.lam u v t = (C.cM : ℝ) * C.lam v u t := by
    rw [h1, h2]
    ring
  exact mul_left_cancel₀ hc e

theorem lam_swap23 (C : UCert) (hC : C.Ok) (u v t : ℝ) : C.lam u v t = C.lam u t v := by
  have h1 := C.slack_eq hC u v t
  have h2 := C.slack_eq hC u t v
  have hc : (C.cM : ℝ) ≠ 0 := by exact_mod_cast hC.hcM.ne'
  have e : (C.cM : ℝ) * C.lam u v t = (C.cM : ℝ) * C.lam u t v := by
    rw [h1, h2]
    ring
  exact mul_left_cancel₀ hc e

/-- The identity of a pair. -/
theorem pair_eq (C : UCert) (hC : C.Ok) (s : ℝ) :
    3 * (((C.N : ℝ) - 2) * C.psi s) + 6 * (C.cK : ℝ) * (C.ker s s 1 + C.ker 1 s s + C.ker s 1 s)
      = 3 * (C.cM : ℝ) * (C.fS : ℝ) / (C.U1.c1 : ℝ) / Real.sqrt (2 - 2 * s)
        + ((C.kp : ℝ) - C.kn) / (C.U1.c1 : ℝ) := by
  have h := pair_id1 C.P C.id1 [C.slot] rfl (fun S hS => by
    rw [List.mem_singleton.mp hS]
    rfl) hC.hc1 hC.h1 s
  have hN2 : ((C.N - 2 : ℕ) : ℝ) = (C.N : ℝ) - 2 := by
    have := hC.hN
    push_cast [Nat.cast_sub (by omega : 2 ≤ C.N)]
    ring
  have es : slotsR C.id1.cM C.id1.wB C.id1.aB C.id1.n [C.slot] s = ((C.N : ℝ) - 2) * C.psi s := by
    simp only [slotsR, add_zero]
    rw [← hN2]
    rfl
  have et : dtermsR C.P C.id1.terms s = C.ker s s 1 + C.ker 1 s s + C.ker s 1 s := by
    rw [C.ker_eq hC, C.ker_eq hC, C.ker_eq hC]
    show dtermsR C.P [⟨C.blocks, 0, 0⟩, ⟨C.blocks, 0, 1⟩, ⟨C.blocks, 0, 2⟩] s = _
    simp only [dtermsR, dtermR]
    norm_num
    ring
  rw [es, et] at h
  exact h

/-- **The bound for the sum of the slacks of a configuration.** -/
theorem energy (C : UCert) (hC : C.Ok) (x : Fin C.N → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1) :
    dsum (fun i j k => (C.cM : ℝ) * C.lam (ip x i j) (ip x i k) (ip x j k))
      ≤ 3 * (C.cM : ℝ) * (C.fS : ℝ) / (C.U1.c1 : ℝ)
          * (∑ i, ∑ j, if i ≠ j then 1 / Real.sqrt (2 - 2 * ip x i j) else 0)
        + (C.N : ℝ) * ((C.N : ℝ) - 1) * (((C.kp : ℝ) - C.kn) / (C.U1.c1 : ℝ))
        + 6 * (C.cK : ℝ) * ((C.N : ℝ) * C.ker 1 1 1) := by
  have hsym : ∀ i j, ip x i j = ip x j i := fun i j => real_inner_comm _ _
  have hcard : (Fintype.card (Fin C.N) : ℝ) = C.N := by simp
  have main := slack_sum_le C.P (fun _ => C.blocks) (fun _ => hC.hPD) (C.cK : ℝ) (Nat.cast_nonneg _)
    (fun _ _ _ => C.psi) (fun _ => 0) x hx
    (fun i j => 3 * (C.cM : ℝ) * (C.fS : ℝ) / (C.U1.c1 : ℝ) / Real.sqrt (2 - 2 * ip x i j)
      + ((C.kp : ℝ) - C.kn) / (C.U1.c1 : ℝ))
    (fun i j hij => by
      have hp := C.pair_eq hC (ip x i j)
      have hs : (∑ k, if i ≠ k ∧ j ≠ k then C.psi (ip x i j) else 0) = ((C.N : ℝ) - 2) * C.psi (ip x i j) := by
        rw [← sum_filter, sum_const, nsmul_eq_mul, card_ne_ne hij, hcard]
      rw [hs]
      exact hp)
  -- the slacks
  have e1 : dsum (slackOf C.P (fun _ => C.blocks) (C.cK : ℝ) (fun _ _ _ => C.psi) (fun _ => 0) x)
      = dsum (fun i j k => (C.cM : ℝ) * C.lam (ip x i j) (ip x i k) (ip x j k)) := by
    unfold dsum
    refine sum3_congr fun i j k => ?_
    split_ifs
    · have h := C.slack_eq hC (ip x i j) (ip x i k) (ip x j k)
      show _ = (C.cM : ℝ) * C.lam (ip x i j) (ip x i k) (ip x j k)
      rw [h]
      unfold slackOf Kf UCert.ker
      rw [hsym k j, hsym j i, hsym k i]
    · rfl
  -- the pairs
  have e2 : (∑ i, ∑ j, if i ≠ j then
        (3 * (C.cM : ℝ) * (C.fS : ℝ) / (C.U1.c1 : ℝ) / Real.sqrt (2 - 2 * ip x i j)
          + ((C.kp : ℝ) - C.kn) / (C.U1.c1 : ℝ)) else 0)
      = 3 * (C.cM : ℝ) * (C.fS : ℝ) / (C.U1.c1 : ℝ)
          * (∑ i, ∑ j, if i ≠ j then 1 / Real.sqrt (2 - 2 * ip x i j) else 0)
        + (C.N : ℝ) * ((C.N : ℝ) - 1) * (((C.kp : ℝ) - C.kn) / (C.U1.c1 : ℝ)) := by
    have hone := sum_ne_one (ι := Fin C.N)
    rw [hcard] at hone
    rw [← hone, mul_sum, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    split_ifs
    · ring
    · ring
  have e3 : (∑ _i : Fin C.N, Kf C.P (fun _ => C.blocks) 0 0 0 1 1 1) = (C.N : ℝ) * C.ker 1 1 1 := by
    rw [sum_const, card_univ, nsmul_eq_mul, hcard]
    rfl
  rw [e1, e2, e3] at main
  exact main

/-- The value of a polynomial with natural coefficients at `(1, 1, 1)` is the sum of its coefficients. -/
theorem evN_one (F : Poly) : evN 1 1 1 F = (csum F : ℝ) := by
  induction F using MvPolynomial.induction_on with
  | C a => rw [evN_C, csum_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, Nat.cast_add]
  | mul_X p i hp =>
    have hX : evN 1 1 1 (MvPolynomial.X i) = 1 := by
      fin_cases i
      · exact evN_X0 1 1 1
      · exact evN_X1 1 1 1
      · exact evN_X2 1 1 1
    rw [map_mul, map_mul, hp, hX, csum_X, mul_one, mul_one]

/-- The kernel at `(1, 1, 1)` from the two numbers that the kernel computes at this point. -/
theorem ker_one (C : UCert) (hC : C.Ok) (z1 z2 : ℕ) (hz : kern C.P ⟨0, 0, 0⟩ 0 C.blocks = (z1, z2)) :
    C.ker 1 1 1 = (z1 : ℝ) - z2 := by
  have F := facts3_of_ok hC.h3
  have h := kern_zero C.P 0 C.blocks
  rw [hz] at h
  have h1 : z1 = csum (kernP C.P 0 C.blocks).1 := congrArg Prod.fst h
  have h2 : z2 = csum (kernP C.P 0 C.blocks).2 := congrArg Prod.snd h
  rw [C.ker_eq hC, ← val_kernP C.P F.heb F.hcb, ← evN_sub, evN_one, evN_one, h1, h2]

/-- The distance of two points of the unit sphere. -/
theorem dist_sphere {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1) (i j : Fin n) :
    dist (x i) (x j) = Real.sqrt (2 - 2 * ip x i j) := by
  unfold ip
  rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg (x i - x j)), norm_sub_sq_real, hx i, hx j]
  congr 1
  ring

/-- **The bound for the energy.** With the two numbers `z1`, `z2` of the kernel at `(1, 1, 1)` and a rational
number `en / ed` that satisfies the equation of the constants (an equation between natural numbers), the energy
of `N` points of the unit sphere is at least `en / ed` plus a multiple of the sum of the slacks. -/
theorem energy_ge (C : UCert) (hC : C.Ok) (z1 z2 en ed : ℕ)
    (hz : kern C.P ⟨0, 0, 0⟩ 0 C.blocks = (z1, z2)) (hed : 0 < ed) (hfS : 0 < C.fS)
    (hconst : en * (6 * C.cM * C.fS) + (C.N * (C.N - 1) * C.kp + 6 * C.U1.c1 * C.cK * C.N * z1) * ed
      = (C.N * (C.N - 1) * C.kn + 6 * C.U1.c1 * C.cK * C.N * z2) * ed)
    (x : Fin C.N → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1) :
    (en : ℝ) / ed + (C.U1.c1 : ℝ) * dsum (fun i j k => C.lam (ip x i j) (ip x i k) (ip x j k)) / (6 * (C.fS : ℝ))
      ≤ ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / dist (x i) (x j) := by
  have h := C.energy hC x hx
  rw [dsum_smul, C.ker_one hC z1 z2 hz] at h
  -- the pairs
  have hpair : (∑ i, ∑ j, if i ≠ j then 1 / Real.sqrt (2 - 2 * ip x i j) else 0)
      = 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / dist (x i) (x j) := by
    have h4 := CAP.ThreePoint.sum_ne_eq_two_mul_sum_lt (fun i j => 1 / dist (x i) (x j))
      (fun i j => by rw [dist_comm])
    rw [← h4]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [dist_sphere x hx]
  rw [hpair] at h
  -- the constants as real numbers
  have hN1 : ((C.N - 1 : ℕ) : ℝ) = (C.N : ℝ) - 1 := by
    have := hC.hN
    push_cast [Nat.cast_sub (by omega : 1 ≤ C.N)]
    ring
  have hc := congrArg (Nat.cast (R := ℝ)) hconst
  push_cast at hc
  rw [hN1] at hc
  have hc1 : (0 : ℝ) < C.U1.c1 := by exact_mod_cast hC.hc1
  have hcM : (0 : ℝ) < C.cM := by exact_mod_cast hC.hcM
  have hfS' : (0 : ℝ) < C.fS := by exact_mod_cast hfS
  have hed' : (0 : ℝ) < ed := by exact_mod_cast hed
  set D := dsum (fun i j k => C.lam (ip x i j) (ip x i k) (ip x j k)) with hD
  set E := ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / dist (x i) (x j) with hE
  -- the bound multiplied by `c1`
  have key : (C.U1.c1 : ℝ) * ((C.cM : ℝ) * D)
      ≤ 6 * (C.cM : ℝ) * (C.fS : ℝ) * E + (C.N : ℝ) * ((C.N : ℝ) - 1) * ((C.kp : ℝ) - C.kn)
        + 6 * (C.U1.c1 : ℝ) * (C.cK : ℝ) * ((C.N : ℝ) * ((z1 : ℝ) - z2)) := by
    have h' := mul_le_mul_of_nonneg_left h hc1.le
    have e : (C.U1.c1 : ℝ) * (3 * (C.cM : ℝ) * (C.fS : ℝ) / (C.U1.c1 : ℝ) * (2 * E)
          + (C.N : ℝ) * ((C.N : ℝ) - 1) * (((C.kp : ℝ) - C.kn) / (C.U1.c1 : ℝ))
          + 6 * (C.cK : ℝ) * ((C.N : ℝ) * ((z1 : ℝ) - z2)))
        = 6 * (C.cM : ℝ) * (C.fS : ℝ) * E + (C.N : ℝ) * ((C.N : ℝ) - 1) * ((C.kp : ℝ) - C.kn)
          + 6 * (C.U1.c1 : ℝ) * (C.cK : ℝ) * ((C.N : ℝ) * ((z1 : ℝ) - z2)) := by
      field_simp
      ring
    rw [e] at h'
    exact h'
  have hpos : (0 : ℝ) < 6 * (C.cM : ℝ) * (C.fS : ℝ) * ed := by positivity
  have e2 : (en : ℝ) / ed + (C.U1.c1 : ℝ) * D / (6 * (C.fS : ℝ))
      = ((en : ℝ) * (6 * (C.cM : ℝ) * (C.fS : ℝ)) + (C.U1.c1 : ℝ) * ((C.cM : ℝ) * D) * ed)
        / (6 * (C.cM : ℝ) * (C.fS : ℝ) * ed) := by
    field_simp
  rw [e2, div_le_iff₀ hpos]
  have key2 := mul_le_mul_of_nonneg_right key hed'.le
  linarith

end UCert

/-- A lower bound for a symmetric function of three variables follows from the bound for arguments in
increasing order, under a condition that is symmetric as well. -/
theorem ge_of_sorted (f : ℝ → ℝ → ℝ → ℝ) (h12 : ∀ u v t, f u v t = f v u t) (h23 : ∀ u v t, f u v t = f u t v)
    (S : ℝ → ℝ → ℝ → Prop) (hS12 : ∀ u v t, S u v t → S v u t) (hS23 : ∀ u v t, S u v t → S u t v) (θ : ℝ)
    (h : ∀ u v t, u ≤ v → v ≤ t → S u v t → θ ≤ f u v t) (u v t : ℝ) (hS : S u v t) : θ ≤ f u v t := by
  rcases le_total u v with huv | huv
  · rcases le_total v t with hvt | hvt
    · exact h u v t huv hvt hS
    · rcases le_total u t with hut | hut
      · rw [h23]
        exact h u t v hut hvt (hS23 _ _ _ hS)
      · rw [h23, h12]
        exact h t u v hut huv (hS12 _ _ _ (hS23 _ _ _ hS))
  · rcases le_total u t with hut | hut
    · rw [h12]
      exact h v u t huv hut (hS12 _ _ _ hS)
    · rcases le_total v t with hvt | hvt
      · rw [h12, h23]
        exact h v t u hvt hut (hS23 _ _ _ (hS12 _ _ _ hS))
      · rw [h12, h23, h12]
        exact h t v u hvt huv (hS12 _ _ _ (hS23 _ _ _ (hS12 _ _ _ hS)))

/-! ## Points of the sphere -/

theorem neg_one_le_ip {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1) (i j : Fin n) :
    -1 ≤ ip x i j := by
  have habs := abs_real_inner_le_norm (x i) (x j)
  rw [hx i, hx j, mul_one] at habs
  exact (abs_le.mp habs).1

theorem ip_lt_one {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1)
    (hinj : Function.Injective x) {i j : Fin n} (hij : i ≠ j) : ip x i j < 1 := by
  have habs := abs_real_inner_le_norm (x i) (x j)
  rw [hx i, hx j, mul_one] at habs
  have hne : inner ℝ (x i) (x j) ≠ (1 : ℝ) := fun h => hij (hinj (eq_of_inner_eq_one (hx i) (hx j) h))
  exact lt_of_le_of_ne (abs_le.mp habs).2 hne

theorem gram_ip {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1) (i j k : Fin n) :
    0 ≤ gram (ip x i j) (ip x i k) (ip x j k) :=
  gram_nonneg (x i) (x j) (x k) (hx i) (hx j) (hx k)

theorem gram_swap12 (u v t : ℝ) : gram v u t = gram u v t := by
  unfold gram
  ring

theorem gram_swap23 (u v t : ℝ) : gram u t v = gram u v t := by
  unfold gram
  ring

/-- **A lower bound for the slack function at the triples of a configuration.** If `θ ≤ λ (u, v, t)` for
ordered arguments `u ≤ v ≤ t` of `[-1, 1)³` with nonnegative Gram determinant in a region that is symmetric in
the three arguments, then `θ ≤ λ` at the three inner products of every triple of distinct points whose inner
products lie in the region. -/
theorem lam_region3 (C : UCert) (hC : C.Ok) (Rg : ℝ → ℝ → ℝ → Prop) (hR12 : ∀ u v t, Rg u v t → Rg v u t)
    (hR23 : ∀ u v t, Rg u v t → Rg u t v) (θ : ℝ)
    (h : ∀ u v t, u ≤ v → v ≤ t → -1 ≤ u → t < 1 → 0 ≤ gram u v t → Rg u v t → θ ≤ C.lam u v t)
    {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1) (hinj : Function.Injective x)
    (i j k : Fin n) (hd : Distinct3 i j k) (hR : Rg (ip x i j) (ip x i k) (ip x j k)) :
    θ ≤ C.lam (ip x i j) (ip x i k) (ip x j k) := by
  refine ge_of_sorted C.lam (C.lam_swap12 hC) (C.lam_swap23 hC)
    (fun u v t => (-1 ≤ u ∧ -1 ≤ v ∧ -1 ≤ t) ∧ (u < 1 ∧ v < 1 ∧ t < 1) ∧ 0 ≤ gram u v t ∧ Rg u v t)
    ?_ ?_ θ ?_ _ _ _ ?_
  · rintro u v t ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, hg, hr⟩
    exact ⟨⟨a2, a1, a3⟩, ⟨b2, b1, b3⟩, by rw [gram_swap12]; exact hg, hR12 _ _ _ hr⟩
  · rintro u v t ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, hg, hr⟩
    exact ⟨⟨a1, a3, a2⟩, ⟨b1, b3, b2⟩, by rw [gram_swap23]; exact hg, hR23 _ _ _ hr⟩
  · rintro u v t huv hvt ⟨⟨a1, _, _⟩, ⟨_, _, b3⟩, hg, hr⟩
    exact h u v t huv hvt a1 b3 hg hr
  · exact ⟨⟨neg_one_le_ip x hx i j, neg_one_le_ip x hx i k, neg_one_le_ip x hx j k⟩,
      ⟨ip_lt_one x hx hinj hd.1, ip_lt_one x hx hinj hd.2.1, ip_lt_one x hx hinj hd.2.2⟩, gram_ip x hx i j k, hR⟩

/-- The same for a region that is given by a condition on each inner product. -/
theorem lam_region (C : UCert) (hC : C.Ok) (S : ℝ → Prop) (θ : ℝ)
    (h : ∀ u v t, u ≤ v → v ≤ t → -1 ≤ u → t < 1 → 0 ≤ gram u v t → S u → S v → S t → θ ≤ C.lam u v t)
    {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1) (hinj : Function.Injective x)
    (i j k : Fin n) (hd : Distinct3 i j k) (h1 : S (ip x i j)) (h2 : S (ip x i k)) (h3 : S (ip x j k)) :
    θ ≤ C.lam (ip x i j) (ip x i k) (ip x j k) :=
  lam_region3 C hC (fun u v t => S u ∧ S v ∧ S t) (fun _ _ _ ⟨a, b, c⟩ => ⟨b, a, c⟩)
    (fun _ _ _ ⟨a, b, c⟩ => ⟨a, c, b⟩) θ
    (fun u v t huv hvt hu ht1 hg ⟨a, b, c⟩ => h u v t huv hvt hu ht1 hg a b c) x hx hinj i j k hd ⟨h1, h2, h3⟩

end N14.Energy

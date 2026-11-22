module

public import N14.Energy.Triples
public import N14.Energy.Kernel

/-!
# T7, the bound for the sum of the slacks of a certificate with slack functions

**Setting.** Points `x i` of the unit sphere of `ℝ³` with types `τ i`; for every type `r` of a root point a list
of positive definite blocks (`blocks r`), with the kernel `K_r (σ, σ') = kerR P (blocks r) 0 σ σ'`; functions of
one variable `ψ a b c` (the share that a pair of the types `a`, `b` gives to a third point of the type `c`); a
number `cK ≥ 0`. The *slack* of an ordered triple of distinct points `i`, `j`, `k` is

  `ψ (τ i) (τ j) (τ k) (⟨x i, x j⟩) + ψ (τ i) (τ k) (τ j) (⟨x i, x k⟩) + ψ (τ j) (τ k) (τ i) (⟨x j, x k⟩)`
  `- cK * (the six kernels that contain the three points, one of them as the root)`      (`slackOf`).

**Theorem** (`slack_sum_le`). Let `g i j` be numbers with, for `i ≠ j` and `s = ⟨x i, x j⟩`,

  `3 * ∑_{k ≠ i, j} ψ (τ i) (τ j) (τ k) s + 6 * cK * (K (s, s, 1) + K (1, s, s) + K (s, 1, s)) = g i j`

(the kernels rooted at `i`, with the types of the three places). Then the sum of the slacks over the ordered
triples of distinct points is at most `∑_{i ≠ j} g i j + 6 * cK * ∑ i, K_{τ i} (τ i, τ i) (1, 1, 1)`.

This is the identity of the three-point bound (`triple_identity`) together with the positivity of the kernels
(`kerR_sphere`). In a certificate `g i j` is a multiple of the Coulomb potential of the pair plus a constant, so
the theorem bounds the energy from below by the sum of the slacks.
-/

@[expose] public section

namespace N14.Energy

open CAP CAP.ThreePoint N14.Ident Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The kernel rooted at a point of the type `r`, for two points of the types `σ`, `σ'`. -/
noncomputable def Kf (P : Params) (blocks : ℕ → List Blk) (r σ σ' : ℕ) (u v t : ℝ) : ℝ :=
  kerR P (blocks r) 0 σ σ' u v t

/-- The inner product of two points. -/
noncomputable def ip (x : ι → EuclideanSpace ℝ (Fin 3)) (i j : ι) : ℝ := inner ℝ (x i) (x j)

/-- The slack of an ordered triple of points. -/
noncomputable def slackOf (P : Params) (blocks : ℕ → List Blk) (cK : ℝ) (ψ : ℕ → ℕ → ℕ → ℝ → ℝ) (τ : ι → ℕ)
    (x : ι → EuclideanSpace ℝ (Fin 3)) (i j k : ι) : ℝ :=
  ψ (τ i) (τ j) (τ k) (ip x i j) + ψ (τ i) (τ k) (τ j) (ip x i k) + ψ (τ j) (τ k) (τ i) (ip x j k)
    - cK * (Kf P blocks (τ i) (τ j) (τ k) (ip x i j) (ip x i k) (ip x j k)
      + Kf P blocks (τ i) (τ k) (τ j) (ip x i k) (ip x i j) (ip x k j)
      + Kf P blocks (τ j) (τ i) (τ k) (ip x j i) (ip x j k) (ip x i k)
      + Kf P blocks (τ j) (τ k) (τ i) (ip x j k) (ip x j i) (ip x k i)
      + Kf P blocks (τ k) (τ i) (τ j) (ip x k i) (ip x k j) (ip x i j)
      + Kf P blocks (τ k) (τ j) (τ i) (ip x k j) (ip x k i) (ip x j i))

/-- **The sum of the slacks is bounded by the energy side of the identity.** -/
theorem slack_sum_le (P : Params) (blocks : ℕ → List Blk) (hPD : ∀ r, BlkPD P (blocks r)) (cK : ℝ)
    (hcK : 0 ≤ cK) (ψ : ℕ → ℕ → ℕ → ℝ → ℝ) (τ : ι → ℕ) (x : ι → EuclideanSpace ℝ (Fin 3))
    (hx : ∀ i, ‖x i‖ = 1) (g : ι → ι → ℝ)
    (h2 : ∀ i j, i ≠ j → 3 * (∑ k, if i ≠ k ∧ j ≠ k then ψ (τ i) (τ j) (τ k) (ip x i j) else 0)
        + 6 * cK * (Kf P blocks (τ i) (τ j) (τ j) (ip x i j) (ip x i j) 1
          + Kf P blocks (τ i) (τ i) (τ j) 1 (ip x i j) (ip x i j)
          + Kf P blocks (τ i) (τ j) (τ i) (ip x i j) 1 (ip x i j)) = g i j) :
    dsum (slackOf P blocks cK ψ τ x)
      ≤ (∑ i, ∑ j, if i ≠ j then g i j else 0) + 6 * cK * ∑ i, Kf P blocks (τ i) (τ i) (τ i) 1 1 1 := by
  have ha1 : ∀ i, ip x i i = 1 := fun i => by
    unfold ip
    rw [real_inner_self_eq_norm_sq, hx i, one_pow]
  have hsym : ∀ i j, ip x i j = ip x j i := fun i j => real_inner_comm _ _
  -- the numbers of the identity
  have key := triple_identity
    (fun i j k => cK / 2 * Kf P blocks (τ i) (τ j) (τ k) (ip x i j) (ip x i k) (ip x j k))
    (fun i j k => ψ (τ i) (τ j) (τ k) (ip x i j)) g (fun i j hij => by
      have h := h2 i j hij
      simp only [ha1, hsym j i]
      linarith)
  have e1 : dsum (slackOf P blocks cK ψ τ x) = dsum (fun i j k =>
      ψ (τ i) (τ j) (τ k) (ip x i j) + ψ (τ i) (τ k) (τ j) (ip x i k) + ψ (τ j) (τ k) (τ i) (ip x j k)
      + (-2) * (cK / 2 * Kf P blocks (τ i) (τ j) (τ k) (ip x i j) (ip x i k) (ip x j k)
        + cK / 2 * Kf P blocks (τ i) (τ k) (τ j) (ip x i k) (ip x i j) (ip x k j)
        + cK / 2 * Kf P blocks (τ j) (τ i) (τ k) (ip x j i) (ip x j k) (ip x i k)
        + cK / 2 * Kf P blocks (τ j) (τ k) (τ i) (ip x j k) (ip x j i) (ip x k i)
        + cK / 2 * Kf P blocks (τ k) (τ i) (τ j) (ip x k i) (ip x k j) (ip x i j)
        + cK / 2 * Kf P blocks (τ k) (τ j) (τ i) (ip x k j) (ip x k i) (ip x j i))) := by
    unfold dsum
    refine sum3_congr fun i j k => ?_
    split_ifs
    · unfold slackOf
      ring
    · rfl
  -- the kernels are positive definite
  have hpos : 0 ≤ sum3 (fun i j k => cK / 2 * Kf P blocks (τ i) (τ j) (τ k) (ip x i j) (ip x i k) (ip x j k)) := by
    unfold sum3
    refine sum_nonneg fun i _ => ?_
    have h := kerR_sphere P (blocks (τ i)) (hPD (τ i)) τ x hx i
    have e : (∑ j, ∑ k, cK / 2 * Kf P blocks (τ i) (τ j) (τ k) (ip x i j) (ip x i k) (ip x j k))
        = cK / 2 * ∑ j, ∑ k, kerR P (blocks (τ i)) 0 (τ j) (τ k) (inner ℝ (x i) (x j)) (inner ℝ (x i) (x k))
          (inner ℝ (x j) (x k)) := by
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [mul_sum]
      rfl
    rw [e]
    exact mul_nonneg (by linarith) h
  have e2 : (∑ i, cK / 2 * Kf P blocks (τ i) (τ i) (τ i) (ip x i i) (ip x i i) (ip x i i))
      = cK / 2 * ∑ i, Kf P blocks (τ i) (τ i) (τ i) 1 1 1 := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [ha1]
  rw [e1]
  rw [e2] at key
  linarith

end N14.Energy

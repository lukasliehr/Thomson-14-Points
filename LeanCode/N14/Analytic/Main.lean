module

public import N14.Analytic.Coordinates
public import N14.Analytic.LocalMin

/-!
# The theorem for 14 points, analytic part: the theorem (row A12)

`thomson14_of : N14.T7.CAP → N14.Thomson14`: the theorem for 14 points follows from its computer-assisted part.

Let `x` be a configuration of 14 distinct points of the sphere with `energy x ≤ energy Xstar`. By the case
analysis (`tube_of_energy_le`) it satisfies the hypotheses of the rigidity lemma. By the rigidity lemma
(`rigidity`) it is, after an orthogonal map and a relabelling, the configuration with the gauge coordinates
`pStarN + D` with `|D|₂ ≤ 0.0075`. By local minimality (`local_min`) the displacement `D` vanishes, since the
energy does not change under orthogonal maps and relabellings. Hence `x` arises from the candidate by an
orthogonal map and a relabelling, and its energy is that of the candidate.
-/

@[expose] public section

namespace N14

open Finset N14.T7 N14.Local

/-- **A configuration with energy at most that of the candidate is congruent to the candidate.** -/
theorem congruent_of_energy_le (H : CAP) (x : Fin 14 → Fin 3 → ℝ) (hx : OnSphere x)
    (hinj : Function.Injective x) (hE : energy x ≤ energy Xstar) :
    Congruent Xstar x ∧ energy x = energy Xstar := by
  have hb := hStar_bounds H
  have hh : 4553 / 10000 ≤ hStar ∧ hStar ≤ 4554 / 10000 := ⟨by linarith [hb.1], by linarith [hb.2]⟩
  obtain ⟨p, q, T⟩ := tube_of_energy_le H x hx hinj hE
  obtain ⟨U, hU, σ, D, hS, hn, hk, hg⟩ := rigidity x hx hh p q T
  have hEx : energyG (qOf D) = energy x := by
    unfold energyG
    exact energy_of_congr x _ U hU σ (fun n => (hg n).symm)
  -- the displacement vanishes
  have hn0 : nsq D = 0 := by
    by_contra hne
    have hpos : 0 < nsq D := lt_of_le_of_ne (nsq_nonneg D) (Ne.symm hne)
    have := local_min H D hS hk hpos hn
    linarith
  have hD0 : ∀ k, D k = 0 := by
    intro k
    by_cases hk25 : k < 25
    · have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (D k))).mp hn0 k
        (Finset.mem_range.mpr hk25)
      exact (pow_eq_zero_iff (by norm_num)).mp h1
    · exact hS k (by omega)
  have hq : qOf D = pStarN := funext fun k => by
    unfold qOf
    rw [hD0 k, zero_add]
  have hX : ∀ n : Fin 14, U.mulVec (x (σ n)) = Xstar n := fun n => by
    rw [hg n, hq, gauge_star n.val n.isLt]
    rfl
  -- the inverse of the orthogonal map
  have hUt : U.transpose * U = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hU
  have hUt' : U.transpose ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff, Matrix.transpose_transpose]
    exact hUt
  have hcong : ∀ i, x i = U.transpose.mulVec (Xstar (σ.symm i)) := fun i => by
    have h1 := hX (σ.symm i)
    rw [Equiv.apply_symm_apply] at h1
    rw [← h1, Matrix.mulVec_mulVec, hUt, Matrix.one_mulVec]
  exact ⟨⟨U.transpose, hUt', σ.symm, hcong⟩, energy_of_congr Xstar x U.transpose hUt' σ.symm hcong⟩

/-- **The theorem for 14 points follows from its computer-assisted part.** -/
theorem thomson14_of (H : CAP) : Thomson14 := by
  refine ⟨H.height, H.candidate.1, H.candidate.2, fun x hx hinj => ⟨?_, fun he => ?_⟩⟩
  · by_contra hlt
    rw [not_le] at hlt
    have := (congruent_of_energy_le H x hx hinj hlt.le).2
    linarith
  · exact (congruent_of_energy_le H x hx hinj he.le).1

end N14

import Mathlib
import N14Cert.T7A

/-!
# The Thomson problem for 14 points

The Thomson problem asks for the configurations of `N` points on the unit sphere of `ℝ³` that
minimize the Coulomb energy, the sum of the reciprocal distances over all pairs of points.
This file states its solution for `N = 14`: the minimizer is the bicapped hexagonal antiprism,
and it is unique up to orthogonal transformations and relabelling of the points.

All definitions needed to read the statement are included here.
This companion supplies the complete proof of the statement in `Showcase.lean`.
-/

noncomputable section
open Real

namespace Thomson14

/-! ## Configurations and Coulomb energy -/

/-- Three-dimensional Euclidean space. -/
abbrev Point := EuclideanSpace ℝ (Fin 3)

/-- Fourteen distinct points on the unit sphere. -/
def IsConfiguration (Y : Fin 14 → Point) : Prop :=
  (∀ i, ‖Y i‖ = 1) ∧ Function.Injective Y

/-- The Coulomb energy, summed over the 91 unordered pairs of points.
(For two equal points Lean evaluates `1 / 0` to `0`; the theorem below concerns configurations
of distinct points only.) -/
def E (Y : Fin 14 → Point) : ℝ :=
  ∑ i : Fin 14, ∑ j : Fin 14 with i < j, 1 / ‖Y i - Y j‖

/-- `Y` arises from `Z` by an orthogonal transformation and a permutation of the labels.
Here `Point ≃ₗᵢ[ℝ] Point` is the type of the linear isometries of `ℝ³` onto itself, that is, of
the orthogonal transformations, and `Equiv.Perm (Fin 14)` is the type of the permutations of the
labels `0, …, 13`. -/
def Congruent (Y Z : Fin 14 → Point) : Prop :=
  ∃ (U : Point ≃ₗᵢ[ℝ] Point) (σ : Equiv.Perm (Fin 14)),
    ∀ i, Y i = U (Z (σ i))

/-- `Z` is a configuration that attains the global minimum of the energy, and equality occurs
exactly at its congruent copies. -/
def IsUniqueMinimizer (Z : Fin 14 → Point) : Prop :=
  IsConfiguration Z ∧ ∀ Y, IsConfiguration Y →
    E Z ≤ E Y ∧ (E Y = E Z ↔ Congruent Y Z)

/-! ## The bicapped hexagonal antiprism -/

/-- The point of the unit sphere at height `z` and longitude `θ`, for `-1 ≤ z ≤ 1`.
Here `!₂[x, y, z]` is the Euclidean vector with coordinates `(x, y, z)`. -/
def pointAt (z θ : ℝ) : Point :=
  !₂[√(1 - z ^ 2) * cos θ, √(1 - z ^ 2) * sin θ, z]

/-- `X(h)` consists of the two poles, a regular hexagon at height `h`, and a regular hexagon
at height `-h` that is rotated by `π/6` against the first: the six points at height `h` have the
longitudes `k π / 3`, and the six points at height `-h` the longitudes `(2 k + 1) π / 6`, for
`k = 0, …, 5`. Here `![x₀, …, x₁₃]` is the family with the entries `x₀, …, x₁₃`. -/
def X (h : ℝ) : Fin 14 → Point :=
  ![!₂[0, 0, 1], !₂[0, 0, -1],
    pointAt h 0, pointAt h (π / 3), pointAt h (2 * π / 3),
    pointAt h (3 * π / 3), pointAt h (4 * π / 3), pointAt h (5 * π / 3),
    pointAt (-h) (π / 6), pointAt (-h) (3 * π / 6), pointAt (-h) (5 * π / 6),
    pointAt (-h) (7 * π / 6), pointAt (-h) (9 * π / 6), pointAt (-h) (11 * π / 6)]

/-! ## Translation to the coordinates of the proof

The proof in `LeanCode` describes a configuration by its coordinates `Fin 14 → Fin 3 → ℝ` and an
orthogonal transformation by its matrix. The lemmas of this section translate its statements to
the definitions above. -/

/-- The coordinates of a configuration. -/
private def coords (Y : Fin 14 → Point) : Fin 14 → Fin 3 → ℝ := fun i => (Y i).ofLp

private theorem pt_coords (Y : Fin 14 → Point) : N14.pt (coords Y) = Y := rfl

private theorem isConfiguration_iff (Y : Fin 14 → Point) :
    IsConfiguration Y ↔ N14.OnSphere (coords Y) ∧ Function.Injective (coords Y) := by
  rw [N14.onSphere_iff, ← N14.injective_pt, pt_coords]
  rfl

private theorem E_eq (Y : Fin 14 → Point) : E Y = N14.energy (coords Y) := by
  rw [N14.energy_eq, pt_coords]
  simp only [E, dist_eq_norm]

/-- The family `X(h)` is the family of the proof. -/
private theorem coords_X (h : ℝ) : coords (X h) = N14.X14 h := by
  funext n k
  fin_cases n <;> fin_cases k <;>
    simp [coords, X, pointAt, N14.X14, N14.X14N] <;> ring_nf <;> simp

/-- The orthogonal transformation with a given orthogonal matrix. -/
private def isometryOfMatrix (U : Matrix (Fin 3) (Fin 3) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ) : Point ≃ₗᵢ[ℝ] Point :=
  LinearIsometry.toLinearIsometryEquiv
    ⟨Matrix.toEuclideanLin U, fun v => by
      have h := N14.dot_mulVec U hU v.ofLp v.ofLp
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      congr 1
      simpa [sq] using h⟩ rfl

private theorem isometryOfMatrix_apply (U : Matrix (Fin 3) (Fin 3) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (v : Point) :
    isometryOfMatrix U hU v = WithLp.toLp 2 (U.mulVec v.ofLp) := rfl

private theorem congruent_of_coords {Y Z : Fin 14 → Point}
    (h : N14.Congruent (coords Z) (coords Y)) : Congruent Y Z := by
  obtain ⟨U, hU, σ, hY⟩ := h
  refine ⟨isometryOfMatrix U hU, σ, fun i => ?_⟩
  rw [isometryOfMatrix_apply]
  exact congrArg (WithLp.toLp 2) (hY i)

/-- Congruent configurations have the same energy. -/
private theorem E_eq_of_congruent {Y Z : Fin 14 → Point} (h : Congruent Y Z) : E Y = E Z := by
  obtain ⟨U, σ, hY⟩ := h
  have hd : ∀ i j, ‖Y i - Y j‖ = ‖Z (σ i) - Z (σ j)‖ := fun i j => by
    rw [hY i, hY j, ← map_sub, LinearIsometryEquiv.norm_map]
  simp only [E, hd]
  exact N14.pairsum_comp_perm (fun i j => 1 / ‖Z i - Z j‖)
    (fun i j => by rw [norm_sub_rev]) (fun i => by simp) σ

/-! ## The main theorem -/

/-- A decimal number with 50 decimal places, which approximates the optimal height. -/
def h₀ : ℝ := 0.45536779516246300350924502372107445741075259468695

/-- A decimal number with 48 decimal places, which approximates the minimal energy. -/
def E₀ : ℝ := 69.306363296626421258489991276382007864282129573759

/-- **The Thomson problem for 14 points.** There is a height `h` with the following properties.

* `h` agrees with the decimal number `h₀` up to `2 · 10⁻⁵¹`.
* Among all `t` within `10⁻⁴⁰` of `h₀`, the height `h` is the only stationary point of the
  energy `t ↦ E(X(t))` of the family of bicapped hexagonal antiprisms. Here
  `HasDerivAt f 0 t` states that `f` is differentiable at `t` with derivative `0`.
  This property and the previous one determine `h`.
* `X(h)` is a configuration of 14 distinct points on the unit sphere, every such configuration
  `Y` satisfies `E(X(h)) ≤ E(Y)`, and equality holds exactly when `Y` arises from `X(h)` by an
  orthogonal transformation and a relabelling of the points.
* The minimal energy `E(X(h))` agrees with the decimal number `E₀` up to `10⁻⁴⁹`. -/
theorem thomson_14_points :
    ∃ h : ℝ,
      |h - h₀| ≤ 2 / 10 ^ 51 ∧
      (∀ t : ℝ, |t - h₀| ≤ 1 / 10 ^ 40 → (HasDerivAt (fun s ↦ E (X s)) 0 t ↔ t = h)) ∧
      IsUniqueMinimizer (X h) ∧
      |E (X h) - E₀| ≤ 1 / 10 ^ 49 := by
  -- The computer-assisted part of the proof (`Certificates`) and the theorem in
  -- the coordinates of the proof, for the height `N14.hStar` and the family `N14.X14`.
  have cap : N14.T7.CAP := N14Cert.T7.cap
  obtain ⟨hex, hsph, hinj, hmin⟩ : N14.Thomson14 := N14Cert.T7A.thomson14
  have hstat : N14.StationaryHeight N14.hStar := N14.stationary_hStar cap
  have hfam : (fun s ↦ E (X s)) = fun t ↦ N14.energy (N14.X14 t) :=
    funext fun s => by rw [E_eq, coords_X]
  have hEX : E (X N14.hStar) = N14.energy N14.Xstar := by rw [E_eq, coords_X]; rfl
  refine ⟨N14.hStar, cap.hStar_enc, fun t ht => ?_, ⟨?_, fun Y hY => ?_⟩, ?_⟩
  · -- the stationary height
    rw [hfam]
    exact ⟨fun hd => hex.unique ⟨ht, hd⟩ hstat, fun ht' => ht' ▸ hstat.2⟩
  · -- the candidate is a configuration
    rw [isConfiguration_iff, coords_X]
    exact ⟨hsph, hinj⟩
  · -- minimality and the case of equality
    obtain ⟨hYs, hYi⟩ := (isConfiguration_iff Y).mp hY
    obtain ⟨hle, heq⟩ := hmin (coords Y) hYs hYi
    rw [hEX, E_eq Y]
    refine ⟨hle, fun h => congruent_of_coords ?_, fun h => ?_⟩
    · rw [coords_X]
      exact heq h
    · rw [← E_eq Y, ← hEX]
      exact E_eq_of_congruent h
  · -- the minimal energy
    rw [hEX]
    exact cap.energy_enc

/-- info: 'Thomson14.thomson_14_points' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thomson_14_points

end Thomson14

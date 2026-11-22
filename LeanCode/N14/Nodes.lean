module

public import N14.Basic
public import N14.Energy.Types

/-!
# The theorem for 14 points: the nodes of the cap as the types of the triples of the candidate

In Case III of the source two points `P`, `Q` of a configuration have the type `P` and the others the type `R`.
The *type* of an ordered triple of points is the triple of its inner products, and the *nodes* of a pattern
`(t₁, t₂, t₃)` of types are the types of the ordered triples of distinct points of the candidate with these
types of points (the poles are the points of the type `P`). This file states the distance to the nodes without
a list of nodes:

* `FarAll h ρ t₁ t₂ t₃ u v t`: the point `(u, v, t)` has distance at least `ρ` from the type of every ordered
  triple of distinct points of `X14 h` whose points have the types `t₁, t₂, t₃`;
* `FarAll.swap12`, `FarAll.swap23`: the statement does not depend on the order of the triple;
* `PairFar h τ t₁ t₂ s`: the number `s` has distance at least `τ` from the inner product of every ordered pair
  of distinct points of `X14 h` with the types `t₁, t₂` (the *class values* of the source);
* `FarAll.of_pair12`, `of_pair13`, `of_pair23`: a triple with such an inner product is far from all nodes
  (statement (7.5) of the source);
* `Far`, `Far.swap12`, `Far.swap23`: the same for a triple of a configuration with the types `tau p q`.
-/

@[expose] public section

namespace N14

open CAP.ThreePoint N14.Energy

/-- The type of a point of the candidate: `0` for the poles, `1` for the points of the hexagons. -/
def tauS (a : Fin 14) : ℕ := if a.val < 2 then 0 else 1

/-- The point `(u, v, t)` has distance at least `ρ` from the types of all ordered triples of distinct points of
`X14 h` whose points have the types `t1, t2, t3`. -/
def FarAll (h ρ : ℝ) (t1 t2 t3 : ℕ) (u v t : ℝ) : Prop :=
  ∀ a b c : Fin 14, Distinct3 a b c → tauS a = t1 → tauS b = t2 → tauS c = t3 →
    ρ ^ 2 ≤ (u - ipc h a b) ^ 2 + (v - ipc h a c) ^ 2 + (t - ipc h b c) ^ 2

theorem FarAll.swap12 {h ρ : ℝ} {t1 t2 t3 : ℕ} {u v t : ℝ} (H : FarAll h ρ t1 t2 t3 u v t) :
    FarAll h ρ t2 t1 t3 u t v := by
  intro a b c hd ha hb hc
  have h1 := H b a c ⟨hd.1.symm, hd.2.2, hd.2.1⟩ hb ha hc
  rw [ipc_comm h b a hd.1.symm] at h1
  linarith

theorem FarAll.swap23 {h ρ : ℝ} {t1 t2 t3 : ℕ} {u v t : ℝ} (H : FarAll h ρ t1 t2 t3 u v t) :
    FarAll h ρ t1 t3 t2 v u t := by
  intro a b c hd ha hb hc
  have h1 := H a c b ⟨hd.2.1, hd.1, hd.2.2.symm⟩ ha hc hb
  rw [ipc_comm h c b hd.2.2.symm] at h1
  linarith

/-- The number `s` has distance at least `τ` from the inner products of all ordered pairs of distinct points of
`X14 h` with the types `t1, t2`. -/
def PairFar (h τ : ℝ) (t1 t2 : ℕ) (s : ℝ) : Prop :=
  ∀ a b : Fin 14, a ≠ b → tauS a = t1 → tauS b = t2 → τ ≤ |s - ipc h a b|

theorem PairFar.symm {h τ : ℝ} {t1 t2 : ℕ} {s : ℝ} (H : PairFar h τ t1 t2 s) : PairFar h τ t2 t1 s := by
  intro a b hab ha hb
  have h1 := H b a hab.symm hb ha
  rw [ipc_comm h b a hab.symm] at h1
  exact h1

theorem sq_le_of_le_abs {τ d : ℝ} (hτ : 0 ≤ τ) (h : τ ≤ |d|) : τ ^ 2 ≤ d ^ 2 := by
  rw [← sq_abs d]
  exact pow_le_pow_left₀ hτ h 2

theorem FarAll.of_pair12 {h τ : ℝ} {t1 t2 : ℕ} (t3 : ℕ) {u : ℝ} (v t : ℝ) (hτ : 0 ≤ τ)
    (H : PairFar h τ t1 t2 u) : FarAll h τ t1 t2 t3 u v t := by
  intro a b c hd ha hb _
  have h1 := sq_le_of_le_abs hτ (H a b hd.1 ha hb)
  nlinarith [sq_nonneg (v - ipc h a c), sq_nonneg (t - ipc h b c)]

theorem FarAll.of_pair13 {h τ : ℝ} {t1 t3 : ℕ} (t2 : ℕ) (u : ℝ) {v : ℝ} (t : ℝ) (hτ : 0 ≤ τ)
    (H : PairFar h τ t1 t3 v) : FarAll h τ t1 t2 t3 u v t := by
  intro a b c hd ha _ hc
  have h1 := sq_le_of_le_abs hτ (H a c hd.2.1 ha hc)
  nlinarith [sq_nonneg (u - ipc h a b), sq_nonneg (t - ipc h b c)]

theorem FarAll.of_pair23 {h τ : ℝ} {t2 t3 : ℕ} (t1 : ℕ) (u v : ℝ) {t : ℝ} (hτ : 0 ≤ τ)
    (H : PairFar h τ t2 t3 t) : FarAll h τ t1 t2 t3 u v t := by
  intro a b c hd _ hb hc
  have h1 := sq_le_of_le_abs hτ (H b c hd.2.2 hb hc)
  nlinarith [sq_nonneg (u - ipc h a b), sq_nonneg (v - ipc h a c)]

theorem ipc_eq (h : ℝ) (a b : Fin 14) (c : ℕ) (hc : pcS a.val b.val = c) : ipc h a b = ipVal h c := by
  unfold ipc
  rw [hc]

/-- A number close to an enclosure of an inner product of the family is close to this inner product. -/
theorem near_of {h : ℝ} {a b : Fin 14} {c : ℕ} {s V ε0 ε : ℝ} (e : ipc h a b = ipVal h c)
    (hv : |ipVal h c - V| ≤ ε0) (hs : |s - V| ≤ ε - ε0) : |s - ipc h a b| ≤ ε := by
  rw [e]
  rw [abs_le] at hv hs ⊢
  constructor <;> linarith [hv.1, hv.2, hs.1, hs.2]

/-! ## Triples and pairs of a configuration -/

variable {N : ℕ}

/-- The type of the triple `i, j, k` of the configuration `x`, with the points `p`, `q` of the type `P`, has
distance at least `ρ` from all nodes of its pattern. -/
def Far (h ρ : ℝ) (x : Fin N → EuclideanSpace ℝ (Fin 3)) (p q i j k : Fin N) : Prop :=
  FarAll h ρ (tau p q i) (tau p q j) (tau p q k) (ip x i j) (ip x i k) (ip x j k)

theorem Far.swap12 {h ρ : ℝ} {x : Fin N → EuclideanSpace ℝ (Fin 3)} {p q i j k : Fin N}
    (H : Far h ρ x p q i j k) : Far h ρ x p q j i k := by
  have h1 := FarAll.swap12 H
  have e : ip x j i = ip x i j := real_inner_comm _ _
  unfold Far
  rw [e]
  exact h1

theorem Far.swap23 {h ρ : ℝ} {x : Fin N → EuclideanSpace ℝ (Fin 3)} {p q i j k : Fin N}
    (H : Far h ρ x p q i j k) : Far h ρ x p q i k j := by
  have h1 := FarAll.swap23 H
  have e : ip x k j = ip x j k := real_inner_comm _ _
  unfold Far
  rw [e]
  exact h1

/-- The inner product of the pair `i, j` of the configuration `x` has distance at least `τ` from the class
values of its pair class. -/
def PairDisplaced (h τ : ℝ) (x : Fin N → EuclideanSpace ℝ (Fin 3)) (p q i j : Fin N) : Prop :=
  PairFar h τ (tau p q i) (tau p q j) (ip x i j)

theorem PairDisplaced.symm {h τ : ℝ} {x : Fin N → EuclideanSpace ℝ (Fin 3)} {p q i j : Fin N}
    (H : PairDisplaced h τ x p q i j) : PairDisplaced h τ x p q j i := by
  have h1 := PairFar.symm H
  have e : ip x j i = ip x i j := real_inner_comm _ _
  unfold PairDisplaced
  rw [e]
  exact h1

/-- **Statement (7.5) of the source for a configuration**: every triple through a displaced pair is far from
the nodes of its pattern. -/
theorem Far.of_pair {h τ : ℝ} {x : Fin N → EuclideanSpace ℝ (Fin 3)} {p q i0 j0 : Fin N} (hτ : 0 ≤ τ)
    (h0 : i0 ≠ j0) (H : PairDisplaced h τ x p q i0 j0) (i j k : Fin N)
    (c1 : i = i0 ∨ j = i0 ∨ k = i0) (c2 : i = j0 ∨ j = j0 ∨ k = j0) : Far h τ x p q i j k := by
  have H' := H.symm
  rcases c1 with rfl | rfl | rfl <;> rcases c2 with rfl | rfl | rfl
  · exact absurd rfl h0
  · exact FarAll.of_pair12 _ _ _ hτ H
  · exact FarAll.of_pair13 _ _ _ hτ H
  · exact FarAll.of_pair12 _ _ _ hτ H'
  · exact absurd rfl h0
  · exact FarAll.of_pair23 _ _ _ hτ H
  · exact FarAll.of_pair13 _ _ _ hτ H'
  · exact FarAll.of_pair23 _ _ _ hτ H'
  · exact absurd rfl h0

end N14

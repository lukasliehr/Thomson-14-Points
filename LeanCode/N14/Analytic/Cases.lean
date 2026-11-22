module

public import N14.Interface
public import N14.Analytic.Invariance

/-!
# The theorem for 14 points, analytic part: from the eight statements to the hypotheses of rigidity (rows A2 to A5)

Let `x` be a configuration of 14 distinct points of the sphere with `energy x ≤ energy Xstar`, and let `H` be the
computer-assisted part `N14.T7.CAP`.

* `cap_of_energy_le` (row A2): `x` belongs to Case III: there is a pair `p`, `q` with the smallest inner product,
  this inner product is below `-0.99`, and all inner products are below `0.8` (the fields `sep`, `caseI`,
  `caseII`).
* `near_class` (row A3): every inner product of `x` lies within `τ = 39/200000` of the inner product of a pair of
  the candidate with the same types (the field `cap_loc`, which contains the counting lemma of the source).
* `sign_coupling` (row A4, Lemma 7.2 of the source): a point with the height `±h` over `p` has the height `∓h`
  over `q`.
* `class_coupling` (row A5, Lemma 7.3 of the source with the field `cap_far`): the inner product of two points of
  the rings is near a value of the class that their heights determine.
* `tube_of_energy_le`: the hypotheses `Tube` of the rigidity lemma.
-/

@[expose] public section

namespace N14

open Finset N14.T7 N14.Energy CAP.ThreePoint

/-! ## The classes of the pairs of the candidate -/

theorem pcS_pp : ∀ a b : Fin 14, a ≠ b → tauS a = 0 → tauS b = 0 → pcS a.val b.val = 0 := by decide +kernel

theorem pcS_pr : ∀ a b : Fin 14, tauS a = 0 → tauS b = 1 → pcS a.val b.val = 1 ∨ pcS a.val b.val = 2 := by
  decide +kernel

theorem pcS_rr : ∀ a b : Fin 14, a ≠ b → tauS a = 1 → tauS b = 1 → 3 ≤ pcS a.val b.val ∧ pcS a.val b.val ≤ 8 := by
  decide +kernel

/-- Two points of the hexagons lie in the same hexagon if and only if they have the same class with a pole. -/
theorem pcS_tri : ∀ a b c : Fin 14, tauS a = 0 → tauS b = 1 → tauS c = 1 → b ≠ c →
    (pcS a.val b.val = pcS a.val c.val ↔ pcS b.val c.val ≤ 5) := by decide +kernel

theorem tau_left (p q : Fin 14) : tau p q p = 0 := by
  unfold tau
  rw [if_pos (Or.inl rfl)]

theorem tau_right (p q : Fin 14) : tau p q q = 0 := by
  unfold tau
  rw [if_pos (Or.inr rfl)]

theorem tau_other {p q i : Fin 14} (hp : i ≠ p) (hq : i ≠ q) : tau p q i = 1 := by
  unfold tau
  rw [if_neg (fun h => h.elim hp hq)]

/-! ## The stationary height -/

theorem hStar_bounds (H : CAP) : 4553677 / 10000000 ≤ hStar ∧ hStar ≤ 4553678 / 10000000 := by
  obtain ⟨h1, h2⟩ := abs_le.mp H.hStar_enc
  unfold hDec at h1 h2
  constructor
  · norm_num at h1 ⊢
    linarith
  · norm_num at h2 ⊢
    linarith

/-! ## The energy and the inner products -/

/-- The inner products of a point with two points: the square of their sum (Cauchy–Schwarz). -/
theorem dot_add_sq_le {N : ℕ} (x : Fin N → Fin 3 → ℝ) (hx : OnSphere x) (p q i : Fin N) :
    (dot x p i + dot x q i) ^ 2 ≤ 2 + 2 * dot x p q := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin 3)) (fun k => x p k + x q k) (fun k => x i k)
  beta_reduce at hcs
  have e1 : ∑ k, (x p k + x q k) * x i k = dot x p i + dot x q i := by
    unfold dot
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ k, (x p k + x q k) ^ 2 = 2 + 2 * dot x p q := by
    have hp := hx p
    have hq := hx q
    unfold dot
    have e : ∑ k, (x p k + x q k) ^ 2 = ∑ k, x p k ^ 2 + ∑ k, x q k ^ 2 + 2 * ∑ k, x p k * x q k := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, hp, hq]
    ring
  have e3 : ∑ k, x i k ^ 2 = 1 := hx i
  rw [e1, e2, e3] at hcs
  linarith

/-- **A configuration with energy at most that of the candidate belongs to Case III** (row A2). -/
theorem cap_of_energy_le (H : CAP) (x : Fin 14 → Fin 3 → ℝ) (hx : OnSphere x) (hinj : Function.Injective x)
    (hE : energy x ≤ energy Xstar) : ∃ p q : Fin 14, Cap x p q := by
  have hsep : ∀ i j : Fin 14, i ≠ j → dot x i j < t0 := by
    intro i j hij
    by_contra hno
    have := H.sep x hx hinj i j hij (not_lt.mp hno)
    linarith
  obtain ⟨p, q, hpq, hmin⟩ := exists_min_pair (by norm_num : 2 ≤ 14) x
  have hlow : dot x p q < b99 := by
    by_contra hno
    rw [not_lt] at hno
    rcases le_or_gt (dot x p q) b98 with h98 | h98
    · have := H.caseII x hx hinj p q hpq hmin hno h98
      linarith
    · have := H.caseI x hx hinj (fun i j hij => le_trans h98.le (hmin i j hij))
      linarith
  exact ⟨p, q, hpq, hmin, hlow.le, fun i j hij => (hsep i j hij).le⟩

/-- **Every inner product lies within `τ` of a class value of its pair class** (row A3). -/
theorem near_class (H : CAP) (x : Fin 14 → Fin 3 → ℝ) (hx : OnSphere x) (hinj : Function.Injective x)
    (hE : energy x ≤ energy Xstar) (p q : Fin 14) (hcap : Cap x p q) (i j : Fin 14) (hij : i ≠ j) :
    ∃ a b : Fin 14, a ≠ b ∧ tauS a = tau p q i ∧ tauS b = tau p q j
      ∧ |dot x i j - ipc hStar a b| < 39 / 200000 := by
  by_contra hno
  refine absurd (H.cap_loc x hx hinj p q hcap i j hij ?_) (not_lt.mpr hE)
  unfold PairFar
  intro a b hab ha hb
  by_contra hlt
  exact hno ⟨a, b, hab, ha, hb, not_le.mp hlt⟩

/-- The inner product of the two poles of the configuration. -/
theorem near_pole (H : CAP) (x : Fin 14 → Fin 3 → ℝ) (hx : OnSphere x) (hinj : Function.Injective x)
    (hE : energy x ≤ energy Xstar) (p q : Fin 14) (hcap : Cap x p q) : |dot x p q + 1| < 39 / 200000 := by
  obtain ⟨a, b, hab, ha, hb, h⟩ := near_class H x hx hinj hE p q hcap p q hcap.1
  rw [tau_left] at ha
  rw [tau_right] at hb
  unfold ipc at h
  rw [pcS_pp a b hab ha hb] at h
  simp only [ipVal] at h
  rw [sub_neg_eq_add] at h
  exact h

/-- The inner product of a pole of the configuration with a point of the rings: within `τ` of `ipVal h 1 = h`
or of `ipVal h 2 = -h`. -/
theorem near_height (H : CAP) (x : Fin 14 → Fin 3 → ℝ) (hx : OnSphere x) (hinj : Function.Injective x)
    (hE : energy x ≤ energy Xstar) (p q : Fin 14) (hcap : Cap x p q) (r i : Fin 14) (hr : r = p ∨ r = q)
    (hip : i ≠ p) (hiq : i ≠ q) :
    ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ |dot x r i - ipVal hStar m| < 39 / 200000 := by
  have hri : r ≠ i := by
    rcases hr with rfl | rfl
    · exact Ne.symm hip
    · exact Ne.symm hiq
  obtain ⟨a, b, _, ha, hb, h⟩ := near_class H x hx hinj hE p q hcap r i hri
  have hr0 : tau p q r = 0 := by
    rcases hr with rfl | rfl
    · exact tau_left _ _
    · exact tau_right _ _
  rw [hr0] at ha
  rw [tau_other hip hiq] at hb
  exact ⟨pcS a.val b.val, pcS_pr a b ha hb, h⟩

/-- The inner product of two points of the rings: within `τ` of one of the six values `ipVal h c`,
`3 ≤ c ≤ 8`. -/
theorem near_rr (H : CAP) (x : Fin 14 → Fin 3 → ℝ) (hx : OnSphere x) (hinj : Function.Injective x)
    (hE : energy x ≤ energy Xstar) (p q : Fin 14) (hcap : Cap x p q) (i j : Fin 14) (hip : i ≠ p) (hiq : i ≠ q)
    (hjp : j ≠ p) (hjq : j ≠ q) (hij : i ≠ j) :
    ∃ c : ℕ, 3 ≤ c ∧ c ≤ 8 ∧ |dot x i j - ipVal hStar c| < 39 / 200000 := by
  obtain ⟨a, b, hab, ha, hb, h⟩ := near_class H x hx hinj hE p q hcap i j hij
  rw [tau_other hip hiq] at ha
  rw [tau_other hjp hjq] at hb
  obtain ⟨h3, h8⟩ := pcS_rr a b hab ha hb
  exact ⟨pcS a.val b.val, h3, h8, h⟩

/-! ## Sign coupling -/

/-- **Sign coupling** (row A4, Lemma 7.2 of the source). -/
theorem sign_coupling (h s t e : ℝ) (hh : 4553 / 10000 ≤ h) (m m' : ℕ) (hm : m = 1 ∨ m = 2)
    (hs : |s - ipVal h m| < 39 / 200000) (ht : |t - ipVal h m'| < 39 / 200000) (hst : (s + t) ^ 2 ≤ 2 + 2 * e)
    (he : |e + 1| < 39 / 200000) : m' ≠ m := by
  have hs' := abs_lt.mp hs
  have ht' := abs_lt.mp ht
  have he' := abs_lt.mp he
  intro hmm
  rw [hmm] at ht'
  rcases hm with rfl | rfl
  · simp only [ipVal] at hs' ht'
    have h1 : (9 / 10 : ℝ) ≤ s + t := by linarith
    have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 10) h1 2
    linarith
  · simp only [ipVal] at hs' ht'
    have h1 : (9 / 10 : ℝ) ≤ -(s + t) := by linarith
    have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 10) h1 2
    have e2 : (-(s + t)) ^ 2 = (s + t) ^ 2 := by ring
    linarith

/-! ## Class coupling -/

/-- A number near `±h` is far from `∓h`. -/
theorem far_sign (h s : ℝ) (hh : 4553 / 10000 ≤ h) (m m' : ℕ) (hm : m = 1 ∨ m = 2) (hm' : m' = 1 ∨ m' = 2)
    (hne : m' ≠ m) (hs : |s - ipVal h m| < 39 / 200000) : (1 / 100 : ℝ) ^ 2 ≤ (s - ipVal h m') ^ 2 := by
  have hs' := abs_lt.mp hs
  rcases hm with rfl | rfl <;> rcases hm' with rfl | rfl
  · exact absurd rfl hne
  · simp only [ipVal] at hs' ⊢
    have h1 : (1 / 100 : ℝ) ≤ s - -h := by linarith
    exact pow_le_pow_left₀ (by norm_num) h1 2
  · simp only [ipVal] at hs' ⊢
    have h1 : (1 / 100 : ℝ) ≤ h - s := by linarith
    have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 100) h1 2
    have e2 : (h - s) ^ 2 = (s - h) ^ 2 := by ring
    linarith
  · exact absurd rfl hne

/-- A number near one of the nine values of the candidate is far from the eight others. -/
theorem far_class (H : CAP) (t : ℝ) (c m : ℕ) (hc : c < 9) (hm : m < 9) (hne : c ≠ m)
    (ht : |t - ipVal hStar c| < 39 / 200000) : (1 / 100 : ℝ) ^ 2 ≤ (t - ipVal hStar m) ^ 2 := by
  have hsep := H.separation c m hc hm hne
  have h1 := abs_sub_le (ipVal hStar c) t (ipVal hStar m)
  rw [abs_sub_comm (ipVal hStar c) t] at h1
  have h2 : (1 / 100 : ℝ) ≤ |t - ipVal hStar m| := by linarith
  rw [← sq_abs (t - ipVal hStar m)]
  exact pow_le_pow_left₀ (by norm_num) h2 2

/-- **Class coupling** (row A5, Lemma 7.3 of the source with the field `cap_far`): two points of the rings with
the heights `ipVal h mi`, `ipVal h mj` over `p` have an inner product near a value `ipVal h c` with `c ≤ 5` if and
only if `mi = mj`. -/
theorem class_coupling (H : CAP) (x : Fin 14 → Fin 3 → ℝ) (hx : OnSphere x) (hinj : Function.Injective x)
    (hE : energy x ≤ energy Xstar) (p q : Fin 14) (hcap : Cap x p q) (i j : Fin 14) (hip : i ≠ p) (hiq : i ≠ q)
    (hjp : j ≠ p) (hjq : j ≠ q) (hij : i ≠ j) (mi mj c : ℕ) (hmi : mi = 1 ∨ mi = 2) (hmj : mj = 1 ∨ mj = 2)
    (hc3 : 3 ≤ c) (hc8 : c ≤ 8) (hi : |dot x p i - ipVal hStar mi| < 39 / 200000)
    (hj : |dot x p j - ipVal hStar mj| < 39 / 200000) (hc : |dot x i j - ipVal hStar c| < 39 / 200000) :
    (mi = mj ↔ c ≤ 5) := by
  by_contra hno
  have hb := hStar_bounds H
  have hh : (4553 / 10000 : ℝ) ≤ hStar := by linarith [hb.1]
  refine absurd (H.cap_far x hx hinj p q hcap p i j ⟨Ne.symm hip, Ne.symm hjp, hij⟩ ?_) (not_lt.mpr hE)
  unfold FarAll
  intro a b c' hd ha hb' hc'
  rw [tau_left] at ha
  rw [tau_other hip hiq] at hb'
  rw [tau_other hjp hjq] at hc'
  have h1 := pcS_pr a b ha hb'
  have h2 := pcS_pr a c' ha hc'
  have h3 := pcS_rr b c' hd.2.2 hb' hc'
  have h4 := pcS_tri a b c' ha hb' hc' hd.2.2
  unfold ipc
  have n1 := sq_nonneg (dot x p i - ipVal hStar (pcS a.val b.val))
  have n2 := sq_nonneg (dot x p j - ipVal hStar (pcS a.val c'.val))
  have n3 := sq_nonneg (dot x i j - ipVal hStar (pcS b.val c'.val))
  by_cases e1 : pcS a.val b.val = mi
  · by_cases e2 : pcS a.val c'.val = mj
    · have hne : c ≠ pcS b.val c'.val := by
        intro e
        apply hno
        rw [e, ← h4, e1, e2]
      have := far_class H (dot x i j) c (pcS b.val c'.val) (by omega) (by omega) hne hc
      linarith
    · have := far_sign hStar (dot x p j) hh mj (pcS a.val c'.val) hmj h2 e2 hj
      linarith
  · have := far_sign hStar (dot x p i) hh mi (pcS a.val b.val) hmi h1 e1 hi
    linarith

/-! ## The hypotheses of the rigidity lemma -/

/-- **The hypotheses of the rigidity lemma** for the configuration `x` with the poles `p`, `q`, for the height `h`
and the radius `τ = 39/200000`: (i) the poles are nearly antipodal; (ii) every other point has the height `± h`
over `p` and `∓ h` over `q`; (iii) two other points whose heights have the same sign have an inner product near
`h² + (1 - h²) c` with `c ∈ {1/2, -1/2, -1}`, and two points with different signs near `-h² + (1 - h²) c` with
`c ∈ {√3/2, 0, -√3/2}`. -/
structure Tube (h : ℝ) (x : Fin 14 → Fin 3 → ℝ) (p q : Fin 14) : Prop where
  ne : p ≠ q
  pole : |dot x p q + 1| ≤ 39 / 200000
  ring : ∀ i, i ≠ p → i ≠ q →
    (|dot x p i - h| ≤ 39 / 200000 ∧ |dot x q i + h| ≤ 39 / 200000)
      ∨ (|dot x p i + h| ≤ 39 / 200000 ∧ |dot x q i - h| ≤ 39 / 200000)
  same : ∀ i j, i ≠ p → i ≠ q → j ≠ p → j ≠ q → i ≠ j → (0 < dot x p i ↔ 0 < dot x p j) →
    ∃ c : ℝ, (c = 1 / 2 ∨ c = -(1 / 2) ∨ c = -1) ∧ |dot x i j - (h ^ 2 + (1 - h ^ 2) * c)| ≤ 39 / 200000
  diff : ∀ i j, i ≠ p → i ≠ q → j ≠ p → j ≠ q → i ≠ j → ¬ (0 < dot x p i ↔ 0 < dot x p j) →
    ∃ c : ℝ, (c = √3 / 2 ∨ c = 0 ∨ c = -(√3 / 2)) ∧ |dot x i j - (-h ^ 2 + (1 - h ^ 2) * c)| ≤ 39 / 200000

/-- The sign of a number near `ipVal h m`, `m ∈ {1, 2}`. -/
theorem pos_iff_one (h s : ℝ) (hh : 4553 / 10000 ≤ h) (m : ℕ) (hm : m = 1 ∨ m = 2)
    (hs : |s - ipVal h m| < 39 / 200000) : (0 < s ↔ m = 1) := by
  have hs' := abs_lt.mp hs
  rcases hm with rfl | rfl
  · simp only [ipVal] at hs'
    exact ⟨fun _ => rfl, fun _ => by linarith⟩
  · simp only [ipVal] at hs'
    exact ⟨fun h0 => by linarith, fun h0 => by omega⟩

/-- The six values of the inner product of two points of the rings, by the cosines of the hexagons. -/
theorem ipVal_ring (h : ℝ) :
    ipVal h 3 = h ^ 2 + (1 - h ^ 2) * (1 / 2) ∧ ipVal h 4 = h ^ 2 + (1 - h ^ 2) * (-(1 / 2))
      ∧ ipVal h 5 = h ^ 2 + (1 - h ^ 2) * (-1) ∧ ipVal h 6 = -h ^ 2 + (1 - h ^ 2) * (√3 / 2)
      ∧ ipVal h 7 = -h ^ 2 + (1 - h ^ 2) * 0 ∧ ipVal h 8 = -h ^ 2 + (1 - h ^ 2) * (-(√3 / 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [ipVal] <;> ring

/-- **The hypotheses of the rigidity lemma hold for a configuration with energy at most that of the
candidate.** -/
theorem tube_of_energy_le (H : CAP) (x : Fin 14 → Fin 3 → ℝ) (hx : OnSphere x) (hinj : Function.Injective x)
    (hE : energy x ≤ energy Xstar) : ∃ p q : Fin 14, Tube hStar x p q := by
  obtain ⟨p, q, hcap⟩ := cap_of_energy_le H x hx hinj hE
  have hb := hStar_bounds H
  have hh : (4553 / 10000 : ℝ) ≤ hStar := by linarith [hb.1]
  have hpole := near_pole H x hx hinj hE p q hcap
  -- the heights of a point of the rings over the two poles
  have hring : ∀ i, i ≠ p → i ≠ q → ∃ m m' : ℕ, (m = 1 ∨ m = 2) ∧ (m' = 1 ∨ m' = 2) ∧ m' ≠ m
      ∧ |dot x p i - ipVal hStar m| < 39 / 200000 ∧ |dot x q i - ipVal hStar m'| < 39 / 200000 := by
    intro i hip hiq
    obtain ⟨m, hm, h1⟩ := near_height H x hx hinj hE p q hcap p i (Or.inl rfl) hip hiq
    obtain ⟨m', hm', h2⟩ := near_height H x hx hinj hE p q hcap q i (Or.inr rfl) hip hiq
    exact ⟨m, m', hm, hm', sign_coupling hStar _ _ _ hh m m' hm h1 h2 (dot_add_sq_le x hx p q i) hpole,
      h1, h2⟩
  refine ⟨p, q, hcap.1, hpole.le, ?_, ?_, ?_⟩
  · intro i hip hiq
    obtain ⟨m, m', hm, hm', hne, h1, h2⟩ := hring i hip hiq
    rcases hm with rfl | rfl <;> rcases hm' with rfl | rfl
    · exact absurd rfl hne
    · left
      simp only [ipVal] at h1 h2
      rw [sub_neg_eq_add] at h2
      exact ⟨h1.le, h2.le⟩
    · right
      simp only [ipVal] at h1 h2
      rw [sub_neg_eq_add] at h1
      exact ⟨h1.le, h2.le⟩
    · exact absurd rfl hne
  · intro i j hip hiq hjp hjq hij hsame
    obtain ⟨mi, _, hmi, _, _, hi, _⟩ := hring i hip hiq
    obtain ⟨mj, _, hmj, _, _, hj, _⟩ := hring j hjp hjq
    obtain ⟨c, hc3, hc8, hc⟩ := near_rr H x hx hinj hE p q hcap i j hip hiq hjp hjq hij
    have hcc := class_coupling H x hx hinj hE p q hcap i j hip hiq hjp hjq hij mi mj c hmi hmj hc3 hc8 hi hj hc
    have hmm : mi = mj := by
      have e1 := pos_iff_one hStar _ hh mi hmi hi
      have e2 := pos_iff_one hStar _ hh mj hmj hj
      have : (mi = 1 ↔ mj = 1) := by rw [← e1, ← e2]; exact hsame
      rcases hmi with rfl | rfl <;> rcases hmj with rfl | rfl <;> simp_all
    have hc5 : c ≤ 5 := hcc.mp hmm
    obtain ⟨v3, v4, v5, _, _, _⟩ := ipVal_ring hStar
    have hcase : c = 3 ∨ c = 4 ∨ c = 5 := by omega
    rcases hcase with rfl | rfl | rfl
    · exact ⟨1 / 2, Or.inl rfl, by rw [← v3]; exact hc.le⟩
    · exact ⟨-(1 / 2), Or.inr (Or.inl rfl), by rw [← v4]; exact hc.le⟩
    · exact ⟨-1, Or.inr (Or.inr rfl), by rw [← v5]; exact hc.le⟩
  · intro i j hip hiq hjp hjq hij hdiff
    obtain ⟨mi, _, hmi, _, _, hi, _⟩ := hring i hip hiq
    obtain ⟨mj, _, hmj, _, _, hj, _⟩ := hring j hjp hjq
    obtain ⟨c, hc3, hc8, hc⟩ := near_rr H x hx hinj hE p q hcap i j hip hiq hjp hjq hij
    have hcc := class_coupling H x hx hinj hE p q hcap i j hip hiq hjp hjq hij mi mj c hmi hmj hc3 hc8 hi hj hc
    have hmm : mi ≠ mj := by
      intro e
      apply hdiff
      have e1 := pos_iff_one hStar _ hh mi hmi hi
      have e2 := pos_iff_one hStar _ hh mj hmj hj
      rw [e1, e2, e]
    have hc5 : ¬ c ≤ 5 := fun h5 => hmm (hcc.mpr h5)
    obtain ⟨_, _, _, v6, v7, v8⟩ := ipVal_ring hStar
    have hcase : c = 6 ∨ c = 7 ∨ c = 8 := by omega
    rcases hcase with rfl | rfl | rfl
    · exact ⟨√3 / 2, Or.inl rfl, by rw [← v6]; exact hc.le⟩
    · exact ⟨0, Or.inr (Or.inl rfl), by rw [← v7]; exact hc.le⟩
    · exact ⟨-(√3 / 2), Or.inr (Or.inr rfl), by rw [← v8]; exact hc.le⟩

end N14

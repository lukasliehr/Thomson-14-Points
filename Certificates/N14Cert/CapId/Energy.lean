module

public import N14.Energy.CapThr
public import N14.Nodes
public import N14Cert.CapId.IdentCap
public import N14Cert.CapId.PatternPPR
public import N14Cert.CapId.PatternPRR
public import N14Cert.CapId.PatternRRR
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.CapId

open CAP.ThreePoint N14 N14.Box N14.Ident N14.Energy N14Cert.Height Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- **The identity of the certificate of the cap as an inequality.** For 14 points of the unit sphere and every
choice of two of them as the points of the type `P`, the Coulomb energy is at least the number `e + 364 θ` plus a
positive multiple of the sum of the slacks of all ordered triples of distinct points; `e` is the offset of the
certificate and `θ` the threshold of its three global runs, whose slack functions are the slacks of the source
minus `θ` (in the units `2 ^ s0` of the runs). The slack of a triple is `cM` times the slack function of the run
of its pattern at the inner products of the triple (`N14.Energy.TCert.slackOf_ppr`, `slackOf_prr`,
`slackOf_rrr`), and the runs bound these functions from below on their domains (the theorems `lam<Run>` of the
modules `Shift<Run>`, and `slack_nonneg` of the three global runs). -/
theorem energy_slack (x : Fin 14 → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1) (p q : Fin 14)
    (hpq : p ≠ q) :
    (304812609295633439910279097184196042327068504614344715250805707 : ℝ) / 4398046511104000000000000000000000000000000000000000000000000
        + (cert.c1 : ℝ) * dsum (slackOf cert.P cert.blk (cert.cK : ℝ) cert.psi (tau p q) x)
          / (6 * (cert.cM : ℝ) * (cert.fS : ℝ))
      ≤ ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / dist (x i) (x j) := by
  have h := cert.energy_ge cert_ok _ _ _ _ 304812609295633439910279097184196042327068504614344715250805707 4398046511104000000000000000000000000000000000000000000000000 cert_one0 cert_one1
    (by decide) (by decide) (by decide +kernel) x hx p q hpq
  push_cast at h
  exact h

/-- info: 'N14Cert.CapId.energy_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms energy_slack

set_option linter.unusedVariables false

/-- The cutoffs of the cap: the stored numbers `-0.99` and `0.8` of the source. -/
noncomputable def bLow : ℝ := ((-4458563631096791 : ℝ) / 4503599627370496)

noncomputable def tHigh : ℝ := ((3602879701896397 : ℝ) / 4503599627370496)

/-- The radius of the tubes around the nodes (`τ` of the source). -/
noncomputable def tauTube : ℝ := ((39 : ℝ) / 200000)

/-- The radius of the far region (`ρ₁` of the source). -/
noncomputable def rhoFar : ℝ := ((1 : ℝ) / 100)

/-- The threshold of the local runs in the units of the slack functions: `2 ^ s0 * θ_loc`. -/
noncomputable def GLoc : Nat := hex% "2d09370d4257360000000000000000000000000000000000000000000000000000000000000"

theorem GLoc_add : GLoc + DLocalN00 = DCoreN00 := by decide +kernel

/-- The slack of the pattern `PPR` at the inner products of the pair `P` with a third point. -/
theorem ppr_ge (u v t : ℝ) (hu : -1 ≤ u) (hv : -1 ≤ v) (ht : -1 ≤ t) (hu1 : u < 1) (hv1 : v < 1) (ht1 : t < 1)
    (hg : 0 ≤ gram u v t) (h0 : u ≤ ((-4458563631096791 : ℝ) / 4503599627370496)) (huv : u ≤ v) (hut : u ≤ t) (hvT : v ≤ ((3602879701896397 : ℝ) / 4503599627370496)) (htT : t ≤ ((3602879701896397 : ℝ) / 4503599627370496))
    (hLv : ((-4240589409132059 : ℝ) / 4503599627370496) ≤ v) (hLt : ((-4240589409132059 : ℝ) / 4503599627370496) ≤ t) :
    -(DCoreN00 : ℝ) ≤ cert.ppr.lam u v t := by
  refine ge_of_sorted23 cert.ppr.lam (cert.ppr_swap23 cert_ok)
    (fun u v t => ((-1 ≤ u ∧ -1 ≤ v ∧ -1 ≤ t) ∧ (u < 1 ∧ v < 1 ∧ t < 1) ∧ 0 ≤ gram u v t) ∧ u ≤ ((-4458563631096791 : ℝ) / 4503599627370496) ∧ (u ≤ v ∧ u ≤ t) ∧ (v ≤ ((3602879701896397 : ℝ) / 4503599627370496) ∧ t ≤ ((3602879701896397 : ℝ) / 4503599627370496)) ∧ (((-4240589409132059 : ℝ) / 4503599627370496) ≤ v ∧ ((-4240589409132059 : ℝ) / 4503599627370496) ≤ t))
    ?_ (-(DCoreN00 : ℝ)) ?_ u v t ⟨⟨⟨hu, hv, ht⟩, ⟨hu1, hv1, ht1⟩, hg⟩, h0, ⟨huv, hut⟩, ⟨hvT, htT⟩, ⟨hLv, hLt⟩⟩
  · rintro u v t ⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, e, ⟨f1, f2⟩, ⟨g1, g2⟩, ⟨h1, h2⟩⟩
    exact ⟨⟨⟨a1, a3, a2⟩, ⟨b1, b3, b2⟩, by rw [gram_swap23]; exact d⟩, e, ⟨f2, f1⟩, ⟨g2, g1⟩, ⟨h2, h1⟩⟩
  · rintro u v t hvt ⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, e, ⟨f1, f2⟩, ⟨g1, g2⟩, ⟨h1, h2⟩⟩
    exact lamPPR_ge u v t a1 a2 a3 b1 b2 b3 d (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)

/-- The slack of the pattern `PRR` at the inner products of a point of the pair `P` with two other points. -/
theorem prr_ge (u v t : ℝ) (hu : -1 ≤ u) (hv : -1 ≤ v) (ht : -1 ≤ t) (hu1 : u < 1) (hv1 : v < 1) (ht1 : t < 1)
    (hg : 0 ≤ gram u v t) (huT : u ≤ ((3602879701896397 : ℝ) / 4503599627370496)) (hvT : v ≤ ((3602879701896397 : ℝ) / 4503599627370496)) (htT : t ≤ ((3602879701896397 : ℝ) / 4503599627370496)) (hLu : ((-4240589409132059 : ℝ) / 4503599627370496) ≤ u)
    (hLv : ((-4240589409132059 : ℝ) / 4503599627370496) ≤ v) :
    -(DCoreN00 : ℝ) ≤ cert.prr.lam u v t := by
  refine ge_of_sorted12 cert.prr.lam (cert.prr_swap12 cert_ok)
    (fun u v t => ((-1 ≤ u ∧ -1 ≤ v ∧ -1 ≤ t) ∧ (u < 1 ∧ v < 1 ∧ t < 1) ∧ 0 ≤ gram u v t) ∧ (u ≤ ((3602879701896397 : ℝ) / 4503599627370496) ∧ v ≤ ((3602879701896397 : ℝ) / 4503599627370496)) ∧ t ≤ ((3602879701896397 : ℝ) / 4503599627370496) ∧ (((-4240589409132059 : ℝ) / 4503599627370496) ≤ u ∧ ((-4240589409132059 : ℝ) / 4503599627370496) ≤ v))
    ?_ (-(DCoreN00 : ℝ)) ?_ u v t ⟨⟨⟨hu, hv, ht⟩, ⟨hu1, hv1, ht1⟩, hg⟩, ⟨huT, hvT⟩, htT, ⟨hLu, hLv⟩⟩
  · rintro u v t ⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, ⟨f1, f2⟩, g, ⟨h1, h2⟩⟩
    exact ⟨⟨⟨a2, a1, a3⟩, ⟨b2, b1, b3⟩, by rw [gram_swap12]; exact d⟩, ⟨f2, f1⟩, g, ⟨h2, h1⟩⟩
  · rintro u v t huv ⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, ⟨f1, f2⟩, g, ⟨h1, h2⟩⟩
    exact lamPRR_ge u v t a1 a2 a3 b1 b2 b3 d (by linarith) (by linarith) (by linarith) (by linarith)

/-- The slack of the pattern `RRR` at the inner products of three points outside the pair `P`. -/
theorem rrr_ge (u v t : ℝ) (hu : -1 ≤ u) (hv : -1 ≤ v) (ht : -1 ≤ t) (hu1 : u < 1) (hv1 : v < 1) (ht1 : t < 1)
    (hg : 0 ≤ gram u v t) (huT : u ≤ ((3602879701896397 : ℝ) / 4503599627370496)) (hvT : v ≤ ((3602879701896397 : ℝ) / 4503599627370496)) (htT : t ≤ ((3602879701896397 : ℝ) / 4503599627370496)) :
    -(DCoreN00 : ℝ) ≤ cert.rrr.lam u v t := by
  refine ge_of_sorted cert.rrr.lam (cert.rrr_swap12 cert_ok) (cert.rrr_swap23 cert_ok)
    (fun u v t => ((-1 ≤ u ∧ -1 ≤ v ∧ -1 ≤ t) ∧ (u < 1 ∧ v < 1 ∧ t < 1) ∧ 0 ≤ gram u v t) ∧ u ≤ ((3602879701896397 : ℝ) / 4503599627370496) ∧ v ≤ ((3602879701896397 : ℝ) / 4503599627370496) ∧ t ≤ ((3602879701896397 : ℝ) / 4503599627370496))
    ?_ ?_ (-(DCoreN00 : ℝ)) ?_ u v t ⟨⟨⟨hu, hv, ht⟩, ⟨hu1, hv1, ht1⟩, hg⟩, huT, hvT, htT⟩
  · rintro u v t ⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, f1, f2, f3⟩
    exact ⟨⟨⟨a2, a1, a3⟩, ⟨b2, b1, b3⟩, by rw [gram_swap12]; exact d⟩, f2, f1, f3⟩
  · rintro u v t ⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, f1, f2, f3⟩
    exact ⟨⟨⟨a1, a3, a2⟩, ⟨b1, b3, b2⟩, by rw [gram_swap23]; exact d⟩, f1, f3, f2⟩
  · rintro u v t huv hvt ⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, f1, f2, f3⟩
    exact lamRRR_ge u v t a1 a2 a3 b1 b2 b3 d (by linarith) (by linarith) (by linarith)

/-- The slack of the pattern `PPR` at the inner products of the pair `P` with a third point at a point that is not within `τ` of a node. -/
theorem ppr_loc (u v t : ℝ) (hu : -1 ≤ u) (hv : -1 ≤ v) (ht : -1 ≤ t) (hu1 : u < 1) (hv1 : v < 1) (ht1 : t < 1)
    (hg : 0 ≤ gram u v t) (h0 : u ≤ ((-4458563631096791 : ℝ) / 4503599627370496)) (huv : u ≤ v) (hut : u ≤ t) (hvT : v ≤ ((3602879701896397 : ℝ) / 4503599627370496)) (htT : t ≤ ((3602879701896397 : ℝ) / 4503599627370496))
    (hLv : ((-4240589409132059 : ℝ) / 4503599627370496) ≤ v) (hLt : ((-4240589409132059 : ℝ) / 4503599627370496) ≤ t)
    (hfar : FarAll hStar ((39 : ℝ) / 200000) 0 0 1 u v t) :
    -(DLocalN00 : ℝ) ≤ cert.ppr.lam u v t := by
  refine ge_of_sorted23 cert.ppr.lam (cert.ppr_swap23 cert_ok)
    (fun u v t => (((-1 ≤ u ∧ -1 ≤ v ∧ -1 ≤ t) ∧ (u < 1 ∧ v < 1 ∧ t < 1) ∧ 0 ≤ gram u v t) ∧ u ≤ ((-4458563631096791 : ℝ) / 4503599627370496) ∧ (u ≤ v ∧ u ≤ t) ∧ (v ≤ ((3602879701896397 : ℝ) / 4503599627370496) ∧ t ≤ ((3602879701896397 : ℝ) / 4503599627370496)) ∧ (((-4240589409132059 : ℝ) / 4503599627370496) ≤ v ∧ ((-4240589409132059 : ℝ) / 4503599627370496) ≤ t)) ∧ FarAll hStar ((39 : ℝ) / 200000) 0 0 1 u v t)
    ?_ (-(DLocalN00 : ℝ)) ?_ u v t ⟨⟨⟨⟨hu, hv, ht⟩, ⟨hu1, hv1, ht1⟩, hg⟩, h0, ⟨huv, hut⟩, ⟨hvT, htT⟩, ⟨hLv, hLt⟩⟩, hfar⟩
  · rintro u v t ⟨⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, e, ⟨f1, f2⟩, ⟨g1, g2⟩, ⟨h1, h2⟩⟩, hf⟩
    exact ⟨⟨⟨⟨a1, a3, a2⟩, ⟨b1, b3, b2⟩, by rw [gram_swap23]; exact d⟩, e, ⟨f2, f1⟩, ⟨g2, g1⟩, ⟨h2, h1⟩⟩, hf.swap12⟩
  · rintro u v t hvt ⟨⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, e, ⟨f1, f2⟩, ⟨g1, g2⟩, ⟨h1, h2⟩⟩, hf⟩
    exact lamPPR_loc u v t a1 a2 a3 b1 b2 b3 d (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hf

/-- The slack of the pattern `PRR` at the inner products of a point of the pair `P` with two other points at a point that is not within `τ` of a node. -/
theorem prr_loc (u v t : ℝ) (hu : -1 ≤ u) (hv : -1 ≤ v) (ht : -1 ≤ t) (hu1 : u < 1) (hv1 : v < 1) (ht1 : t < 1)
    (hg : 0 ≤ gram u v t) (huT : u ≤ ((3602879701896397 : ℝ) / 4503599627370496)) (hvT : v ≤ ((3602879701896397 : ℝ) / 4503599627370496)) (htT : t ≤ ((3602879701896397 : ℝ) / 4503599627370496)) (hLu : ((-4240589409132059 : ℝ) / 4503599627370496) ≤ u)
    (hLv : ((-4240589409132059 : ℝ) / 4503599627370496) ≤ v)
    (hfar : FarAll hStar ((39 : ℝ) / 200000) 0 1 1 u v t) :
    -(DLocalN00 : ℝ) ≤ cert.prr.lam u v t := by
  refine ge_of_sorted12 cert.prr.lam (cert.prr_swap12 cert_ok)
    (fun u v t => (((-1 ≤ u ∧ -1 ≤ v ∧ -1 ≤ t) ∧ (u < 1 ∧ v < 1 ∧ t < 1) ∧ 0 ≤ gram u v t) ∧ (u ≤ ((3602879701896397 : ℝ) / 4503599627370496) ∧ v ≤ ((3602879701896397 : ℝ) / 4503599627370496)) ∧ t ≤ ((3602879701896397 : ℝ) / 4503599627370496) ∧ (((-4240589409132059 : ℝ) / 4503599627370496) ≤ u ∧ ((-4240589409132059 : ℝ) / 4503599627370496) ≤ v)) ∧ FarAll hStar ((39 : ℝ) / 200000) 0 1 1 u v t)
    ?_ (-(DLocalN00 : ℝ)) ?_ u v t ⟨⟨⟨⟨hu, hv, ht⟩, ⟨hu1, hv1, ht1⟩, hg⟩, ⟨huT, hvT⟩, htT, ⟨hLu, hLv⟩⟩, hfar⟩
  · rintro u v t ⟨⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, ⟨f1, f2⟩, g, ⟨h1, h2⟩⟩, hf⟩
    exact ⟨⟨⟨⟨a2, a1, a3⟩, ⟨b2, b1, b3⟩, by rw [gram_swap12]; exact d⟩, ⟨f2, f1⟩, g, ⟨h2, h1⟩⟩, hf.swap23⟩
  · rintro u v t huv ⟨⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, ⟨f1, f2⟩, g, ⟨h1, h2⟩⟩, hf⟩
    exact lamPRR_loc u v t a1 a2 a3 b1 b2 b3 d (by linarith) (by linarith) (by linarith) (by linarith) hf

/-- The slack of the pattern `RRR` at the inner products of three points outside the pair `P` at a point that is not within `τ` of a node. -/
theorem rrr_loc (u v t : ℝ) (hu : -1 ≤ u) (hv : -1 ≤ v) (ht : -1 ≤ t) (hu1 : u < 1) (hv1 : v < 1) (ht1 : t < 1)
    (hg : 0 ≤ gram u v t) (huT : u ≤ ((3602879701896397 : ℝ) / 4503599627370496)) (hvT : v ≤ ((3602879701896397 : ℝ) / 4503599627370496)) (htT : t ≤ ((3602879701896397 : ℝ) / 4503599627370496))
    (hfar : FarAll hStar ((39 : ℝ) / 200000) 1 1 1 u v t) :
    -(DLocalN00 : ℝ) ≤ cert.rrr.lam u v t := by
  refine ge_of_sorted cert.rrr.lam (cert.rrr_swap12 cert_ok) (cert.rrr_swap23 cert_ok)
    (fun u v t => (((-1 ≤ u ∧ -1 ≤ v ∧ -1 ≤ t) ∧ (u < 1 ∧ v < 1 ∧ t < 1) ∧ 0 ≤ gram u v t) ∧ u ≤ ((3602879701896397 : ℝ) / 4503599627370496) ∧ v ≤ ((3602879701896397 : ℝ) / 4503599627370496) ∧ t ≤ ((3602879701896397 : ℝ) / 4503599627370496)) ∧ FarAll hStar ((39 : ℝ) / 200000) 1 1 1 u v t)
    ?_ ?_ (-(DLocalN00 : ℝ)) ?_ u v t ⟨⟨⟨⟨hu, hv, ht⟩, ⟨hu1, hv1, ht1⟩, hg⟩, huT, hvT, htT⟩, hfar⟩
  · rintro u v t ⟨⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, f1, f2, f3⟩, hf⟩
    exact ⟨⟨⟨⟨a2, a1, a3⟩, ⟨b2, b1, b3⟩, by rw [gram_swap12]; exact d⟩, f2, f1, f3⟩, hf.swap23⟩
  · rintro u v t ⟨⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, f1, f2, f3⟩, hf⟩
    exact ⟨⟨⟨⟨a1, a3, a2⟩, ⟨b1, b3, b2⟩, by rw [gram_swap23]; exact d⟩, f1, f3, f2⟩, hf.swap12⟩
  · rintro u v t huv hvt ⟨⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, f1, f2, f3⟩, hf⟩
    exact lamRRR_loc u v t a1 a2 a3 b1 b2 b3 d (by linarith) (by linarith) (by linarith) hf

/-- The slack of the pattern `PPR` at the inner products of the pair `P` with a third point at a point that is not within `ρ₁` of a node. -/
theorem ppr_far (u v t : ℝ) (hu : -1 ≤ u) (hv : -1 ≤ v) (ht : -1 ≤ t) (hu1 : u < 1) (hv1 : v < 1) (ht1 : t < 1)
    (hg : 0 ≤ gram u v t) (h0 : u ≤ ((-4458563631096791 : ℝ) / 4503599627370496)) (huv : u ≤ v) (hut : u ≤ t) (hvT : v ≤ ((3602879701896397 : ℝ) / 4503599627370496)) (htT : t ≤ ((3602879701896397 : ℝ) / 4503599627370496))
    (hLv : ((-4240589409132059 : ℝ) / 4503599627370496) ≤ v) (hLt : ((-4240589409132059 : ℝ) / 4503599627370496) ≤ t)
    (hfar : FarAll hStar ((1 : ℝ) / 100) 0 0 1 u v t) :
    (0 : ℝ) ≤ cert.ppr.lam u v t := by
  refine ge_of_sorted23 cert.ppr.lam (cert.ppr_swap23 cert_ok)
    (fun u v t => (((-1 ≤ u ∧ -1 ≤ v ∧ -1 ≤ t) ∧ (u < 1 ∧ v < 1 ∧ t < 1) ∧ 0 ≤ gram u v t) ∧ u ≤ ((-4458563631096791 : ℝ) / 4503599627370496) ∧ (u ≤ v ∧ u ≤ t) ∧ (v ≤ ((3602879701896397 : ℝ) / 4503599627370496) ∧ t ≤ ((3602879701896397 : ℝ) / 4503599627370496)) ∧ (((-4240589409132059 : ℝ) / 4503599627370496) ≤ v ∧ ((-4240589409132059 : ℝ) / 4503599627370496) ≤ t)) ∧ FarAll hStar ((1 : ℝ) / 100) 0 0 1 u v t)
    ?_ ((0 : ℝ)) ?_ u v t ⟨⟨⟨⟨hu, hv, ht⟩, ⟨hu1, hv1, ht1⟩, hg⟩, h0, ⟨huv, hut⟩, ⟨hvT, htT⟩, ⟨hLv, hLt⟩⟩, hfar⟩
  · rintro u v t ⟨⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, e, ⟨f1, f2⟩, ⟨g1, g2⟩, ⟨h1, h2⟩⟩, hf⟩
    exact ⟨⟨⟨⟨a1, a3, a2⟩, ⟨b1, b3, b2⟩, by rw [gram_swap23]; exact d⟩, e, ⟨f2, f1⟩, ⟨g2, g1⟩, ⟨h2, h1⟩⟩, hf.swap12⟩
  · rintro u v t hvt ⟨⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, e, ⟨f1, f2⟩, ⟨g1, g2⟩, ⟨h1, h2⟩⟩, hf⟩
    exact lamPPR_far u v t a1 a2 a3 b1 b2 b3 d (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hf

/-- The slack of the pattern `PRR` at the inner products of a point of the pair `P` with two other points at a point that is not within `ρ₁` of a node. -/
theorem prr_far (u v t : ℝ) (hu : -1 ≤ u) (hv : -1 ≤ v) (ht : -1 ≤ t) (hu1 : u < 1) (hv1 : v < 1) (ht1 : t < 1)
    (hg : 0 ≤ gram u v t) (huT : u ≤ ((3602879701896397 : ℝ) / 4503599627370496)) (hvT : v ≤ ((3602879701896397 : ℝ) / 4503599627370496)) (htT : t ≤ ((3602879701896397 : ℝ) / 4503599627370496)) (hLu : ((-4240589409132059 : ℝ) / 4503599627370496) ≤ u)
    (hLv : ((-4240589409132059 : ℝ) / 4503599627370496) ≤ v)
    (hfar : FarAll hStar ((1 : ℝ) / 100) 0 1 1 u v t) :
    (0 : ℝ) ≤ cert.prr.lam u v t := by
  refine ge_of_sorted12 cert.prr.lam (cert.prr_swap12 cert_ok)
    (fun u v t => (((-1 ≤ u ∧ -1 ≤ v ∧ -1 ≤ t) ∧ (u < 1 ∧ v < 1 ∧ t < 1) ∧ 0 ≤ gram u v t) ∧ (u ≤ ((3602879701896397 : ℝ) / 4503599627370496) ∧ v ≤ ((3602879701896397 : ℝ) / 4503599627370496)) ∧ t ≤ ((3602879701896397 : ℝ) / 4503599627370496) ∧ (((-4240589409132059 : ℝ) / 4503599627370496) ≤ u ∧ ((-4240589409132059 : ℝ) / 4503599627370496) ≤ v)) ∧ FarAll hStar ((1 : ℝ) / 100) 0 1 1 u v t)
    ?_ ((0 : ℝ)) ?_ u v t ⟨⟨⟨⟨hu, hv, ht⟩, ⟨hu1, hv1, ht1⟩, hg⟩, ⟨huT, hvT⟩, htT, ⟨hLu, hLv⟩⟩, hfar⟩
  · rintro u v t ⟨⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, ⟨f1, f2⟩, g, ⟨h1, h2⟩⟩, hf⟩
    exact ⟨⟨⟨⟨a2, a1, a3⟩, ⟨b2, b1, b3⟩, by rw [gram_swap12]; exact d⟩, ⟨f2, f1⟩, g, ⟨h2, h1⟩⟩, hf.swap23⟩
  · rintro u v t huv ⟨⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, ⟨f1, f2⟩, g, ⟨h1, h2⟩⟩, hf⟩
    exact lamPRR_far u v t a1 a2 a3 b1 b2 b3 d (by linarith) (by linarith) (by linarith) (by linarith) hf

/-- The slack of the pattern `RRR` at the inner products of three points outside the pair `P` at a point that is not within `ρ₁` of a node. -/
theorem rrr_far (u v t : ℝ) (hu : -1 ≤ u) (hv : -1 ≤ v) (ht : -1 ≤ t) (hu1 : u < 1) (hv1 : v < 1) (ht1 : t < 1)
    (hg : 0 ≤ gram u v t) (huT : u ≤ ((3602879701896397 : ℝ) / 4503599627370496)) (hvT : v ≤ ((3602879701896397 : ℝ) / 4503599627370496)) (htT : t ≤ ((3602879701896397 : ℝ) / 4503599627370496))
    (hfar : FarAll hStar ((1 : ℝ) / 100) 1 1 1 u v t) :
    (0 : ℝ) ≤ cert.rrr.lam u v t := by
  refine ge_of_sorted cert.rrr.lam (cert.rrr_swap12 cert_ok) (cert.rrr_swap23 cert_ok)
    (fun u v t => (((-1 ≤ u ∧ -1 ≤ v ∧ -1 ≤ t) ∧ (u < 1 ∧ v < 1 ∧ t < 1) ∧ 0 ≤ gram u v t) ∧ u ≤ ((3602879701896397 : ℝ) / 4503599627370496) ∧ v ≤ ((3602879701896397 : ℝ) / 4503599627370496) ∧ t ≤ ((3602879701896397 : ℝ) / 4503599627370496)) ∧ FarAll hStar ((1 : ℝ) / 100) 1 1 1 u v t)
    ?_ ?_ ((0 : ℝ)) ?_ u v t ⟨⟨⟨⟨hu, hv, ht⟩, ⟨hu1, hv1, ht1⟩, hg⟩, huT, hvT, htT⟩, hfar⟩
  · rintro u v t ⟨⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, f1, f2, f3⟩, hf⟩
    exact ⟨⟨⟨⟨a2, a1, a3⟩, ⟨b2, b1, b3⟩, by rw [gram_swap12]; exact d⟩, f2, f1, f3⟩, hf.swap23⟩
  · rintro u v t ⟨⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, f1, f2, f3⟩, hf⟩
    exact ⟨⟨⟨⟨a1, a3, a2⟩, ⟨b1, b3, b2⟩, by rw [gram_swap23]; exact d⟩, f1, f3, f2⟩, hf.swap12⟩
  · rintro u v t huv hvt ⟨⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, d⟩, f1, f2, f3⟩, hf⟩
    exact lamRRR_far u v t a1 a2 a3 b1 b2 b3 d (by linarith) (by linarith) (by linarith) hf

theorem cfg_ppr_ge (x : Fin 14 → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1)
    (hinj : Function.Injective x) (p q : Fin 14) (hpq : p ≠ q)
    (hmin : ∀ i j, i ≠ j → inner ℝ (x p) (x q) ≤ inner ℝ (x i) (x j))
    (hlow : inner ℝ (x p) (x q) ≤ bLow) (hhigh : ∀ i j, i ≠ j → inner ℝ (x i) (x j) ≤ tHigh) (k : Fin 14) (hkp : k ≠ p) (hkq : k ≠ q) :
    -(DCoreN00 : ℝ) ≤ cert.ppr.lam (ip x p q) (ip x p k) (ip x q k) := by
  unfold bLow at hlow
  have hT : ∀ i j, i ≠ j → ip x i j ≤ ((3602879701896397 : ℝ) / 4503599627370496) := fun i j hij => by
    have h := hhigh i j hij
    unfold tHigh at h
    exact h
  have hL : ∀ a b k, ip x a b ≤ ((-4458563631096791 : ℝ) / 4503599627370496) → k ≠ b → ((-4240589409132059 : ℝ) / 4503599627370496) ≤ ip x a k := fun a b k hab hkb =>
    far_pair_bound (ip x a b) (ip x a k) (ip x b k) ((-4458563631096791 : ℝ) / 4503599627370496) ((3602879701896397 : ℝ) / 4503599627370496) ((-4240589409132059 : ℝ) / 4503599627370496) (neg_one_le_ip x hx a b) hab
      (by norm_num) (hT b k (Ne.symm hkb)) (by norm_num) (by norm_num) (by norm_num) (gram_ip x hx a b k)
  have hqp : ip x q p ≤ ((-4458563631096791 : ℝ) / 4503599627370496) := (le_of_eq (real_inner_comm (x p) (x q))).trans hlow
  exact ppr_ge _ _ _ (neg_one_le_ip x hx p q) (neg_one_le_ip x hx p k) (neg_one_le_ip x hx q k)
    (ip_lt_one x hx hinj hpq) (ip_lt_one x hx hinj (Ne.symm hkp)) (ip_lt_one x hx hinj (Ne.symm hkq))
    (gram_ip x hx p q k) hlow (hmin p k (Ne.symm hkp)) (hmin q k (Ne.symm hkq)) (hT p k (Ne.symm hkp))
    (hT q k (Ne.symm hkq)) (hL p q k hlow hkq) (hL q p k hqp hkp)

theorem cfg_prr_ge (x : Fin 14 → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1)
    (hinj : Function.Injective x) (p q : Fin 14) (hpq : p ≠ q)
    (hmin : ∀ i j, i ≠ j → inner ℝ (x p) (x q) ≤ inner ℝ (x i) (x j))
    (hlow : inner ℝ (x p) (x q) ≤ bLow) (hhigh : ∀ i j, i ≠ j → inner ℝ (x i) (x j) ≤ tHigh) (i j k : Fin 14) (hi : i = p ∨ i = q) (hjp : j ≠ p) (hjq : j ≠ q)
    (hkp : k ≠ p) (hkq : k ≠ q) (hjk : j ≠ k) :
    -(DCoreN00 : ℝ) ≤ cert.prr.lam (ip x i j) (ip x i k) (ip x j k) := by
  unfold bLow at hlow
  have hT : ∀ i j, i ≠ j → ip x i j ≤ ((3602879701896397 : ℝ) / 4503599627370496) := fun i j hij => by
    have h := hhigh i j hij
    unfold tHigh at h
    exact h
  have hL : ∀ a b k, ip x a b ≤ ((-4458563631096791 : ℝ) / 4503599627370496) → k ≠ b → ((-4240589409132059 : ℝ) / 4503599627370496) ≤ ip x a k := fun a b k hab hkb =>
    far_pair_bound (ip x a b) (ip x a k) (ip x b k) ((-4458563631096791 : ℝ) / 4503599627370496) ((3602879701896397 : ℝ) / 4503599627370496) ((-4240589409132059 : ℝ) / 4503599627370496) (neg_one_le_ip x hx a b) hab
      (by norm_num) (hT b k (Ne.symm hkb)) (by norm_num) (by norm_num) (by norm_num) (gram_ip x hx a b k)
  have hqp : ip x q p ≤ ((-4458563631096791 : ℝ) / 4503599627370496) := (le_of_eq (real_inner_comm (x p) (x q))).trans hlow
  rcases hi with rfl | rfl
  · exact prr_ge _ _ _ (neg_one_le_ip x hx i j) (neg_one_le_ip x hx i k) (neg_one_le_ip x hx j k)
      (ip_lt_one x hx hinj (Ne.symm hjp)) (ip_lt_one x hx hinj (Ne.symm hkp)) (ip_lt_one x hx hinj hjk)
      (gram_ip x hx i j k) (hT i j (Ne.symm hjp)) (hT i k (Ne.symm hkp)) (hT j k hjk)
      (hL i q j hlow hjq) (hL i q k hlow hkq)
  · exact prr_ge _ _ _ (neg_one_le_ip x hx i j) (neg_one_le_ip x hx i k) (neg_one_le_ip x hx j k)
      (ip_lt_one x hx hinj (Ne.symm hjq)) (ip_lt_one x hx hinj (Ne.symm hkq)) (ip_lt_one x hx hinj hjk)
      (gram_ip x hx i j k) (hT i j (Ne.symm hjq)) (hT i k (Ne.symm hkq)) (hT j k hjk)
      (hL i p j hqp hjp) (hL i p k hqp hkp)

theorem cfg_rrr_ge (x : Fin 14 → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1)
    (hinj : Function.Injective x) (p q : Fin 14) (hpq : p ≠ q)
    (hmin : ∀ i j, i ≠ j → inner ℝ (x p) (x q) ≤ inner ℝ (x i) (x j))
    (hlow : inner ℝ (x p) (x q) ≤ bLow) (hhigh : ∀ i j, i ≠ j → inner ℝ (x i) (x j) ≤ tHigh) (i j k : Fin 14) (hip : i ≠ p) (hiq : i ≠ q) (hjp : j ≠ p) (hjq : j ≠ q)
    (hkp : k ≠ p) (hkq : k ≠ q) (hd : Distinct3 i j k) :
    -(DCoreN00 : ℝ) ≤ cert.rrr.lam (ip x i j) (ip x i k) (ip x j k) := by
  have hT : ∀ i j, i ≠ j → ip x i j ≤ ((3602879701896397 : ℝ) / 4503599627370496) := fun i j hij => by
    have h := hhigh i j hij
    unfold tHigh at h
    exact h
  exact rrr_ge _ _ _ (neg_one_le_ip x hx i j) (neg_one_le_ip x hx i k)
    (neg_one_le_ip x hx j k) (ip_lt_one x hx hinj hd.1) (ip_lt_one x hx hinj hd.2.1)
    (ip_lt_one x hx hinj hd.2.2) (gram_ip x hx i j k) (hT i j hd.1) (hT i k hd.2.1) (hT j k hd.2.2)

theorem cfg_ppr_loc (x : Fin 14 → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1)
    (hinj : Function.Injective x) (p q : Fin 14) (hpq : p ≠ q)
    (hmin : ∀ i j, i ≠ j → inner ℝ (x p) (x q) ≤ inner ℝ (x i) (x j))
    (hlow : inner ℝ (x p) (x q) ≤ bLow) (hhigh : ∀ i j, i ≠ j → inner ℝ (x i) (x j) ≤ tHigh) (k : Fin 14) (hkp : k ≠ p) (hkq : k ≠ q) (hF : Far hStar ((39 : ℝ) / 200000) x p q p q k) :
    -(DLocalN00 : ℝ) ≤ cert.ppr.lam (ip x p q) (ip x p k) (ip x q k) := by
  unfold bLow at hlow
  have hT : ∀ i j, i ≠ j → ip x i j ≤ ((3602879701896397 : ℝ) / 4503599627370496) := fun i j hij => by
    have h := hhigh i j hij
    unfold tHigh at h
    exact h
  have hL : ∀ a b k, ip x a b ≤ ((-4458563631096791 : ℝ) / 4503599627370496) → k ≠ b → ((-4240589409132059 : ℝ) / 4503599627370496) ≤ ip x a k := fun a b k hab hkb =>
    far_pair_bound (ip x a b) (ip x a k) (ip x b k) ((-4458563631096791 : ℝ) / 4503599627370496) ((3602879701896397 : ℝ) / 4503599627370496) ((-4240589409132059 : ℝ) / 4503599627370496) (neg_one_le_ip x hx a b) hab
      (by norm_num) (hT b k (Ne.symm hkb)) (by norm_num) (by norm_num) (by norm_num) (gram_ip x hx a b k)
  have hqp : ip x q p ≤ ((-4458563631096791 : ℝ) / 4503599627370496) := (le_of_eq (real_inner_comm (x p) (x q))).trans hlow
  exact ppr_loc _ _ _ (neg_one_le_ip x hx p q) (neg_one_le_ip x hx p k) (neg_one_le_ip x hx q k)
    (ip_lt_one x hx hinj hpq) (ip_lt_one x hx hinj (Ne.symm hkp)) (ip_lt_one x hx hinj (Ne.symm hkq))
    (gram_ip x hx p q k) hlow (hmin p k (Ne.symm hkp)) (hmin q k (Ne.symm hkq)) (hT p k (Ne.symm hkp))
    (hT q k (Ne.symm hkq)) (hL p q k hlow hkq) (hL q p k hqp hkp)
      (by have h := hF; unfold Far at h; rwa [tau_left, tau_right, tau_other hkp hkq] at h)

theorem cfg_prr_loc (x : Fin 14 → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1)
    (hinj : Function.Injective x) (p q : Fin 14) (hpq : p ≠ q)
    (hmin : ∀ i j, i ≠ j → inner ℝ (x p) (x q) ≤ inner ℝ (x i) (x j))
    (hlow : inner ℝ (x p) (x q) ≤ bLow) (hhigh : ∀ i j, i ≠ j → inner ℝ (x i) (x j) ≤ tHigh) (i j k : Fin 14) (hi : i = p ∨ i = q) (hjp : j ≠ p) (hjq : j ≠ q)
    (hkp : k ≠ p) (hkq : k ≠ q) (hjk : j ≠ k) (hF : Far hStar ((39 : ℝ) / 200000) x p q i j k) :
    -(DLocalN00 : ℝ) ≤ cert.prr.lam (ip x i j) (ip x i k) (ip x j k) := by
  unfold bLow at hlow
  have hT : ∀ i j, i ≠ j → ip x i j ≤ ((3602879701896397 : ℝ) / 4503599627370496) := fun i j hij => by
    have h := hhigh i j hij
    unfold tHigh at h
    exact h
  have hL : ∀ a b k, ip x a b ≤ ((-4458563631096791 : ℝ) / 4503599627370496) → k ≠ b → ((-4240589409132059 : ℝ) / 4503599627370496) ≤ ip x a k := fun a b k hab hkb =>
    far_pair_bound (ip x a b) (ip x a k) (ip x b k) ((-4458563631096791 : ℝ) / 4503599627370496) ((3602879701896397 : ℝ) / 4503599627370496) ((-4240589409132059 : ℝ) / 4503599627370496) (neg_one_le_ip x hx a b) hab
      (by norm_num) (hT b k (Ne.symm hkb)) (by norm_num) (by norm_num) (by norm_num) (gram_ip x hx a b k)
  have hqp : ip x q p ≤ ((-4458563631096791 : ℝ) / 4503599627370496) := (le_of_eq (real_inner_comm (x p) (x q))).trans hlow
  rcases hi with rfl | rfl
  · exact prr_loc _ _ _ (neg_one_le_ip x hx i j) (neg_one_le_ip x hx i k) (neg_one_le_ip x hx j k)
      (ip_lt_one x hx hinj (Ne.symm hjp)) (ip_lt_one x hx hinj (Ne.symm hkp)) (ip_lt_one x hx hinj hjk)
      (gram_ip x hx i j k) (hT i j (Ne.symm hjp)) (hT i k (Ne.symm hkp)) (hT j k hjk)
      (hL i q j hlow hjq) (hL i q k hlow hkq)
        (by have h := hF; unfold Far at h; rwa [tau_left, tau_other hjp hjq, tau_other hkp hkq] at h)
  · exact prr_loc _ _ _ (neg_one_le_ip x hx i j) (neg_one_le_ip x hx i k) (neg_one_le_ip x hx j k)
      (ip_lt_one x hx hinj (Ne.symm hjq)) (ip_lt_one x hx hinj (Ne.symm hkq)) (ip_lt_one x hx hinj hjk)
      (gram_ip x hx i j k) (hT i j (Ne.symm hjq)) (hT i k (Ne.symm hkq)) (hT j k hjk)
      (hL i p j hqp hjp) (hL i p k hqp hkp)
        (by have h := hF; unfold Far at h; rwa [tau_right, tau_other hjp hjq, tau_other hkp hkq] at h)

theorem cfg_rrr_loc (x : Fin 14 → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1)
    (hinj : Function.Injective x) (p q : Fin 14) (hpq : p ≠ q)
    (hmin : ∀ i j, i ≠ j → inner ℝ (x p) (x q) ≤ inner ℝ (x i) (x j))
    (hlow : inner ℝ (x p) (x q) ≤ bLow) (hhigh : ∀ i j, i ≠ j → inner ℝ (x i) (x j) ≤ tHigh) (i j k : Fin 14) (hip : i ≠ p) (hiq : i ≠ q) (hjp : j ≠ p) (hjq : j ≠ q)
    (hkp : k ≠ p) (hkq : k ≠ q) (hd : Distinct3 i j k) (hF : Far hStar ((39 : ℝ) / 200000) x p q i j k) :
    -(DLocalN00 : ℝ) ≤ cert.rrr.lam (ip x i j) (ip x i k) (ip x j k) := by
  have hT : ∀ i j, i ≠ j → ip x i j ≤ ((3602879701896397 : ℝ) / 4503599627370496) := fun i j hij => by
    have h := hhigh i j hij
    unfold tHigh at h
    exact h
  exact rrr_loc _ _ _ (neg_one_le_ip x hx i j) (neg_one_le_ip x hx i k)
    (neg_one_le_ip x hx j k) (ip_lt_one x hx hinj hd.1) (ip_lt_one x hx hinj hd.2.1)
    (ip_lt_one x hx hinj hd.2.2) (gram_ip x hx i j k) (hT i j hd.1) (hT i k hd.2.1) (hT j k hd.2.2)
    (by have h := hF; unfold Far at h; rwa [tau_other hip hiq, tau_other hjp hjq, tau_other hkp hkq] at h)

theorem cfg_ppr_far (x : Fin 14 → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1)
    (hinj : Function.Injective x) (p q : Fin 14) (hpq : p ≠ q)
    (hmin : ∀ i j, i ≠ j → inner ℝ (x p) (x q) ≤ inner ℝ (x i) (x j))
    (hlow : inner ℝ (x p) (x q) ≤ bLow) (hhigh : ∀ i j, i ≠ j → inner ℝ (x i) (x j) ≤ tHigh) (k : Fin 14) (hkp : k ≠ p) (hkq : k ≠ q) (hF : Far hStar ((1 : ℝ) / 100) x p q p q k) :
    (0 : ℝ) ≤ cert.ppr.lam (ip x p q) (ip x p k) (ip x q k) := by
  unfold bLow at hlow
  have hT : ∀ i j, i ≠ j → ip x i j ≤ ((3602879701896397 : ℝ) / 4503599627370496) := fun i j hij => by
    have h := hhigh i j hij
    unfold tHigh at h
    exact h
  have hL : ∀ a b k, ip x a b ≤ ((-4458563631096791 : ℝ) / 4503599627370496) → k ≠ b → ((-4240589409132059 : ℝ) / 4503599627370496) ≤ ip x a k := fun a b k hab hkb =>
    far_pair_bound (ip x a b) (ip x a k) (ip x b k) ((-4458563631096791 : ℝ) / 4503599627370496) ((3602879701896397 : ℝ) / 4503599627370496) ((-4240589409132059 : ℝ) / 4503599627370496) (neg_one_le_ip x hx a b) hab
      (by norm_num) (hT b k (Ne.symm hkb)) (by norm_num) (by norm_num) (by norm_num) (gram_ip x hx a b k)
  have hqp : ip x q p ≤ ((-4458563631096791 : ℝ) / 4503599627370496) := (le_of_eq (real_inner_comm (x p) (x q))).trans hlow
  exact ppr_far _ _ _ (neg_one_le_ip x hx p q) (neg_one_le_ip x hx p k) (neg_one_le_ip x hx q k)
    (ip_lt_one x hx hinj hpq) (ip_lt_one x hx hinj (Ne.symm hkp)) (ip_lt_one x hx hinj (Ne.symm hkq))
    (gram_ip x hx p q k) hlow (hmin p k (Ne.symm hkp)) (hmin q k (Ne.symm hkq)) (hT p k (Ne.symm hkp))
    (hT q k (Ne.symm hkq)) (hL p q k hlow hkq) (hL q p k hqp hkp)
      (by have h := hF; unfold Far at h; rwa [tau_left, tau_right, tau_other hkp hkq] at h)

theorem cfg_prr_far (x : Fin 14 → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1)
    (hinj : Function.Injective x) (p q : Fin 14) (hpq : p ≠ q)
    (hmin : ∀ i j, i ≠ j → inner ℝ (x p) (x q) ≤ inner ℝ (x i) (x j))
    (hlow : inner ℝ (x p) (x q) ≤ bLow) (hhigh : ∀ i j, i ≠ j → inner ℝ (x i) (x j) ≤ tHigh) (i j k : Fin 14) (hi : i = p ∨ i = q) (hjp : j ≠ p) (hjq : j ≠ q)
    (hkp : k ≠ p) (hkq : k ≠ q) (hjk : j ≠ k) (hF : Far hStar ((1 : ℝ) / 100) x p q i j k) :
    (0 : ℝ) ≤ cert.prr.lam (ip x i j) (ip x i k) (ip x j k) := by
  unfold bLow at hlow
  have hT : ∀ i j, i ≠ j → ip x i j ≤ ((3602879701896397 : ℝ) / 4503599627370496) := fun i j hij => by
    have h := hhigh i j hij
    unfold tHigh at h
    exact h
  have hL : ∀ a b k, ip x a b ≤ ((-4458563631096791 : ℝ) / 4503599627370496) → k ≠ b → ((-4240589409132059 : ℝ) / 4503599627370496) ≤ ip x a k := fun a b k hab hkb =>
    far_pair_bound (ip x a b) (ip x a k) (ip x b k) ((-4458563631096791 : ℝ) / 4503599627370496) ((3602879701896397 : ℝ) / 4503599627370496) ((-4240589409132059 : ℝ) / 4503599627370496) (neg_one_le_ip x hx a b) hab
      (by norm_num) (hT b k (Ne.symm hkb)) (by norm_num) (by norm_num) (by norm_num) (gram_ip x hx a b k)
  have hqp : ip x q p ≤ ((-4458563631096791 : ℝ) / 4503599627370496) := (le_of_eq (real_inner_comm (x p) (x q))).trans hlow
  rcases hi with rfl | rfl
  · exact prr_far _ _ _ (neg_one_le_ip x hx i j) (neg_one_le_ip x hx i k) (neg_one_le_ip x hx j k)
      (ip_lt_one x hx hinj (Ne.symm hjp)) (ip_lt_one x hx hinj (Ne.symm hkp)) (ip_lt_one x hx hinj hjk)
      (gram_ip x hx i j k) (hT i j (Ne.symm hjp)) (hT i k (Ne.symm hkp)) (hT j k hjk)
      (hL i q j hlow hjq) (hL i q k hlow hkq)
        (by have h := hF; unfold Far at h; rwa [tau_left, tau_other hjp hjq, tau_other hkp hkq] at h)
  · exact prr_far _ _ _ (neg_one_le_ip x hx i j) (neg_one_le_ip x hx i k) (neg_one_le_ip x hx j k)
      (ip_lt_one x hx hinj (Ne.symm hjq)) (ip_lt_one x hx hinj (Ne.symm hkq)) (ip_lt_one x hx hinj hjk)
      (gram_ip x hx i j k) (hT i j (Ne.symm hjq)) (hT i k (Ne.symm hkq)) (hT j k hjk)
      (hL i p j hqp hjp) (hL i p k hqp hkp)
        (by have h := hF; unfold Far at h; rwa [tau_right, tau_other hjp hjq, tau_other hkp hkq] at h)

theorem cfg_rrr_far (x : Fin 14 → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1)
    (hinj : Function.Injective x) (p q : Fin 14) (hpq : p ≠ q)
    (hmin : ∀ i j, i ≠ j → inner ℝ (x p) (x q) ≤ inner ℝ (x i) (x j))
    (hlow : inner ℝ (x p) (x q) ≤ bLow) (hhigh : ∀ i j, i ≠ j → inner ℝ (x i) (x j) ≤ tHigh) (i j k : Fin 14) (hip : i ≠ p) (hiq : i ≠ q) (hjp : j ≠ p) (hjq : j ≠ q)
    (hkp : k ≠ p) (hkq : k ≠ q) (hd : Distinct3 i j k) (hF : Far hStar ((1 : ℝ) / 100) x p q i j k) :
    (0 : ℝ) ≤ cert.rrr.lam (ip x i j) (ip x i k) (ip x j k) := by
  have hT : ∀ i j, i ≠ j → ip x i j ≤ ((3602879701896397 : ℝ) / 4503599627370496) := fun i j hij => by
    have h := hhigh i j hij
    unfold tHigh at h
    exact h
  exact rrr_far _ _ _ (neg_one_le_ip x hx i j) (neg_one_le_ip x hx i k)
    (neg_one_le_ip x hx j k) (ip_lt_one x hx hinj hd.1) (ip_lt_one x hx hinj hd.2.1)
    (ip_lt_one x hx hinj hd.2.2) (gram_ip x hx i j k) (hT i j hd.1) (hT i k hd.2.1) (hT j k hd.2.2)
    (by have h := hF; unfold Far at h; rwa [tau_other hip hiq, tau_other hjp hjq, tau_other hkp hkq] at h)

/-- The slacks of all triples of a configuration of the cap are nonnegative. -/
theorem slack_all (x : Fin 14 → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1)
    (hinj : Function.Injective x) (p q : Fin 14) (hpq : p ≠ q)
    (hmin : ∀ i j, i ≠ j → inner ℝ (x p) (x q) ≤ inner ℝ (x i) (x j))
    (hlow : inner ℝ (x p) (x q) ≤ bLow) (hhigh : ∀ i j, i ≠ j → inner ℝ (x i) (x j) ≤ tHigh) (i j k : Fin 14) (hd : Distinct3 i j k) :
    -((cert.cM : ℝ) * (DCoreN00 : ℝ)) ≤ slackOf cert.P cert.blk (cert.cK : ℝ) cert.psi (tau p q) x i j k :=
  cert.slackOf_ge cert_ok (DCoreN00 : ℝ) x p q (fun k a b => cfg_ppr_ge x hx hinj p q hpq hmin hlow hhigh k a b)
    (fun i j k a b c d e f => cfg_prr_ge x hx hinj p q hpq hmin hlow hhigh i j k a b c d e f)
    (fun i j k a b c d e f g => cfg_rrr_ge x hx hinj p q hpq hmin hlow hhigh i j k a b c d e f g) i j k hd

/-- **Case III, the cap: a configuration of 14 points of the unit sphere whose smallest inner product, attained by
the pair `p`, `q`, is at most `bLow`, and all of whose inner products are at most `tHigh`, has Coulomb energy at
least the offset of the certificate.** The slacks of all triples are nonnegative: outside the excluded balls by
the global runs, in the ellipsoids of the nodes by the runs of the nodes (`lamPPR_ge`, `lamPRR_ge`, `lamRRR_ge`). -/
theorem energy_ge (x : Fin 14 → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1)
    (hinj : Function.Injective x) (p q : Fin 14) (hpq : p ≠ q)
    (hmin : ∀ i j, i ≠ j → inner ℝ (x p) (x q) ≤ inner ℝ (x i) (x j))
    (hlow : inner ℝ (x p) (x q) ≤ bLow) (hhigh : ∀ i j, i ≠ j → inner ℝ (x i) (x j) ≤ tHigh) :
    (34653181648313028629244995638191003932141064786879 : ℝ) / 500000000000000000000000000000000000000000000000
      ≤ ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / dist (x i) (x j) := by
  have h := cert.energy_ge_shift cert_ok _ _ _ _ 304812609295633439910279097184196042327068504614344715250805707 4398046511104000000000000000000000000000000000000000000000000 cert_one0 cert_one1
    (by decide) (by decide) (by decide +kernel) DCoreN00 34653181648313028629244995638191003932141064786879 500000000000000000000000000000000000000000000000 (by decide)
    (by decide +kernel) x hx p q hpq (fun i j k hd => slack_all x hx hinj p q hpq hmin hlow hhigh i j k hd)
  push_cast at h
  exact h

/-- info: 'N14Cert.CapId.energy_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms energy_ge

/-- **Statement (7.3) of the source for a configuration of the cap**: if the type of one triple of points has distance
at least `rhoFar = 0.01` from all nodes of its pattern (the types of the triples of the candidate with this
pattern, `N14.Far`), the energy is at least the offset of the certificate plus the threshold `θ_far` of the global
runs. -/
theorem energy_far (x : Fin 14 → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1)
    (hinj : Function.Injective x) (p q : Fin 14) (hpq : p ≠ q)
    (hmin : ∀ i j, i ≠ j → inner ℝ (x p) (x q) ≤ inner ℝ (x i) (x j))
    (hlow : inner ℝ (x p) (x q) ≤ bLow) (hhigh : ∀ i j, i ≠ j → inner ℝ (x i) (x j) ≤ tHigh)
    (i0 j0 k0 : Fin 14) (hd0 : Distinct3 i0 j0 k0) (hfar : Far hStar rhoFar x p q i0 j0 k0) :
    (1219250437176147796106993380865227304096814210405792709880175953 : ℝ) / 17592186044416000000000000000000000000000000000000000000000000
      ≤ ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / dist (x i) (x j) := by
  unfold rhoFar at hfar
  have hall := slack_all x hx hinj p q hpq hmin hlow hhigh
  have hS : ∀ i j k, Distinct3 i j k → Far hStar ((1 : ℝ) / 100) x p q i j k →
      -((cert.cM : ℝ) * (0 : ℝ)) ≤ slackOf cert.P cert.blk (cert.cK : ℝ) cert.psi (tau p q) x i j k := fun i j k hd hF =>
    cert.slackOf_ge_on cert_ok (0 : ℝ) x p q (fun i j k => Far hStar ((1 : ℝ) / 100) x p q i j k)
      (fun _ _ _ h => Far.swap12 h) (fun _ _ _ h => Far.swap23 h)
      (fun k a b hF => by rw [neg_zero]; exact cfg_ppr_far x hx hinj p q hpq hmin hlow hhigh k a b hF)
      (fun i j k a b c d e f hF => by rw [neg_zero]; exact cfg_prr_far x hx hinj p q hpq hmin hlow hhigh i j k a b c d e f hF)
      (fun i j k a b c d e f g hF => by rw [neg_zero]; exact cfg_rrr_far x hx hinj p q hpq hmin hlow hhigh i j k a b c d e f g hF)
      i j k hd hF
  have hcM : (0 : ℝ) ≤ (cert.cM : ℝ) := Nat.cast_nonneg _
  have hDp : (0 : ℝ) ≤ (DCoreN00 : ℝ) := Nat.cast_nonneg _
  have hgain := dsum_triple_ge (fun i j k => slackOf cert.P cert.blk (cert.cK : ℝ) cert.psi (tau p q) x i j k + (cert.cM : ℝ) * (DCoreN00 : ℝ))
    i0 j0 k0 hd0 ((cert.cM : ℝ) * (DCoreN00 : ℝ)) (mul_nonneg hcM hDp)
    (fun i j k hd => by have := hall i j k hd; linarith)
    (fun i j k hd c1 c2 c3 => by
      have := hS i j k hd (perm3_of (fun i j k => Far hStar ((1 : ℝ) / 100) x p q i j k)
        (fun _ _ _ h => Far.swap12 h) (fun _ _ _ h => Far.swap23 h) i0 j0 k0 hd0 hfar i j k c1 c2 c3)
      linarith)
  have h := cert.energy_ge_gain cert_ok _ _ _ _ 304812609295633439910279097184196042327068504614344715250805707 4398046511104000000000000000000000000000000000000000000000000 cert_one0 cert_one1
    (by decide) (by decide) (by decide +kernel) DCoreN00 DCoreN00 6 1219250437176147796106993380865227304096814210405792709880175953 17592186044416000000000000000000000000000000000000000000000000 (by decide)
    (by decide +kernel) x hx p q hpq (by push_cast; exact hgain)
  push_cast at h
  exact h

/-- info: 'N14Cert.CapId.energy_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms energy_far

/-- **The counting lemma of the source (Lemma 7.1) with statement (7.2), for a configuration of the cap**: if the inner
product of one pair of points has distance at least `tauTube = 1.95e-4` from the class values of its pair class (the
inner products of the pairs of the candidate with the same types, `N14.PairDisplaced`), the energy is at least the
offset of the certificate plus twelve times the threshold `θ_loc` of the local runs: each of the twelve triples
through the pair is not within `tauTube` of a node. -/
theorem energy_loc (x : Fin 14 → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1)
    (hinj : Function.Injective x) (p q : Fin 14) (hpq : p ≠ q)
    (hmin : ∀ i j, i ≠ j → inner ℝ (x p) (x q) ≤ inner ℝ (x i) (x j))
    (hlow : inner ℝ (x p) (x q) ≤ bLow) (hhigh : ∀ i j, i ≠ j → inner ℝ (x i) (x j) ≤ tHigh)
    (i0 j0 : Fin 14) (h0 : i0 ≠ j0) (hdisp : PairDisplaced hStar tauTube x p q i0 j0) :
    (9754003497409109185362002276364569375100315271841255161707423249 : ℝ) / 140737488355328000000000000000000000000000000000000000000000000
      ≤ ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / dist (x i) (x j) := by
  unfold tauTube at hdisp
  have hall := slack_all x hx hinj p q hpq hmin hlow hhigh
  have hS : ∀ i j k, Distinct3 i j k → Far hStar ((39 : ℝ) / 200000) x p q i j k →
      -((cert.cM : ℝ) * (DLocalN00 : ℝ)) ≤ slackOf cert.P cert.blk (cert.cK : ℝ) cert.psi (tau p q) x i j k := fun i j k hd hF =>
    cert.slackOf_ge_on cert_ok (DLocalN00 : ℝ) x p q (fun i j k => Far hStar ((39 : ℝ) / 200000) x p q i j k)
      (fun _ _ _ h => Far.swap12 h) (fun _ _ _ h => Far.swap23 h)
      (fun k a b hF => cfg_ppr_loc x hx hinj p q hpq hmin hlow hhigh k a b hF)
      (fun i j k a b c d e f hF => cfg_prr_loc x hx hinj p q hpq hmin hlow hhigh i j k a b c d e f hF)
      (fun i j k a b c d e f g hF => cfg_rrr_loc x hx hinj p q hpq hmin hlow hhigh i j k a b c d e f g hF)
      i j k hd hF
  have hcM : (0 : ℝ) ≤ (cert.cM : ℝ) := Nat.cast_nonneg _
  have hG : ((GLoc : ℕ) : ℝ) + (DLocalN00 : ℝ) = (DCoreN00 : ℝ) := by exact_mod_cast GLoc_add
  have hGp : (0 : ℝ) ≤ ((GLoc : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgain := dsum_pair_ge (fun i j k => slackOf cert.P cert.blk (cert.cK : ℝ) cert.psi (tau p q) x i j k + (cert.cM : ℝ) * (DCoreN00 : ℝ))
    i0 j0 h0 ((cert.cM : ℝ) * ((GLoc : ℕ) : ℝ)) (mul_nonneg hcM hGp)
    (fun i j k hd => by have := hall i j k hd; linarith)
    (fun i j k hd c1 c2 => by
      have := hS i j k hd (Far.of_pair (by norm_num) h0 hdisp i j k c1 c2)
      have e : (cert.cM : ℝ) * (DCoreN00 : ℝ)
          = (cert.cM : ℝ) * ((GLoc : ℕ) : ℝ) + (cert.cM : ℝ) * (DLocalN00 : ℝ) := by
        rw [← hG]
        ring
      linarith)
  have hcard : (Fintype.card (Fin 14) : ℝ) = 14 := by simp
  have e72 : (6 : ℝ) * (14 - 2) = 72 := by norm_num
  rw [hcard, e72] at hgain
  have h := cert.energy_ge_gain cert_ok _ _ _ _ 304812609295633439910279097184196042327068504614344715250805707 4398046511104000000000000000000000000000000000000000000000000 cert_one0 cert_one1
    (by decide) (by decide) (by decide +kernel) DCoreN00 GLoc 72 9754003497409109185362002276364569375100315271841255161707423249 140737488355328000000000000000000000000000000000000000000000000 (by decide)
    (by decide +kernel) x hx p q hpq (by push_cast; exact hgain)
  push_cast at h
  exact h

/-- info: 'N14Cert.CapId.energy_loc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms energy_loc

end N14Cert.CapId

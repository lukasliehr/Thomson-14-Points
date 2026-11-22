module

public import N14.Box.Master
public import N14Cert.Case2Ppr.Tables0
public import N14Cert.Case2Ppr.Tables1
public import N14Cert.Case2Ppr.Cells0
public import N14Cert.Case2Ppr.Cells1
public import N14Cert.Case2Ppr.Cells2
public import N14Cert.Case2Ppr.Cells3
public import N14Cert.Case2Ppr.Cells4
public import N14Cert.Case2Ppr.Cells5
public import N14Cert.Case2Ppr.Cells6
public import N14Cert.Case2Ppr.Cells7
public import N14Cert.Case2Ppr.Cells8
public import N14Cert.Case2Ppr.Cells9
public import N14Cert.Case2Ppr.Cells10
public import N14Cert.Case2Ppr.Cells11
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.Case2Ppr

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The boxes of the groups 0 to 39. -/
noncomputable def boxes_p0 : List Bx :=
  [{ e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 1, c3 := 0 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 1, c3 := 1 },
    { e1 := 2, c1 := 0, e2 := 2, c2 := 0, e3 := 1, c3 := 2 },
    { e1 := 2, c1 := 0, e2 := 2, c2 := 1, e3 := 2, c3 := 4 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 2, e3 := 2, c3 := 5 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 3, e3 := 2, c3 := 5 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 0, e3 := 2, c3 := 6 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 2, e3 := 3, c3 := 12 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 3, e3 := 4, c3 := 24 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 6, e3 := 4, c3 := 25 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 7, e3 := 5, c3 := 50 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 7, e3 := 5, c3 := 51 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 1, e3 := 3, c3 := 13 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 4, e3 := 4, c3 := 24 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 8, e3 := 4, c3 := 25 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 9, e3 := 4, c3 := 25 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 5, e3 := 3, c3 := 12 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 2, e3 := 3, c3 := 13 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 3, e3 := 2, c3 := 6 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 0, e3 := 4, c3 := 28 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 0, e3 := 4, c3 := 29 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 1, e3 := 5, c3 := 58 },
    { e1 := 6, c1 := 0, e2 := 5, c2 := 1, e3 := 5, c3 := 59 },
    { e1 := 6, c1 := 1, e2 := 6, c2 := 2, e3 := 5, c3 := 59 },
    { e1 := 7, c1 := 2, e2 := 6, c2 := 3, e3 := 6, c3 := 118 },
    { e1 := 6, c1 := 1, e2 := 6, c2 := 3, e3 := 6, c3 := 119 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 2, e3 := 5, c3 := 56 },
    { e1 := 6, c1 := 0, e2 := 5, c2 := 2, e3 := 5, c3 := 57 },
    { e1 := 6, c1 := 1, e2 := 6, c2 := 4, e3 := 5, c3 := 57 },
    { e1 := 6, c1 := 1, e2 := 6, c2 := 5, e3 := 6, c3 := 114 },
    { e1 := 6, c1 := 1, e2 := 6, c2 := 5, e3 := 6, c3 := 115 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 3, e3 := 4, c3 := 28 },
    { e1 := 6, c1 := 0, e2 := 5, c2 := 2, e3 := 5, c3 := 58 },
    { e1 := 6, c1 := 1, e2 := 6, c2 := 4, e3 := 6, c3 := 116 },
    { e1 := 7, c1 := 2, e2 := 6, c2 := 4, e3 := 6, c3 := 117 },
    { e1 := 7, c1 := 2, e2 := 6, c2 := 5, e3 := 6, c3 := 116 },
    { e1 := 6, c1 := 1, e2 := 6, c2 := 5, e3 := 6, c3 := 117 },
    { e1 := 6, c1 := 0, e2 := 5, c2 := 2, e3 := 5, c3 := 59 },
    { e1 := 7, c1 := 2, e2 := 6, c2 := 4, e3 := 6, c3 := 118 },
    { e1 := 6, c1 := 1, e2 := 6, c2 := 4, e3 := 6, c3 := 119 }]

theorem done_p0 : AllDone run boxes_p0 :=
  allDone_cons g0_ok <|
  allDone_cons g1_ok <|
  allDone_cons g2_ok <|
  allDone_cons g3_ok <|
  allDone_cons g4_ok <|
  allDone_cons g5_ok <|
  allDone_cons g6_ok <|
  allDone_cons g7_ok <|
  allDone_cons g8_ok <|
  allDone_cons g9_ok <|
  allDone_cons g10_ok <|
  allDone_cons g11_ok <|
  allDone_cons g12_ok <|
  allDone_cons g13_ok <|
  allDone_cons g14_ok <|
  allDone_cons g15_ok <|
  allDone_cons g16_ok <|
  allDone_cons g17_ok <|
  allDone_cons g18_ok <|
  allDone_cons g19_ok <|
  allDone_cons g20_ok <|
  allDone_cons g21_ok <|
  allDone_cons g22_ok <|
  allDone_cons g23_ok <|
  allDone_cons g24_ok <|
  allDone_cons g25_ok <|
  allDone_cons g26_ok <|
  allDone_cons g27_ok <|
  allDone_cons g28_ok <|
  allDone_cons g29_ok <|
  allDone_cons g30_ok <|
  allDone_cons g31_ok <|
  allDone_cons g32_ok <|
  allDone_cons g33_ok <|
  allDone_cons g34_ok <|
  allDone_cons g35_ok <|
  allDone_cons g36_ok <|
  allDone_cons g37_ok <|
  allDone_cons g38_ok <|
  allDone_cons g39_ok <|
  allDone_nil run

/-- The boxes of the groups 40 to 79. -/
noncomputable def boxes_p1 : List Bx :=
  [{ e1 := 6, c1 := 1, e2 := 6, c2 := 5, e3 := 5, c3 := 59 },
    { e1 := 5, c1 := 0, e2 := 5, c2 := 3, e3 := 4, c3 := 29 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 1, e3 := 3, c3 := 14 },
    { e1 := 2, c1 := 0, e2 := 2, c2 := 1, e3 := 3, c3 := 14 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 4, c3 := 30 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 4, c3 := 31 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 1, e3 := 1, c3 := 0 },
    { e1 := 2, c1 := 0, e2 := 2, c2 := 2, e3 := 1, c3 := 1 },
    { e1 := 2, c1 := 0, e2 := 2, c2 := 3, e3 := 2, c3 := 2 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 6, e3 := 3, c3 := 6 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 12, e3 := 3, c3 := 7 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 13, e3 := 3, c3 := 7 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 7, e3 := 3, c3 := 6 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 14, e3 := 3, c3 := 7 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 15, e3 := 3, c3 := 7 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 4, e3 := 2, c3 := 4 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 5, e3 := 3, c3 := 8 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 5, e3 := 3, c3 := 9 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 4, e3 := 3, c3 := 10 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 4, e3 := 3, c3 := 11 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 5, e3 := 3, c3 := 10 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 10, e3 := 3, c3 := 11 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 11, e3 := 3, c3 := 11 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 12, e3 := 4, c3 := 16 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 12, e3 := 4, c3 := 17 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 13, e3 := 3, c3 := 8 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 6, e3 := 3, c3 := 9 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 7, e3 := 2, c3 := 4 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 6, e3 := 2, c3 := 5 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 7, e3 := 2, c3 := 5 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 8, e3 := 3, c3 := 12 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 9, e3 := 3, c3 := 12 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 4, e3 := 3, c3 := 13 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 10, e3 := 4, c3 := 24 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 10, e3 := 4, c3 := 25 },
    { e1 := 4, c1 := 0, e2 := 4, c2 := 11, e3 := 3, c3 := 12 },
    { e1 := 3, c1 := 0, e2 := 3, c2 := 5, e3 := 3, c3 := 13 },
    { e1 := 2, c1 := 0, e2 := 2, c2 := 3, e3 := 2, c3 := 6 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 1, e3 := 2, c3 := 7 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 1, c3 := 1 }]

theorem done_p1 : AllDone run boxes_p1 :=
  allDone_cons g40_ok <|
  allDone_cons g41_ok <|
  allDone_cons g42_ok <|
  allDone_cons g43_ok <|
  allDone_cons g44_ok <|
  allDone_cons g45_ok <|
  allDone_cons g46_ok <|
  allDone_cons g47_ok <|
  allDone_cons g48_ok <|
  allDone_cons g49_ok <|
  allDone_cons g50_ok <|
  allDone_cons g51_ok <|
  allDone_cons g52_ok <|
  allDone_cons g53_ok <|
  allDone_cons g54_ok <|
  allDone_cons g55_ok <|
  allDone_cons g56_ok <|
  allDone_cons g57_ok <|
  allDone_cons g58_ok <|
  allDone_cons g59_ok <|
  allDone_cons g60_ok <|
  allDone_cons g61_ok <|
  allDone_cons g62_ok <|
  allDone_cons g63_ok <|
  allDone_cons g64_ok <|
  allDone_cons g65_ok <|
  allDone_cons g66_ok <|
  allDone_cons g67_ok <|
  allDone_cons g68_ok <|
  allDone_cons g69_ok <|
  allDone_cons g70_ok <|
  allDone_cons g71_ok <|
  allDone_cons g72_ok <|
  allDone_cons g73_ok <|
  allDone_cons g74_ok <|
  allDone_cons g75_ok <|
  allDone_cons g76_ok <|
  allDone_cons g77_ok <|
  allDone_cons g78_ok <|
  allDone_cons g79_ok <|
  allDone_nil run

/-- The boxes of the groups 80 to 84. -/
noncomputable def boxes_p2 : List Bx :=
  [{ e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 3, e3 := 1, c3 := 2 },
    { e1 := 1, c1 := 0, e2 := 2, c2 := 6, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 0, e2 := 2, c2 := 7, e3 := 1, c3 := 3 }]

theorem done_p2 : AllDone run boxes_p2 :=
  allDone_cons g80_ok <|
  allDone_cons g81_ok <|
  allDone_cons g82_ok <|
  allDone_cons g83_ok <|
  allDone_cons g84_ok <|
  allDone_nil run

noncomputable def boxes_q0_0 : List Bx :=
  boxes_p0 ++ (boxes_p1 ++ (boxes_p2))

theorem done_q0_0 : AllDone run boxes_q0_0 :=
  allDone_append done_p0 <| allDone_append done_p1 <| done_p2

/-- **The master tree**: the boxes of the groups, and boxes on which a cut fails, are the leaves of
trees of bisections of the boxes of the grid of the level 1. -/
theorem master_ok : masterOk run 1 (hex% "fffffffffffffffffffffffff7fffffffe4bfd244bfd3fff924bfd3be4fed24ffd3bf4e4ed3fbfffff273f2f39c93fedce4bfcb73b4e444bffff4e493ffed3b4b44bfd3b4f") boxes_q0_0 = true := by
  decide +kernel

/-- **The slack of the run is nonnegative on its domain**: at the points of `[-1, 1)³` at which the Gram
polynomial, the functions of the cuts and the polynomial constraints of the run are nonnegative. The slack
is the polynomial of the numeral `run.PpM` plus the functions of one variable of the tables, in the units
of the run. -/
theorem slack_nonneg (x1 x2 x3 : ℝ) (h1 : -1 ≤ x1) (h2 : -1 ≤ x2) (h3 : -1 ≤ x3) (hD : Dom run x1 x2 x3) :
    0 ≤ slackFn run tab0 tab1 tab1 x1 x2 x3 :=
  run_sound_master run run_ok tab0 tab1 tab1 ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    table0_ok table1_ok table1_ok 1 _ boxes_q0_0 master_ok done_q0_0
    x1 x2 x3 h1 h2 h3 hD

/-- info: 'N14Cert.Case2Ppr.slack_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms slack_nonneg

end N14Cert.Case2Ppr

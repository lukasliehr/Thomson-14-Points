module

public import N14.Box.Master
public import N14Cert.LocalN14.Tables0
public import N14Cert.LocalN14.Tables1
public import N14Cert.LocalN14.Cells0
public import N14Cert.LocalN14.Cells1
public import N14Cert.LocalN14.Cells2
public import N14Cert.LocalN14.Cells3
public import N14Cert.LocalN14.Cells4
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.LocalN14

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The boxes of the groups 0 to 32. -/
noncomputable def boxes_p0 : List Bx :=
  [{ e1 := 5, c1 := 3, e2 := 5, c2 := 3, e3 := 5, c3 := 50 },
    { e1 := 7, c1 := 12, e2 := 6, c2 := 6, e3 := 6, c3 := 102 },
    { e1 := 7, c1 := 13, e2 := 7, c2 := 12, e3 := 6, c3 := 102 },
    { e1 := 7, c1 := 13, e2 := 7, c2 := 13, e3 := 7, c3 := 204 },
    { e1 := 8, c1 := 26, e2 := 8, c2 := 26, e3 := 7, c3 := 205 },
    { e1 := 9, c1 := 52, e2 := 8, c2 := 27, e3 := 8, c3 := 410 },
    { e1 := 9, c1 := 53, e2 := 9, c2 := 54, e3 := 9, c3 := 820 },
    { e1 := 9, c1 := 53, e2 := 9, c2 := 54, e3 := 9, c3 := 821 },
    { e1 := 9, c1 := 53, e2 := 9, c2 := 55, e3 := 9, c3 := 820 },
    { e1 := 9, c1 := 53, e2 := 9, c2 := 55, e3 := 9, c3 := 821 },
    { e1 := 8, c1 := 26, e2 := 8, c2 := 27, e3 := 8, c3 := 411 },
    { e1 := 8, c1 := 27, e2 := 8, c2 := 26, e3 := 7, c3 := 205 },
    { e1 := 9, c1 := 54, e2 := 9, c2 := 54, e3 := 9, c3 := 820 },
    { e1 := 9, c1 := 54, e2 := 9, c2 := 54, e3 := 9, c3 := 821 },
    { e1 := 9, c1 := 54, e2 := 9, c2 := 55, e3 := 8, c3 := 410 },
    { e1 := 9, c1 := 55, e2 := 8, c2 := 27, e3 := 8, c3 := 410 },
    { e1 := 8, c1 := 27, e2 := 8, c2 := 27, e3 := 8, c3 := 411 },
    { e1 := 6, c1 := 6, e2 := 6, c2 := 6, e3 := 6, c3 := 103 },
    { e1 := 7, c1 := 12, e2 := 7, c2 := 14, e3 := 7, c3 := 204 },
    { e1 := 8, c1 := 24, e2 := 7, c2 := 14, e3 := 7, c3 := 205 },
    { e1 := 9, c1 := 50, e2 := 8, c2 := 28, e3 := 8, c3 := 410 },
    { e1 := 9, c1 := 51, e2 := 8, c2 := 28, e3 := 8, c3 := 410 },
    { e1 := 8, c1 := 25, e2 := 8, c2 := 28, e3 := 8, c3 := 411 },
    { e1 := 8, c1 := 25, e2 := 8, c2 := 29, e3 := 7, c3 := 205 },
    { e1 := 7, c1 := 13, e2 := 7, c2 := 14, e3 := 7, c3 := 204 },
    { e1 := 9, c1 := 52, e2 := 9, c2 := 56, e3 := 8, c3 := 410 },
    { e1 := 9, c1 := 52, e2 := 9, c2 := 57, e3 := 8, c3 := 410 },
    { e1 := 9, c1 := 53, e2 := 8, c2 := 28, e3 := 8, c3 := 410 },
    { e1 := 8, c1 := 26, e2 := 8, c2 := 28, e3 := 8, c3 := 411 },
    { e1 := 8, c1 := 26, e2 := 8, c2 := 29, e3 := 7, c3 := 205 },
    { e1 := 8, c1 := 27, e2 := 7, c2 := 14, e3 := 7, c3 := 205 },
    { e1 := 6, c1 := 6, e2 := 6, c2 := 7, e3 := 6, c3 := 103 },
    { e1 := 6, c1 := 7, e2 := 5, c2 := 3, e3 := 5, c3 := 51 }]

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
  allDone_nil run

/-- **The master tree**: the boxes of the groups, and boxes on which a cut fails, are the leaves of
trees of bisections of the boxes of the grid of the level 1. -/
theorem master_ok : masterOk run 1 (hex% "fffffffffffffffffffffffffffffffffffffd24e7ff27392fff92dfef9cb4edc93b73b7244bf") boxes_p0 = true := by
  decide +kernel

/-- **The slack of the run is nonnegative on its domain**: at the points of `[-1, 1)³` at which the Gram
polynomial, the functions of the cuts and the polynomial constraints of the run are nonnegative. The slack
is the polynomial of the numeral `run.PpM` plus the functions of one variable of the tables, in the units
of the run. -/
theorem slack_nonneg (x1 x2 x3 : ℝ) (h1 : -1 ≤ x1) (h2 : -1 ≤ x2) (h3 : -1 ≤ x3) (hD : Dom run x1 x2 x3) :
    0 ≤ slackFn run tab0 tab0 tab1 x1 x2 x3 :=
  run_sound_master run run_ok tab0 tab0 tab1 ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    table0_ok table0_ok table1_ok 1 _ boxes_p0 master_ok done_p0
    x1 x2 x3 h1 h2 h3 hD

/-- info: 'N14Cert.LocalN14.slack_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms slack_nonneg

end N14Cert.LocalN14

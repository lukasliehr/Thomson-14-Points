module

public import N14.Box.Master
public import N14Cert.Case0Close.Tables0
public import N14Cert.Case0Close.Tables1
public import N14Cert.Case0Close.Cells0
public import N14Cert.Case0Close.Cells1
public import N14Cert.Case0Close.Cells2
public import N14Cert.Case0Close.Cells3
public import N14Cert.Case0Close.Cells4
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.Case0Close

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The boxes of the groups 0 to 31. -/
noncomputable def boxes_p0 : List Bx :=
  [{ e1 := 2, c1 := 0, e2 := 2, c2 := 0, e3 := 3, c3 := 14 },
    { e1 := 2, c1 := 0, e2 := 2, c2 := 1, e3 := 3, c3 := 14 },
    { e1 := 2, c1 := 1, e2 := 1, c2 := 0, e3 := 3, c3 := 14 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 3, c3 := 15 },
    { e1 := 2, c1 := 0, e2 := 1, c2 := 1, e3 := 3, c3 := 14 },
    { e1 := 2, c1 := 1, e2 := 1, c2 := 1, e3 := 3, c3 := 14 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 1, e3 := 3, c3 := 15 },
    { e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 0, e2 := 2, c2 := 6, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 0, e2 := 2, c2 := 7, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 1, e2 := 1, c2 := 2, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 1, e2 := 2, c2 := 6, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 1, e2 := 2, c2 := 7, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 2, e2 := 2, c2 := 6, e3 := 1, c3 := 3 },
    { e1 := 1, c1 := 2, e2 := 3, c2 := 14, e3 := 2, c3 := 7 },
    { e1 := 1, c1 := 2, e2 := 3, c2 := 15, e3 := 2, c3 := 7 },
    { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 3 },
    { e1 := 2, c1 := 6, e2 := 2, c2 := 6, e3 := 1, c3 := 3 },
    { e1 := 2, c1 := 6, e2 := 2, c2 := 7, e3 := 1, c3 := 3 },
    { e1 := 2, c1 := 7, e2 := 2, c2 := 6, e3 := 1, c3 := 3 },
    { e1 := 3, c1 := 14, e2 := 2, c2 := 7, e3 := 2, c3 := 7 },
    { e1 := 3, c1 := 15, e2 := 3, c2 := 14, e3 := 2, c3 := 7 },
    { e1 := 3, c1 := 15, e2 := 3, c2 := 15, e3 := 3, c3 := 14 },
    { e1 := 4, c1 := 30, e2 := 3, c2 := 15, e3 := 3, c3 := 15 },
    { e1 := 4, c1 := 31, e2 := 4, c2 := 30, e3 := 3, c3 := 15 },
    { e1 := 4, c1 := 31, e2 := 4, c2 := 31, e3 := 4, c3 := 30 },
    { e1 := 5, c1 := 62, e2 := 4, c2 := 31, e3 := 4, c3 := 31 },
    { e1 := 5, c1 := 63, e2 := 4, c2 := 31, e3 := 4, c3 := 31 }]

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
  allDone_nil run

/-- **The master tree**: the boxes of the groups, and boxes on which a cut fails, are the leaves of
trees of bisections of the boxes of the grid of the level 1. -/
theorem master_ok : masterOk run 1 (hex% "f3b73b73b7d3ffffffff7b7ffffffff7ffffffff7ffffcbbfff4bbf") boxes_p0 = true := by
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

/-- info: 'N14Cert.Case0Close.slack_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms slack_nonneg

end N14Cert.Case0Close

module

public import N14.Box.Master
public import N14Cert.LocalN17.Tables0
public import N14Cert.LocalN17.Tables1
public import N14Cert.LocalN17.Tables2
public import N14Cert.LocalN17.Cells0
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.LocalN17

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The boxes of the groups 0 to 3. -/
noncomputable def boxes_p0 : List Bx :=
  [{ e1 := 5, c1 := 3, e2 := 5, c2 := 25, e3 := 5, c3 := 50 },
    { e1 := 6, c1 := 6, e2 := 6, c2 := 50, e3 := 5, c3 := 51 },
    { e1 := 6, c1 := 6, e2 := 6, c2 := 51, e3 := 5, c3 := 51 },
    { e1 := 6, c1 := 7, e2 := 5, c2 := 25, e3 := 5, c3 := 51 }]

theorem done_p0 : AllDone run boxes_p0 :=
  allDone_cons g0_ok <|
  allDone_cons g1_ok <|
  allDone_cons g2_ok <|
  allDone_cons g3_ok <|
  allDone_nil run

/-- **The master tree**: the boxes of the groups, and boxes on which a cut fails, are the leaves of
trees of bisections of the boxes of the grid of the level 1. -/
theorem master_ok : masterOk run 1 (hex% "ffffffffffffffffffffffffffffffffd3b739c934bfff") boxes_p0 = true := by
  decide +kernel

/-- **The slack of the run is nonnegative on its domain**: at the points of `[-1, 1)³` at which the Gram
polynomial, the functions of the cuts and the polynomial constraints of the run are nonnegative. The slack
is the polynomial of the numeral `run.PpM` plus the functions of one variable of the tables, in the units
of the run. -/
theorem slack_nonneg (x1 x2 x3 : ℝ) (h1 : -1 ≤ x1) (h2 : -1 ≤ x2) (h3 : -1 ≤ x3) (hD : Dom run x1 x2 x3) :
    0 ≤ slackFn run tab0 tab1 tab2 x1 x2 x3 :=
  run_sound_master run run_ok tab0 tab1 tab2 ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    table0_ok table1_ok table2_ok 1 _ boxes_p0 master_ok done_p0
    x1 x2 x3 h1 h2 h3 hD

/-- info: 'N14Cert.LocalN17.slack_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms slack_nonneg

end N14Cert.LocalN17

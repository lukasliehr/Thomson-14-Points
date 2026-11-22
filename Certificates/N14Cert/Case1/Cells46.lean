module

public import N14Cert.Case1.Run
public import N14.Box.MasterKernel
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.Case1

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The cells of the group 370. -/
noncomputable def cells370 : List Cell :=
  [{ i := 0, j := 55, k := 55, use := 0, tree := 5 },
    { i := 0, j := 55, k := 118, use := 0, tree := 5 },
    { i := 0, j := 55, k := 245, use := 0, tree := 5 },
    { i := 0, j := 55, k := 246, use := 0, tree := 5 }]

/-- The group 370: the cover of a box by its cells. -/
theorem g370_ok : boxOk run { e1 := 1, c1 := 0, e2 := 4, c2 := 30, e3 := 3, c3 := 15 } (16110) cells370 = true := by
  decide +kernel

/-- The cells of the group 371. -/
noncomputable def cells371 : List Cell :=
  [{ i := 0, j := 118, k := 55, use := 0, tree := 5 },
    { i := 0, j := 118, k := 118, use := 0, tree := 5 },
    { i := 0, j := 118, k := 245, use := 0, tree := 5 },
    { i := 0, j := 118, k := 246, use := 0, tree := 5 },
    { i := 0, j := 245, k := 118, use := 0, tree := 5 },
    { i := 0, j := 245, k := 245, use := 0, tree := 5 },
    { i := 0, j := 245, k := 246, use := 0, tree := 5 },
    { i := 0, j := 246, k := 245, use := 0, tree := 5 },
    { i := 0, j := 246, k := 246, use := 0, tree := 5 }]

/-- The group 371: the cover of a box by its cells. -/
theorem g371_ok : boxOk run { e1 := 1, c1 := 0, e2 := 4, c2 := 31, e3 := 3, c3 := 15 } (4327706966518) cells371 = true := by
  decide +kernel

/-- The cells of the group 372. -/
noncomputable def cells372 : List Cell :=
  [{ i := 1, j := 0, k := 0, use := 0, tree := hex% "34b4558000cf0c92218327800000000000000000008a08611d0c9e4" }]

/-- The group 372: the cover of a box by its cells. -/
theorem g372_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 0 } (3) cells372 = true := by
  decide +kernel

/-- The cells of the group 373. -/
noncomputable def cells373 : List Cell :=
  [{ i := 1, j := 0, k := 1, use := 0, tree := hex% "542a15000000000000000000000000008d78cd0000000000000000000000000003dd6681500000000000000000000000000734567000000000000000000000000000f89b98150a800000000000000000000000002b6cfd0000000000000000000000000000000f400000000000000000000000000127c36000000000000000000000000000001c48814102156c0000000000000000000000000030c32c000000000000000000000000000000022050541" }]

/-- The group 373: the cover of a box by its cells. -/
theorem g373_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 1 } (3) cells373 = true := by
  decide +kernel

/-- The cells of the group 374. -/
noncomputable def cells374 : List Cell :=
  [{ i := 1, j := 0, k := 2, use := 0, tree := hex% "5400000000000000000000000002154428000000000000000000000000000000021" }]

/-- The group 374: the cover of a box by its cells. -/
theorem g374_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 2 } (3) cells374 = true := by
  decide +kernel

/-- The cells of the group 375. -/
noncomputable def cells375 : List Cell :=
  [{ i := 1, j := 0, k := 9, use := 0, tree := hex% "542a150000000000000000000000000009e8ed000000000000000000000000000000008d0200000000000000000000000000b46f860000000000000000000000000000000110541" }]

/-- The group 375: the cover of a box by its cells. -/
theorem g375_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 2, c3 := 6 } (3) cells375 = true := by
  decide +kernel

/-- The cells of the group 376. -/
noncomputable def cells376 : List Cell :=
  [{ i := 1, j := 0, k := 24, use := 0, tree := 5604673 }]

/-- The group 376: the cover of a box by its cells. -/
theorem g376_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 3, c3 := 14 } (3) cells376 = true := by
  decide +kernel

/-- The cells of the group 377. -/
noncomputable def cells377 : List Cell :=
  [{ i := 1, j := 0, k := 55, use := 0, tree := 5604673 },
    { i := 1, j := 0, k := 118, use := 0, tree := 5604673 },
    { i := 1, j := 0, k := 245, use := 0, tree := 1409345 },
    { i := 1, j := 0, k := 246, use := 0, tree := hex% "140000000000000000000000004ecf548000000000000000000000001409bcce1a0141" }]

/-- The group 377: the cover of a box by its cells. -/
theorem g377_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 3, c3 := 15 } (16110) cells377 = true := by
  decide +kernel

end N14Cert.Case1

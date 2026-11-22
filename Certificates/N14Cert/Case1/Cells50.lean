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

/-- The cells of the group 403. -/
noncomputable def cells403 : List Cell :=
  [{ i := 2, j := 1, k := 118, use := 0, tree := 5604673 },
    { i := 2, j := 1, k := 245, use := 0, tree := hex% "14000000000000000000000000f3eb5f84000000000000000000000026a6c46ac61" },
    { i := 2, j := 1, k := 246, use := 0, tree := hex% "14000000000000000000000000dc735ab8000000000000000000000042932593361" }]

/-- The group 403: the cover of a box by its cells. -/
theorem g403_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 4, c3 := 31 } (1006) cells403 = true := by
  decide +kernel

/-- The cells of the group 404. -/
noncomputable def cells404 : List Cell :=
  [{ i := 2, j := 2, k := 1, use := 0, tree := hex% "1438be18000000000000000000000000000000000000000000000004" }]

/-- The group 404: the cover of a box by its cells. -/
theorem g404_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 1 } (3) cells404 = true := by
  decide +kernel

/-- The cells of the group 405. -/
noncomputable def cells405 : List Cell :=
  [{ i := 2, j := 2, k := 2, use := 0, tree := 3 }]

/-- The group 405: the cover of a box by its cells. -/
theorem g405_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 2 } (3) cells405 = true := by
  decide +kernel

/-- The cells of the group 406. -/
noncomputable def cells406 : List Cell :=
  [{ i := 7, j := 2, k := 9, use := 0, tree := hex% "36da64269a6d36da08b4d1" },
    { i := 8, j := 2, k := 9, use := 0, tree := hex% "387160000000000000000000000000000000011a6db48800000000000000000000000000913e38000000000000000000000000000000046db0d10db6086cb0910d16c0000000000000000000000000025e21800000000000000000000000000000002360a68a" }]

/-- The group 406: the cover of a box by its cells. -/
theorem g406_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 2, c3 := 6 } (60) cells406 = true := by
  decide +kernel

/-- The cells of the group 407. -/
noncomputable def cells407 : List Cell :=
  [{ i := 2, j := 2, k := 24, use := 0, tree := 3 }]

/-- The group 407: the cover of a box by its cells. -/
theorem g407_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 3, c3 := 14 } (3) cells407 = true := by
  decide +kernel

/-- The cells of the group 408. -/
noncomputable def cells408 : List Cell :=
  [{ i := 2, j := 2, k := 55, use := 0, tree := hex% "18000000000000000000000001e1cce74c" }]

/-- The group 408: the cover of a box by its cells. -/
theorem g408_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 4, c3 := 30 } (3) cells408 = true := by
  decide +kernel

/-- The cells of the group 409. -/
noncomputable def cells409 : List Cell :=
  [{ i := 2, j := 2, k := 118, use := 0, tree := hex% "300000000000000000000000091ffffe1c" },
    { i := 2, j := 2, k := 245, use := 0, tree := hex% "580000000000000000000000167ad1b0bc" },
    { i := 2, j := 2, k := 246, use := 0, tree := hex% "8000000000000000000000003d589b4c6c" }]

/-- The group 409: the cover of a box by its cells. -/
theorem g409_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 4, c3 := 31 } (1006) cells409 = true := by
  decide +kernel

/-- The cells of the group 410. -/
noncomputable def cells410 : List Cell :=
  [{ i := 2, j := 9, k := 2, use := 0, tree := hex% "e187ae0000000000000000000000000000000000000000000000004" }]

/-- The group 410: the cover of a box by its cells. -/
theorem g410_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 3, e3 := 1, c3 := 2 } (61) cells410 = true := by
  decide +kernel

/-- The cells of the group 411. -/
noncomputable def cells411 : List Cell :=
  [{ i := 7, j := 9, k := 9, use := 0, tree := hex% "144fc80000000000000000000000000000000000000000000000046da4d16d82db052000000000039dbdc0000000000000000000000000000000000000000000000008d1" },
    { i := 8, j := 9, k := 9, use := 0, tree := hex% "da65b0d32000000000049b9e2c000000000000000000000000000000000000000000000002300000000000ce62f000000000000000000000000000000000000000000000000803a426da4db6886c20db011699" }]

/-- The group 411: the cover of a box by its cells. -/
theorem g411_ok : boxOk run { e1 := 1, c1 := 2, e2 := 2, c2 := 6, e3 := 2, c3 := 6 } (60) cells411 = true := by
  decide +kernel

end N14Cert.Case1

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

/-- The cells of the group 393. -/
noncomputable def cells393 : List Cell :=
  [{ i := 1, j := 24, k := 24, use := 0, tree := 5 },
    { i := 1, j := 24, k := 55, use := 0, tree := 5 },
    { i := 1, j := 24, k := 118, use := 0, tree := 5 },
    { i := 1, j := 24, k := 245, use := 0, tree := 5 },
    { i := 1, j := 24, k := 246, use := 0, tree := 5 }]

/-- The group 393: the cover of a box by its cells. -/
theorem g393_ok : boxOk run { e1 := 1, c1 := 1, e2 := 3, c2 := 14, e3 := 2, c3 := 7 } (257774) cells393 = true := by
  decide +kernel

/-- The cells of the group 394. -/
noncomputable def cells394 : List Cell :=
  [{ i := 1, j := 55, k := 24, use := 0, tree := 5 }]

/-- The group 394: the cover of a box by its cells. -/
theorem g394_ok : boxOk run { e1 := 1, c1 := 1, e2 := 3, c2 := 15, e3 := 3, c3 := 14 } (61) cells394 = true := by
  decide +kernel

/-- The cells of the group 395. -/
noncomputable def cells395 : List Cell :=
  [{ i := 1, j := 55, k := 55, use := 0, tree := 5 },
    { i := 1, j := 55, k := 118, use := 0, tree := 5 },
    { i := 1, j := 55, k := 245, use := 0, tree := 5 },
    { i := 1, j := 55, k := 246, use := 0, tree := 5 }]

/-- The group 395: the cover of a box by its cells. -/
theorem g395_ok : boxOk run { e1 := 1, c1 := 1, e2 := 4, c2 := 30, e3 := 3, c3 := 15 } (16110) cells395 = true := by
  decide +kernel

/-- The cells of the group 396. -/
noncomputable def cells396 : List Cell :=
  [{ i := 1, j := 118, k := 55, use := 0, tree := 5 },
    { i := 1, j := 118, k := 118, use := 0, tree := 5 },
    { i := 1, j := 118, k := 245, use := 0, tree := 5 },
    { i := 1, j := 118, k := 246, use := 0, tree := 5 },
    { i := 1, j := 245, k := 118, use := 0, tree := 5 },
    { i := 1, j := 245, k := 245, use := 0, tree := 5 },
    { i := 1, j := 245, k := 246, use := 0, tree := 5 },
    { i := 1, j := 246, k := 245, use := 0, tree := 5 },
    { i := 1, j := 246, k := 246, use := 0, tree := 5 }]

/-- The group 396: the cover of a box by its cells. -/
theorem g396_ok : boxOk run { e1 := 1, c1 := 1, e2 := 4, c2 := 31, e3 := 3, c3 := 15 } (4327706966518) cells396 = true := by
  decide +kernel

/-- The cells of the group 397. -/
noncomputable def cells397 : List Cell :=
  [{ i := 2, j := 1, k := 0, use := 0, tree := hex% "334421a5000000001a3efd73800000000000000000000000193815134" }]

/-- The group 397: the cover of a box by its cells. -/
theorem g397_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 0 } (3) cells397 = true := by
  decide +kernel

/-- The cells of the group 398. -/
noncomputable def cells398 : List Cell :=
  [{ i := 2, j := 1, k := 1, use := 0, tree := hex% "58f3600000000000b1e6b800000000000000000000000000000004" }]

/-- The group 398: the cover of a box by its cells. -/
theorem g398_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 1 } (3) cells398 = true := by
  decide +kernel

/-- The cells of the group 399. -/
noncomputable def cells399 : List Cell :=
  [{ i := 2, j := 1, k := 2, use := 0, tree := hex% "1438be1800000000000000000000000000000004" }]

/-- The group 399: the cover of a box by its cells. -/
theorem g399_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 2 } (3) cells399 = true := by
  decide +kernel

/-- The cells of the group 400. -/
noncomputable def cells400 : List Cell :=
  [{ i := 2, j := 1, k := 9, use := 0, tree := hex% "540000000000000000000000000064281000000000000000000000000000000002000000000000000000000000000d2b2d0000000000000000000000000000000044d10a8" }]

/-- The group 400: the cover of a box by its cells. -/
theorem g400_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 2, c3 := 6 } (3) cells400 = true := by
  decide +kernel

/-- The cells of the group 401. -/
noncomputable def cells401 : List Cell :=
  [{ i := 2, j := 1, k := 24, use := 0, tree := 5604673 }]

/-- The group 401: the cover of a box by its cells. -/
theorem g401_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 3, c3 := 14 } (3) cells401 = true := by
  decide +kernel

/-- The cells of the group 402. -/
noncomputable def cells402 : List Cell :=
  [{ i := 2, j := 1, k := 55, use := 0, tree := 5604673 }]

/-- The group 402: the cover of a box by its cells. -/
theorem g402_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 4, c3 := 30 } (3) cells402 = true := by
  decide +kernel

end N14Cert.Case1

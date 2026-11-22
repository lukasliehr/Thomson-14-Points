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

/-- The cells of the group 433. -/
noncomputable def cells433 : List Cell :=
  [{ i := 9, j := 118, k := 55, use := 0, tree := hex% "a864a7b88500000000000000000000000000000000000000be99d9b39bc" }]

/-- The group 433: the cover of a box by its cells. -/
theorem g433_ok : boxOk run { e1 := 2, c1 := 6, e2 := 4, c2 := 31, e3 := 4, c3 := 30 } (61) cells433 = true := by
  decide +kernel

/-- The cells of the group 434. -/
noncomputable def cells434 : List Cell :=
  [{ i := 9, j := 118, k := 118, use := 0, tree := 5 },
    { i := 9, j := 118, k := 245, use := 0, tree := 5 },
    { i := 9, j := 118, k := 246, use := 0, tree := 5 },
    { i := 9, j := 245, k := 118, use := 0, tree := 5 },
    { i := 9, j := 245, k := 245, use := 0, tree := 5 },
    { i := 9, j := 245, k := 246, use := 0, tree := 5 },
    { i := 9, j := 246, k := 245, use := 0, tree := 5 },
    { i := 9, j := 246, k := 246, use := 0, tree := 5 }]

/-- The group 434: the cover of a box by its cells. -/
theorem g434_ok : boxOk run { e1 := 2, c1 := 6, e2 := 4, c2 := 31, e3 := 4, c3 := 31 } (16905105337) cells434 = true := by
  decide +kernel

/-- The cells of the group 435. -/
noncomputable def cells435 : List Cell :=
  [{ i := 24, j := 9, k := 9, use := 0, tree := 3 }]

/-- The group 435: the cover of a box by its cells. -/
theorem g435_ok : boxOk run { e1 := 2, c1 := 7, e2 := 2, c2 := 6, e3 := 2, c3 := 6 } (60) cells435 = true := by
  decide +kernel

/-- The cells of the group 436. -/
noncomputable def cells436 : List Cell :=
  [{ i := 24, j := 9, k := 24, use := 0, tree := 3 }]

/-- The group 436: the cover of a box by its cells. -/
theorem g436_ok : boxOk run { e1 := 3, c1 := 14, e2 := 2, c2 := 6, e3 := 3, c3 := 14 } (3) cells436 = true := by
  decide +kernel

/-- The cells of the group 437. -/
noncomputable def cells437 : List Cell :=
  [{ i := 24, j := 9, k := 55, use := 0, tree := hex% "9450c07f8000000000000000000000011bdcfc79c" }]

/-- The group 437: the cover of a box by its cells. -/
theorem g437_ok : boxOk run { e1 := 3, c1 := 14, e2 := 2, c2 := 6, e3 := 4, c3 := 30 } (3) cells437 = true := by
  decide +kernel

/-- The cells of the group 438. -/
noncomputable def cells438 : List Cell :=
  [{ i := 24, j := 9, k := 118, use := 0, tree := 12456 },
    { i := 24, j := 9, k := 245, use := 0, tree := 12456 },
    { i := 24, j := 9, k := 246, use := 0, tree := hex% "16d4cda2a8000000000000000000000338ef760b2c" }]

/-- The group 438: the cover of a box by its cells. -/
theorem g438_ok : boxOk run { e1 := 3, c1 := 14, e2 := 2, c2 := 6, e3 := 4, c3 := 31 } (1006) cells438 = true := by
  decide +kernel

/-- The cells of the group 439. -/
noncomputable def cells439 : List Cell :=
  [{ i := 24, j := 24, k := 9, use := 0, tree := 3 },
    { i := 55, j := 24, k := 9, use := 0, tree := hex% "2a3b96d8380000003380a2de58000000000000000000000011bdcfc79c" }]

/-- The group 439: the cover of a box by its cells. -/
theorem g439_ok : boxOk run { e1 := 2, c1 := 7, e2 := 2, c2 := 7, e3 := 2, c3 := 6 } (258548) cells439 = true := by
  decide +kernel

/-- The cells of the group 440. -/
noncomputable def cells440 : List Cell :=
  [{ i := 24, j := 24, k := 24, use := 0, tree := 3 },
    { i := 24, j := 24, k := 55, use := 0, tree := 3 },
    { i := 24, j := 24, k := 118, use := 0, tree := 3 },
    { i := 24, j := 24, k := 245, use := 0, tree := 3 },
    { i := 24, j := 24, k := 246, use := 0, tree := 3 }]

/-- The group 440: the cover of a box by its cells. -/
theorem g440_ok : boxOk run { e1 := 3, c1 := 14, e2 := 3, c2 := 14, e3 := 2, c3 := 7 } (257774) cells440 = true := by
  decide +kernel

/-- The cells of the group 441. -/
noncomputable def cells441 : List Cell :=
  [{ i := 24, j := 55, k := 24, use := 0, tree := 3 }]

/-- The group 441: the cover of a box by its cells. -/
theorem g441_ok : boxOk run { e1 := 3, c1 := 14, e2 := 3, c2 := 15, e3 := 3, c3 := 14 } (61) cells441 = true := by
  decide +kernel

/-- The cells of the group 442. -/
noncomputable def cells442 : List Cell :=
  [{ i := 24, j := 55, k := 55, use := 0, tree := 3 },
    { i := 24, j := 55, k := 118, use := 0, tree := 3 },
    { i := 24, j := 55, k := 245, use := 0, tree := 3 },
    { i := 24, j := 55, k := 246, use := 0, tree := 1834259559700 }]

/-- The group 442: the cover of a box by its cells. -/
theorem g442_ok : boxOk run { e1 := 3, c1 := 14, e2 := 4, c2 := 30, e3 := 3, c3 := 15 } (16110) cells442 = true := by
  decide +kernel

end N14Cert.Case1

module

public import N14Cert.Case0Pos.Run
public import N14.Box.MasterKernel
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.Case0Pos

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The cells of the group 52. -/
noncomputable def cells52 : List Cell :=
  [{ i := 2, j := 24, k := 9, use := 0, tree := 3 }]

/-- The group 52: the cover of a box by its cells. -/
theorem g52_ok : boxOk run { e1 := 1, c1 := 2, e2 := 2, c2 := 7, e3 := 2, c3 := 6 } (61) cells52 = true := by
  decide +kernel

/-- The cells of the group 53. -/
noncomputable def cells53 : List Cell :=
  [{ i := 2, j := 24, k := 24, use := 0, tree := hex% "30000000000000000000000001b51505a4" },
    { i := 2, j := 24, k := 25, use := 0, tree := 20974882804 },
    { i := 2, j := 24, k := 26, use := 0, tree := 57881441892 },
    { i := 2, j := 24, k := 27, use := 0, tree := 5 },
    { i := 2, j := 24, k := 28, use := 0, tree := 5 }]

/-- The group 53: the cover of a box by its cells. -/
theorem g53_ok : boxOk run { e1 := 1, c1 := 2, e2 := 3, c2 := 14, e3 := 2, c3 := 7 } (257774) cells53 = true := by
  decide +kernel

/-- The cells of the group 54. -/
noncomputable def cells54 : List Cell :=
  [{ i := 2, j := 25, k := 24, use := 0, tree := hex% "aaeae7828000000000000000000000004e2334ff4" },
    { i := 2, j := 25, k := 25, use := 0, tree := 5 },
    { i := 2, j := 25, k := 26, use := 0, tree := 5 },
    { i := 2, j := 25, k := 27, use := 0, tree := 5 },
    { i := 2, j := 25, k := 28, use := 0, tree := 5 },
    { i := 2, j := 26, k := 25, use := 0, tree := 5 },
    { i := 2, j := 26, k := 26, use := 0, tree := 5 },
    { i := 2, j := 26, k := 27, use := 0, tree := 5 },
    { i := 2, j := 26, k := 28, use := 0, tree := 5 },
    { i := 2, j := 27, k := 26, use := 0, tree := 5 },
    { i := 2, j := 27, k := 27, use := 0, tree := 5 },
    { i := 2, j := 27, k := 28, use := 0, tree := 5 },
    { i := 2, j := 28, k := 27, use := 0, tree := 5 },
    { i := 2, j := 28, k := 28, use := 0, tree := 5 }]

/-- The group 54: the cover of a box by its cells. -/
theorem g54_ok : boxOk run { e1 := 1, c1 := 2, e2 := 3, c2 := 15, e3 := 2, c3 := 7 } (hex% "3ef9f6fb9f6fbb9f6") cells54 = true := by
  decide +kernel

/-- The cells of the group 55. -/
noncomputable def cells55 : List Cell :=
  [{ i := 9, j := 2, k := 1, use := 0, tree := hex% "8525cd00000000005ff23580000000000000024" }]

/-- The group 55: the cover of a box by its cells. -/
theorem g55_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 1 } (60) cells55 = true := by
  decide +kernel

/-- The cells of the group 56. -/
noncomputable def cells56 : List Cell :=
  [{ i := 9, j := 2, k := 2, use := 0, tree := hex% "d824600000000007a689f80000000000000004" }]

/-- The group 56: the cover of a box by its cells. -/
theorem g56_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 2 } (60) cells56 = true := by
  decide +kernel

/-- The cells of the group 57. -/
noncomputable def cells57 : List Cell :=
  [{ i := 9, j := 2, k := 9, use := 0, tree := hex% "5d721a80000000000000014" },
    { i := 9, j := 2, k := 24, use := 0, tree := 3 },
    { i := 9, j := 2, k := 25, use := 0, tree := 3 },
    { i := 9, j := 2, k := 26, use := 0, tree := 3 },
    { i := 9, j := 2, k := 27, use := 0, tree := 3 },
    { i := 9, j := 2, k := 28, use := 0, tree := 3 }]

/-- The group 57: the cover of a box by its cells. -/
theorem g57_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 3 } (66829240) cells57 = true := by
  decide +kernel

/-- The cells of the group 58. -/
noncomputable def cells58 : List Cell :=
  [{ i := 9, j := 9, k := 2, use := 0, tree := hex% "5d721a800000000000000080000000000000014" },
    { i := 24, j := 9, k := 2, use := 0, tree := 3 }]

/-- The group 58: the cover of a box by its cells. -/
theorem g58_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 3, e3 := 1, c3 := 2 } (258548) cells58 = true := by
  decide +kernel

/-- The cells of the group 59. -/
noncomputable def cells59 : List Cell :=
  [{ i := 9, j := 9, k := 9, use := 0, tree := 3 },
    { i := 9, j := 9, k := 24, use := 0, tree := 3 },
    { i := 9, j := 9, k := 25, use := 0, tree := 3 },
    { i := 9, j := 9, k := 26, use := 0, tree := 3 },
    { i := 9, j := 9, k := 27, use := 0, tree := 3 },
    { i := 9, j := 9, k := 28, use := 0, tree := 3 }]

/-- The group 59: the cover of a box by its cells. -/
theorem g59_ok : boxOk run { e1 := 2, c1 := 6, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (4124398) cells59 = true := by
  decide +kernel

/-- The cells of the group 60. -/
noncomputable def cells60 : List Cell :=
  [{ i := 9, j := 24, k := 9, use := 0, tree := 3 },
    { i := 9, j := 24, k := 24, use := 0, tree := 3 },
    { i := 9, j := 24, k := 25, use := 0, tree := 3 },
    { i := 9, j := 24, k := 26, use := 0, tree := 3 },
    { i := 9, j := 24, k := 27, use := 0, tree := 3 },
    { i := 9, j := 24, k := 28, use := 0, tree := 3 },
    { i := 9, j := 25, k := 24, use := 0, tree := 3 },
    { i := 9, j := 25, k := 25, use := 0, tree := 3 },
    { i := 9, j := 25, k := 26, use := 0, tree := 3 },
    { i := 9, j := 25, k := 27, use := 0, tree := 3 },
    { i := 9, j := 25, k := 28, use := 0, tree := 5 },
    { i := 9, j := 26, k := 25, use := 0, tree := 3 },
    { i := 9, j := 26, k := 26, use := 0, tree := 5 },
    { i := 9, j := 26, k := 27, use := 0, tree := 5 },
    { i := 9, j := 26, k := 28, use := 0, tree := 5 },
    { i := 9, j := 27, k := 26, use := 0, tree := 5 },
    { i := 9, j := 27, k := 27, use := 0, tree := 5 },
    { i := 9, j := 27, k := 28, use := 0, tree := 5 },
    { i := 9, j := 28, k := 27, use := 0, tree := 5 },
    { i := 9, j := 28, k := 28, use := 0, tree := 5 }]

/-- The group 60: the cover of a box by its cells. -/
theorem g60_ok : boxOk run { e1 := 2, c1 := 6, e2 := 2, c2 := 7, e3 := 1, c3 := 3 } (hex% "3ef9f6fb9f6fbb9f6fbbb9f6") cells60 = true := by
  decide +kernel

/-- The cells of the group 61. -/
noncomputable def cells61 : List Cell :=
  [{ i := 24, j := 9, k := 9, use := 0, tree := 3 },
    { i := 24, j := 9, k := 24, use := 0, tree := 3 },
    { i := 24, j := 9, k := 25, use := 0, tree := 3 },
    { i := 24, j := 9, k := 26, use := 0, tree := 3 },
    { i := 24, j := 9, k := 27, use := 0, tree := 3 },
    { i := 24, j := 9, k := 28, use := 0, tree := 3 }]

/-- The group 61: the cover of a box by its cells. -/
theorem g61_ok : boxOk run { e1 := 2, c1 := 7, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (1069267186) cells61 = true := by
  decide +kernel

/-- The cells of the group 62. -/
noncomputable def cells62 : List Cell :=
  [{ i := 24, j := 24, k := 9, use := 0, tree := 3 },
    { i := 25, j := 24, k := 9, use := 0, tree := 3 }]

/-- The group 62: the cover of a box by its cells. -/
theorem g62_ok : boxOk run { e1 := 2, c1 := 7, e2 := 2, c2 := 7, e3 := 2, c3 := 6 } (258548) cells62 = true := by
  decide +kernel

end N14Cert.Case0Pos

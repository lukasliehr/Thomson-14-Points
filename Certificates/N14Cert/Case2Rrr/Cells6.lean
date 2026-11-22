module

public import N14Cert.Case2Rrr.Run
public import N14.Box.MasterKernel
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.Case2Rrr

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The cells of the group 57. -/
noncomputable def cells57 : List Cell :=
  [{ i := 7, j := 9, k := 9, use := 0, tree := hex% "d9000000000018ef9700000000000000000000000000000000000000000000000089b4d1699" },
    { i := 20, j := 9, k := 9, use := 0, tree := hex% "369900000000001f395700000000000000000000000000000000000000000000000089b4d1699" },
    { i := 21, j := 22, k := 9, use := 0, tree := hex% "da6cb4196da640000000000058048800000000000000000000000000000000000000000000000429a" },
    { i := 21, j := 23, k := 9, use := 0, tree := 3 },
    { i := 2, j := 9, k := 24, use := 0, tree := 3 },
    { i := 2, j := 9, k := 25, use := 0, tree := 3 },
    { i := 2, j := 9, k := 26, use := 0, tree := 3 },
    { i := 2, j := 9, k := 27, use := 0, tree := 3 },
    { i := 2, j := 9, k := 28, use := 0, tree := 3 }]

/-- The group 57: the cover of a box by its cells. -/
theorem g57_ok : boxOk run { e1 := 1, c1 := 2, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (16893540146) cells57 = true := by
  decide +kernel

/-- The cells of the group 58. -/
noncomputable def cells58 : List Cell :=
  [{ i := 2, j := 24, k := 9, use := 0, tree := 3 },
    { i := 2, j := 24, k := 24, use := 0, tree := 3 },
    { i := 2, j := 24, k := 25, use := 0, tree := 3 },
    { i := 2, j := 24, k := 26, use := 0, tree := 3 },
    { i := 2, j := 24, k := 27, use := 0, tree := 5 },
    { i := 2, j := 24, k := 28, use := 0, tree := 5 },
    { i := 2, j := 25, k := 24, use := 0, tree := 3 },
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

/-- The group 58: the cover of a box by its cells. -/
theorem g58_ok : boxOk run { e1 := 1, c1 := 2, e2 := 2, c2 := 7, e3 := 1, c3 := 3 } (hex% "3ef9f6fb9f6fbb9f6fbbb9f6") cells58 = true := by
  decide +kernel

/-- The cells of the group 59. -/
noncomputable def cells59 : List Cell :=
  [{ i := 9, j := 2, k := 1, use := 0, tree := hex% "9897000000000000338ec00000000000000000000000000005fc14" }]

/-- The group 59: the cover of a box by its cells. -/
theorem g59_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 1 } (60) cells59 = true := by
  decide +kernel

/-- The cells of the group 60. -/
noncomputable def cells60 : List Cell :=
  [{ i := 9, j := 2, k := 2, use := 0, tree := hex% "21f4800000000020a4c9800000000000000000000000000000004" }]

/-- The group 60: the cover of a box by its cells. -/
theorem g60_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 2 } (60) cells60 = true := by
  decide +kernel

/-- The cells of the group 61. -/
noncomputable def cells61 : List Cell :=
  [{ i := 9, j := 2, k := 9, use := 0, tree := hex% "542a150000000000000000000000000008ec3a000000000000000000000000000000008000000000000000000000000002797a000000000000000000000000000000001102400000000000000000000000001508d5c0000000000000000000000000000000220a8" },
    { i := 9, j := 2, k := 24, use := 0, tree := 3 },
    { i := 9, j := 2, k := 25, use := 0, tree := 3 },
    { i := 9, j := 2, k := 26, use := 0, tree := 3 },
    { i := 9, j := 2, k := 27, use := 0, tree := 3 },
    { i := 9, j := 2, k := 28, use := 0, tree := 3 }]

/-- The group 61: the cover of a box by its cells. -/
theorem g61_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 3 } (66829240) cells61 = true := by
  decide +kernel

/-- The cells of the group 62. -/
noncomputable def cells62 : List Cell :=
  [{ i := 9, j := 9, k := 2, use := 0, tree := hex% "1644e080000000000b2270000000000000000000000000000000004" },
    { i := 24, j := 9, k := 2, use := 0, tree := 3 }]

/-- The group 62: the cover of a box by its cells. -/
theorem g62_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 3, e3 := 1, c3 := 2 } (258548) cells62 = true := by
  decide +kernel

/-- The cells of the group 63. -/
noncomputable def cells63 : List Cell :=
  [{ i := 9, j := 9, k := 9, use := 0, tree := hex% "2ff58c0000000000646dca0000000000000000000000000000000100000000000c8db9400000000000000000000000000000000000000000000000236000000000000000000000000000aca58000000000000000000000000000000010b69b44221a658" },
    { i := 9, j := 9, k := 24, use := 0, tree := 3 },
    { i := 9, j := 9, k := 25, use := 0, tree := 3 },
    { i := 9, j := 9, k := 26, use := 0, tree := 3 },
    { i := 9, j := 9, k := 27, use := 0, tree := 3 },
    { i := 9, j := 9, k := 28, use := 0, tree := 3 }]

/-- The group 63: the cover of a box by its cells. -/
theorem g63_ok : boxOk run { e1 := 2, c1 := 6, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (4124398) cells63 = true := by
  decide +kernel

end N14Cert.Case2Rrr

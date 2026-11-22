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

/-- The cells of the group 64. -/
noncomputable def cells64 : List Cell :=
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

/-- The group 64: the cover of a box by its cells. -/
theorem g64_ok : boxOk run { e1 := 2, c1 := 6, e2 := 2, c2 := 7, e3 := 1, c3 := 3 } (hex% "3ef9f6fb9f6fbb9f6fbbb9f6") cells64 = true := by
  decide +kernel

/-- The cells of the group 65. -/
noncomputable def cells65 : List Cell :=
  [{ i := 24, j := 9, k := 9, use := 0, tree := 3 },
    { i := 24, j := 9, k := 24, use := 0, tree := 3 },
    { i := 24, j := 9, k := 25, use := 0, tree := 3 },
    { i := 24, j := 9, k := 26, use := 0, tree := 3 },
    { i := 24, j := 9, k := 27, use := 0, tree := 3 },
    { i := 24, j := 9, k := 28, use := 0, tree := 3 }]

/-- The group 65: the cover of a box by its cells. -/
theorem g65_ok : boxOk run { e1 := 2, c1 := 7, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (1069267186) cells65 = true := by
  decide +kernel

/-- The cells of the group 66. -/
noncomputable def cells66 : List Cell :=
  [{ i := 24, j := 24, k := 9, use := 0, tree := 3 },
    { i := 25, j := 24, k := 9, use := 0, tree := 3 }]

/-- The group 66: the cover of a box by its cells. -/
theorem g66_ok : boxOk run { e1 := 2, c1 := 7, e2 := 2, c2 := 7, e3 := 2, c3 := 6 } (258548) cells66 = true := by
  decide +kernel

/-- The cells of the group 67. -/
noncomputable def cells67 : List Cell :=
  [{ i := 24, j := 24, k := 24, use := 0, tree := 3 },
    { i := 24, j := 24, k := 25, use := 0, tree := 3 },
    { i := 24, j := 24, k := 26, use := 0, tree := 3 },
    { i := 24, j := 24, k := 27, use := 0, tree := 3 },
    { i := 24, j := 24, k := 28, use := 0, tree := 3 },
    { i := 24, j := 25, k := 24, use := 0, tree := 3 },
    { i := 24, j := 25, k := 25, use := 0, tree := 3 },
    { i := 24, j := 25, k := 26, use := 0, tree := 3 },
    { i := 24, j := 25, k := 27, use := 0, tree := 3 },
    { i := 24, j := 25, k := 28, use := 0, tree := 3 },
    { i := 24, j := 26, k := 25, use := 0, tree := 3 },
    { i := 24, j := 26, k := 26, use := 0, tree := 3 },
    { i := 24, j := 26, k := 27, use := 0, tree := 3 },
    { i := 24, j := 26, k := 28, use := 0, tree := 3 },
    { i := 24, j := 27, k := 26, use := 0, tree := 3 },
    { i := 24, j := 27, k := 27, use := 0, tree := 5 },
    { i := 24, j := 27, k := 28, use := 0, tree := 5 },
    { i := 24, j := 28, k := 27, use := 0, tree := 5 },
    { i := 24, j := 28, k := 28, use := 0, tree := 5 }]

/-- The group 67: the cover of a box by its cells. -/
theorem g67_ok : boxOk run { e1 := 3, c1 := 14, e2 := 2, c2 := 7, e3 := 2, c3 := 7 } (hex% "3ef9f6fb9f6fbb9f6fbbb9") cells67 = true := by
  decide +kernel

/-- The cells of the group 68. -/
noncomputable def cells68 : List Cell :=
  [{ i := 25, j := 24, k := 24, use := 0, tree := 3 },
    { i := 25, j := 24, k := 25, use := 0, tree := 3 },
    { i := 25, j := 24, k := 26, use := 0, tree := 3 },
    { i := 25, j := 24, k := 27, use := 0, tree := 3 },
    { i := 25, j := 24, k := 28, use := 0, tree := 3 }]

/-- The group 68: the cover of a box by its cells. -/
theorem g68_ok : boxOk run { e1 := 3, c1 := 15, e2 := 3, c2 := 14, e3 := 2, c3 := 7 } (66828530) cells68 = true := by
  decide +kernel

/-- The cells of the group 69. -/
noncomputable def cells69 : List Cell :=
  [{ i := 25, j := 25, k := 24, use := 0, tree := 3 },
    { i := 26, j := 25, k := 24, use := 0, tree := 3 }]

/-- The group 69: the cover of a box by its cells. -/
theorem g69_ok : boxOk run { e1 := 3, c1 := 15, e2 := 3, c2 := 15, e3 := 3, c3 := 14 } (258548) cells69 = true := by
  decide +kernel

/-- The cells of the group 70. -/
noncomputable def cells70 : List Cell :=
  [{ i := 25, j := 25, k := 25, use := 0, tree := 3 },
    { i := 25, j := 25, k := 26, use := 0, tree := 3 },
    { i := 25, j := 25, k := 27, use := 0, tree := 3 },
    { i := 25, j := 25, k := 28, use := 0, tree := 3 },
    { i := 25, j := 26, k := 25, use := 0, tree := 3 },
    { i := 25, j := 26, k := 26, use := 0, tree := 3 },
    { i := 25, j := 26, k := 27, use := 0, tree := 3 },
    { i := 25, j := 26, k := 28, use := 0, tree := 3 },
    { i := 25, j := 27, k := 26, use := 0, tree := 3 },
    { i := 25, j := 27, k := 27, use := 0, tree := 3 },
    { i := 25, j := 27, k := 28, use := 0, tree := 3 },
    { i := 25, j := 28, k := 27, use := 0, tree := 3 },
    { i := 25, j := 28, k := 28, use := 0, tree := 5 }]

/-- The group 70: the cover of a box by its cells. -/
theorem g70_ok : boxOk run { e1 := 4, c1 := 30, e2 := 3, c2 := 15, e3 := 3, c3 := 15 } (283620603757788089) cells70 = true := by
  decide +kernel

/-- The cells of the group 71. -/
noncomputable def cells71 : List Cell :=
  [{ i := 26, j := 25, k := 25, use := 0, tree := 3 },
    { i := 26, j := 25, k := 26, use := 0, tree := 3 },
    { i := 26, j := 25, k := 27, use := 0, tree := 3 },
    { i := 26, j := 25, k := 28, use := 0, tree := 3 }]

/-- The group 71: the cover of a box by its cells. -/
theorem g71_ok : boxOk run { e1 := 4, c1 := 31, e2 := 4, c2 := 30, e3 := 3, c3 := 15 } (4176114) cells71 = true := by
  decide +kernel

/-- The cells of the group 72. -/
noncomputable def cells72 : List Cell :=
  [{ i := 26, j := 26, k := 25, use := 0, tree := 3 },
    { i := 27, j := 26, k := 25, use := 0, tree := 3 }]

/-- The group 72: the cover of a box by its cells. -/
theorem g72_ok : boxOk run { e1 := 4, c1 := 31, e2 := 4, c2 := 31, e3 := 4, c3 := 30 } (258548) cells72 = true := by
  decide +kernel

end N14Cert.Case2Rrr

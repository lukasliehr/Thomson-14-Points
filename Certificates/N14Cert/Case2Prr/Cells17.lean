module

public import N14Cert.Case2Prr.Run
public import N14.Box.MasterKernel
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.Case2Prr

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The cells of the group 119. -/
noncomputable def cells119 : List Cell :=
  [{ i := 22, j := 22, k := 22, use := 0, tree := hex% "da6d16d368869b440000000001ae591c0000000000000000000000000000000000000000000000020" },
    { i := 22, j := 22, k := 23, use := 0, tree := 3 },
    { i := 22, j := 23, k := 9, use := 0, tree := 3 },
    { i := 23, j := 9, k := 9, use := 0, tree := 3 },
    { i := 9, j := 9, k := 24, use := 0, tree := 3 },
    { i := 9, j := 9, k := 25, use := 0, tree := 3 },
    { i := 9, j := 9, k := 26, use := 0, tree := 3 },
    { i := 9, j := 9, k := 27, use := 0, tree := 3 },
    { i := 9, j := 9, k := 28, use := 0, tree := 3 }]

/-- The group 119: the cover of a box by its cells. -/
theorem g119_ok : boxOk run { e1 := 2, c1 := 6, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (16893542290) cells119 = true := by
  decide +kernel

/-- The cells of the group 120. -/
noncomputable def cells120 : List Cell :=
  [{ i := 9, j := 24, k := 9, use := 0, tree := 3 },
    { i := 9, j := 25, k := 9, use := 0, tree := 3 },
    { i := 9, j := 26, k := 9, use := 0, tree := 3 },
    { i := 9, j := 27, k := 9, use := 0, tree := 3 },
    { i := 9, j := 28, k := 9, use := 0, tree := 3 }]

/-- The group 120: the cover of a box by its cells. -/
theorem g120_ok : boxOk run { e1 := 2, c1 := 6, e2 := 2, c2 := 7, e3 := 2, c3 := 6 } (253405) cells120 = true := by
  decide +kernel

/-- The cells of the group 121. -/
noncomputable def cells121 : List Cell :=
  [{ i := 9, j := 24, k := 24, use := 0, tree := 3 },
    { i := 9, j := 24, k := 25, use := 0, tree := 3 },
    { i := 9, j := 24, k := 26, use := 0, tree := 3 },
    { i := 9, j := 24, k := 27, use := 0, tree := 3 },
    { i := 9, j := 24, k := 28, use := 0, tree := 3 }]

/-- The group 121: the cover of a box by its cells. -/
theorem g121_ok : boxOk run { e1 := 2, c1 := 6, e2 := 3, c2 := 14, e3 := 2, c3 := 7 } (257774) cells121 = true := by
  decide +kernel

/-- The cells of the group 122. -/
noncomputable def cells122 : List Cell :=
  [{ i := 9, j := 25, k := 24, use := 0, tree := 3 },
    { i := 9, j := 26, k := 24, use := 0, tree := 3 },
    { i := 9, j := 27, k := 24, use := 0, tree := 3 },
    { i := 9, j := 28, k := 24, use := 0, tree := 3 },
    { i := 9, j := 25, k := 25, use := 0, tree := 3 },
    { i := 9, j := 25, k := 26, use := 0, tree := 3 },
    { i := 9, j := 25, k := 27, use := 0, tree := 3 },
    { i := 9, j := 25, k := 28, use := 0, tree := 5 },
    { i := 9, j := 26, k := 25, use := 0, tree := 3 },
    { i := 9, j := 27, k := 25, use := 0, tree := 3 },
    { i := 9, j := 28, k := 25, use := 0, tree := 5 },
    { i := 9, j := 26, k := 26, use := 0, tree := 5 },
    { i := 9, j := 26, k := 27, use := 0, tree := 5 },
    { i := 9, j := 26, k := 28, use := 0, tree := 5 },
    { i := 9, j := 27, k := 26, use := 0, tree := 5 },
    { i := 9, j := 28, k := 26, use := 0, tree := 5 },
    { i := 9, j := 27, k := 27, use := 0, tree := 5 },
    { i := 9, j := 27, k := 28, use := 0, tree := 5 },
    { i := 9, j := 28, k := 27, use := 0, tree := 5 },
    { i := 9, j := 28, k := 28, use := 0, tree := 5 }]

/-- The group 122: the cover of a box by its cells. -/
theorem g122_ok : boxOk run { e1 := 2, c1 := 6, e2 := 3, c2 := 15, e3 := 2, c3 := 7 } (hex% "3ef9f6fb9f76fbb9f776") cells122 = true := by
  decide +kernel

/-- The cells of the group 123. -/
noncomputable def cells123 : List Cell :=
  [{ i := 24, j := 9, k := 9, use := 0, tree := 3 },
    { i := 24, j := 9, k := 24, use := 0, tree := 3 },
    { i := 24, j := 9, k := 25, use := 0, tree := 3 },
    { i := 24, j := 9, k := 26, use := 0, tree := 3 },
    { i := 24, j := 9, k := 27, use := 0, tree := 3 },
    { i := 24, j := 9, k := 28, use := 0, tree := 3 }]

/-- The group 123: the cover of a box by its cells. -/
theorem g123_ok : boxOk run { e1 := 2, c1 := 7, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (1069267186) cells123 = true := by
  decide +kernel

/-- The cells of the group 124. -/
noncomputable def cells124 : List Cell :=
  [{ i := 24, j := 24, k := 9, use := 0, tree := 3 },
    { i := 24, j := 25, k := 9, use := 0, tree := 3 },
    { i := 24, j := 26, k := 9, use := 0, tree := 3 },
    { i := 24, j := 27, k := 9, use := 0, tree := 3 },
    { i := 24, j := 28, k := 9, use := 0, tree := 3 },
    { i := 25, j := 24, k := 9, use := 0, tree := 3 },
    { i := 25, j := 25, k := 9, use := 0, tree := 3 },
    { i := 25, j := 26, k := 9, use := 0, tree := 3 },
    { i := 25, j := 27, k := 9, use := 0, tree := 3 },
    { i := 25, j := 28, k := 9, use := 0, tree := 5 },
    { i := 26, j := 25, k := 9, use := 0, tree := 3 },
    { i := 26, j := 26, k := 9, use := 0, tree := 5 },
    { i := 26, j := 27, k := 9, use := 0, tree := 5 },
    { i := 26, j := 28, k := 9, use := 0, tree := 5 },
    { i := 27, j := 26, k := 9, use := 0, tree := 5 },
    { i := 27, j := 27, k := 9, use := 0, tree := 5 },
    { i := 27, j := 28, k := 9, use := 0, tree := 5 },
    { i := 28, j := 27, k := 9, use := 0, tree := 5 },
    { i := 28, j := 28, k := 9, use := 0, tree := 5 }]

/-- The group 124: the cover of a box by its cells. -/
theorem g124_ok : boxOk run { e1 := 2, c1 := 7, e2 := 2, c2 := 7, e3 := 2, c3 := 6 } (hex% "3df4f1f74f1f774f1f7774") cells124 = true := by
  decide +kernel

/-- The cells of the group 125. -/
noncomputable def cells125 : List Cell :=
  [{ i := 24, j := 24, k := 24, use := 0, tree := 3 },
    { i := 24, j := 24, k := 25, use := 0, tree := 3 },
    { i := 24, j := 24, k := 26, use := 0, tree := 3 },
    { i := 24, j := 24, k := 27, use := 0, tree := 3 },
    { i := 24, j := 24, k := 28, use := 0, tree := 3 }]

/-- The group 125: the cover of a box by its cells. -/
theorem g125_ok : boxOk run { e1 := 3, c1 := 14, e2 := 3, c2 := 14, e3 := 2, c3 := 7 } (257774) cells125 = true := by
  decide +kernel

end N14Cert.Case2Prr

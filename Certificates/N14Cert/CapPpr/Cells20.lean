module

public import N14Cert.CapPpr.Run
public import N14.Box.MasterKernel
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.CapPpr

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The cells of the group 132. -/
noncomputable def cells132 : List Cell :=
  [{ i := 3, j := 19, k := 7, use := 0, tree := hex% "3400000000000000000000000000000000000000bc9e1801d4000000000000000000000000001a17b00000014cdbe65a52006814014a068" }]

/-- The group 132: the cover of a box by its cells. -/
theorem g132_ok : boxOk run { e1 := 4, c1 := 0, e2 := 3, c2 := 9, e3 := 2, c3 := 4 } (3) cells132 = true := by
  decide +kernel

/-- The cells of the group 133. -/
noncomputable def cells133 : List Cell :=
  [{ i := 3, j := 7, k := 8, use := 0, tree := 20584 }]

/-- The group 133: the cover of a box by its cells. -/
theorem g133_ok : boxOk run { e1 := 4, c1 := 0, e2 := 2, c2 := 4, e3 := 2, c3 := 5 } (3) cells133 = true := by
  decide +kernel

/-- The cells of the group 134. -/
noncomputable def cells134 : List Cell :=
  [{ i := 3, j := 8, k := 2, use := 0, tree := hex% "a62dfea30e5800000000000000000009c51596150b480000d0bf4744519c02a" }]

/-- The group 134: the cover of a box by its cells. -/
theorem g134_ok : boxOk run { e1 := 4, c1 := 0, e2 := 2, c2 := 5, e3 := 1, c3 := 2 } (3) cells134 = true := by
  decide +kernel

/-- The cells of the group 135. -/
noncomputable def cells135 : List Cell :=
  [{ i := 3, j := 2, k := 9, use := 0, tree := 5 },
    { i := 3, j := 2, k := 24, use := 0, tree := 5 }]

/-- The group 135: the cover of a box by its cells. -/
theorem g135_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 1, c3 := 3 } (1072840456) cells135 = true := by
  decide +kernel

/-- The cells of the group 136. -/
noncomputable def cells136 : List Cell :=
  [{ i := 3, j := 9, k := 2, use := 0, tree := 5 }]

/-- The group 136: the cover of a box by its cells. -/
theorem g136_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 3, e3 := 1, c3 := 2 } (261892) cells136 = true := by
  decide +kernel

/-- The cells of the group 137. -/
noncomputable def cells137 : List Cell :=
  [{ i := 3, j := 9, k := 9, use := 0, tree := 5 },
    { i := 3, j := 9, k := 24, use := 0, tree := 5 },
    { i := 3, j := 24, k := 9, use := 0, tree := 5 },
    { i := 3, j := 24, k := 24, use := 0, tree := 5 },
    { i := 3, j := 55, k := 24, use := 0, tree := 5 }]

/-- The group 137: the cover of a box by its cells. -/
theorem g137_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 3, e3 := 1, c3 := 3 } (hex% "3ffd2fc93fc4bfc8fc24") cells137 = true := by
  decide +kernel

end N14Cert.CapPpr

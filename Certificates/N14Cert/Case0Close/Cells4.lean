module

public import N14Cert.Case0Close.Run
public import N14.Box.MasterKernel
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.Case0Close

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The cells of the group 28. -/
noncomputable def cells28 : List Cell :=
  [{ i := 26, j := 25, k := 1, use := 0, tree := 3 },
    { i := 26, j := 25, k := 2, use := 0, tree := 3 },
    { i := 26, j := 25, k := 3, use := 0, tree := 3 },
    { i := 26, j := 25, k := 4, use := 0, tree := 3 }]

/-- The group 28: the cover of a box by its cells. -/
theorem g28_ok : boxOk run { e1 := 4, c1 := 31, e2 := 4, c2 := 30, e3 := 3, c3 := 15 } (4176114) cells28 = true := by
  decide +kernel

/-- The cells of the group 29. -/
noncomputable def cells29 : List Cell :=
  [{ i := 26, j := 26, k := 1, use := 0, tree := 3 },
    { i := 27, j := 26, k := 1, use := 0, tree := 3 }]

/-- The group 29: the cover of a box by its cells. -/
theorem g29_ok : boxOk run { e1 := 4, c1 := 31, e2 := 4, c2 := 31, e3 := 4, c3 := 30 } (258548) cells29 = true := by
  decide +kernel

/-- The cells of the group 30. -/
noncomputable def cells30 : List Cell :=
  [{ i := 26, j := 26, k := 2, use := 0, tree := 3 },
    { i := 26, j := 26, k := 3, use := 0, tree := 3 },
    { i := 26, j := 26, k := 4, use := 0, tree := 3 },
    { i := 26, j := 27, k := 2, use := 0, tree := 3 },
    { i := 26, j := 27, k := 3, use := 0, tree := 3 },
    { i := 26, j := 27, k := 4, use := 0, tree := 3 },
    { i := 26, j := 28, k := 3, use := 0, tree := 3 },
    { i := 26, j := 28, k := 4, use := 0, tree := 3 }]

/-- The group 30: the cover of a box by its cells. -/
theorem g30_ok : boxOk run { e1 := 5, c1 := 62, e2 := 4, c2 := 31, e3 := 4, c3 := 31 } (16905105337) cells30 = true := by
  decide +kernel

/-- The cells of the group 31. -/
noncomputable def cells31 : List Cell :=
  [{ i := 27, j := 26, k := 2, use := 0, tree := 3 },
    { i := 27, j := 26, k := 3, use := 0, tree := 3 },
    { i := 27, j := 26, k := 4, use := 0, tree := 3 },
    { i := 27, j := 27, k := 2, use := 0, tree := 3 },
    { i := 28, j := 27, k := 2, use := 0, tree := 3 },
    { i := 27, j := 27, k := 3, use := 0, tree := 3 },
    { i := 27, j := 27, k := 4, use := 0, tree := 3 },
    { i := 27, j := 28, k := 3, use := 0, tree := 3 },
    { i := 27, j := 28, k := 4, use := 0, tree := 3 },
    { i := 28, j := 27, k := 3, use := 0, tree := 3 },
    { i := 28, j := 27, k := 4, use := 0, tree := 3 },
    { i := 28, j := 28, k := 3, use := 0, tree := 3 },
    { i := 28, j := 28, k := 4, use := 0, tree := 3 }]

/-- The group 31: the cover of a box by its cells. -/
theorem g31_ok : boxOk run { e1 := 5, c1 := 63, e2 := 4, c2 := 31, e3 := 4, c3 := 31 } (hex% "3ef9fbe4f7d2fe3c9") cells31 = true := by
  decide +kernel

end N14Cert.Case0Close

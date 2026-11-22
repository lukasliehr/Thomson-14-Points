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

/-- The cells of the group 73. -/
noncomputable def cells73 : List Cell :=
  [{ i := 26, j := 26, k := 26, use := 0, tree := 3 },
    { i := 26, j := 26, k := 27, use := 0, tree := 3 },
    { i := 26, j := 26, k := 28, use := 0, tree := 3 },
    { i := 26, j := 27, k := 26, use := 0, tree := 3 },
    { i := 26, j := 27, k := 27, use := 0, tree := 3 },
    { i := 26, j := 27, k := 28, use := 0, tree := 3 },
    { i := 26, j := 28, k := 27, use := 0, tree := 3 },
    { i := 26, j := 28, k := 28, use := 0, tree := 3 }]

/-- The group 73: the cover of a box by its cells. -/
theorem g73_ok : boxOk run { e1 := 5, c1 := 62, e2 := 4, c2 := 31, e3 := 4, c3 := 31 } (16905105337) cells73 = true := by
  decide +kernel

/-- The cells of the group 74. -/
noncomputable def cells74 : List Cell :=
  [{ i := 27, j := 26, k := 26, use := 0, tree := 3 },
    { i := 27, j := 26, k := 27, use := 0, tree := 3 },
    { i := 27, j := 26, k := 28, use := 0, tree := 3 },
    { i := 27, j := 27, k := 26, use := 0, tree := 3 },
    { i := 28, j := 27, k := 26, use := 0, tree := 3 },
    { i := 27, j := 27, k := 27, use := 0, tree := 3 },
    { i := 27, j := 27, k := 28, use := 0, tree := 3 },
    { i := 27, j := 28, k := 27, use := 0, tree := 3 },
    { i := 27, j := 28, k := 28, use := 0, tree := 3 },
    { i := 28, j := 27, k := 27, use := 0, tree := 3 },
    { i := 28, j := 27, k := 28, use := 0, tree := 3 },
    { i := 28, j := 28, k := 27, use := 0, tree := 3 },
    { i := 28, j := 28, k := 28, use := 0, tree := 3 }]

/-- The group 74: the cover of a box by its cells. -/
theorem g74_ok : boxOk run { e1 := 5, c1 := 63, e2 := 4, c2 := 31, e3 := 4, c3 := 31 } (hex% "3ef9fbe4f7d2fe3c9") cells74 = true := by
  decide +kernel

end N14Cert.Case2Rrr

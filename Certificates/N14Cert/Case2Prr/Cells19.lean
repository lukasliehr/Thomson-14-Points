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

/-- The cells of the group 133. -/
noncomputable def cells133 : List Cell :=
  [{ i := 27, j := 26, k := 26, use := 0, tree := 3 },
    { i := 27, j := 26, k := 27, use := 0, tree := 3 },
    { i := 27, j := 26, k := 28, use := 0, tree := 3 },
    { i := 27, j := 27, k := 26, use := 0, tree := 3 },
    { i := 27, j := 28, k := 26, use := 0, tree := 3 },
    { i := 28, j := 27, k := 26, use := 0, tree := 3 },
    { i := 28, j := 28, k := 26, use := 0, tree := 3 },
    { i := 27, j := 27, k := 27, use := 0, tree := 3 },
    { i := 27, j := 27, k := 28, use := 0, tree := 3 },
    { i := 27, j := 28, k := 27, use := 0, tree := 3 },
    { i := 27, j := 28, k := 28, use := 0, tree := 3 },
    { i := 28, j := 27, k := 27, use := 0, tree := 3 },
    { i := 28, j := 27, k := 28, use := 0, tree := 3 },
    { i := 28, j := 28, k := 27, use := 0, tree := 3 },
    { i := 28, j := 28, k := 28, use := 0, tree := 3 }]

/-- The group 133: the cover of a box by its cells. -/
theorem g133_ok : boxOk run { e1 := 5, c1 := 63, e2 := 4, c2 := 31, e3 := 4, c3 := 31 } (hex% "3ef9fbe4f7d2fe3c9") cells133 = true := by
  decide +kernel

end N14Cert.Case2Prr

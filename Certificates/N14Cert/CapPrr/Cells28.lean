module

public import N14Cert.CapPrr.Run
public import N14.Box.MasterKernel
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.CapPrr

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The cells of the group 258. -/
noncomputable def cells258 : List Cell :=
  [{ i := 24, j := 9, k := 9, use := 0, tree := hex% "558066c00000000000000004" },
    { i := 24, j := 9, k := 24, use := 0, tree := hex% "45c7e02080000000000000000000000041bb6f428000000000000005c" }]

/-- The group 258: the cover of a box by its cells. -/
theorem g258_ok : boxOk run { e1 := 2, c1 := 7, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (260338) cells258 = true := by
  decide +kernel

/-- The cells of the group 259. -/
noncomputable def cells259 : List Cell :=
  [{ i := 24, j := 24, k := 9, use := 0, tree := hex% "6a2e9d560000000000000002000000000000000100000000000000000000000000000000000000001d3cfc0a000000001633ced940000000000000002054800000000000000000000000000000000000000004511cd2400000000000000030000000000000000800000000000000000000000000000000000000013fca6ee20000000107587d7a000000000000000102a42" },
    { i := 55, j := 24, k := 9, use := 0, tree := hex% "22605f4b580000001bce75d638000000000000355c" },
    { i := 24, j := 24, k := 24, use := 0, tree := hex% "3000000006d205a070000000000000001000000000000000040ea" },
    { i := 55, j := 24, k := 24, use := 0, tree := hex% "58000000258c1b67180000001e819734380000000000000004" }]

/-- The group 259: the cover of a box by its cells. -/
theorem g259_ok : boxOk run { e1 := 2, c1 := 7, e2 := 2, c2 := 7, e3 := 1, c3 := 3 } (70136787617746) cells259 = true := by
  decide +kernel

end N14Cert.CapPrr

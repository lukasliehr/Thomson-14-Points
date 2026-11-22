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

/-- The cells of the group 9. -/
noncomputable def cells9 : List Cell :=
  [{ i := 0, j := 24, k := 0, use := 0, tree := 5 },
    { i := 0, j := 24, k := 1, use := 0, tree := 5 },
    { i := 0, j := 24, k := 2, use := 0, tree := 5 },
    { i := 0, j := 24, k := 3, use := 0, tree := 5 },
    { i := 0, j := 24, k := 4, use := 0, tree := 5 },
    { i := 0, j := 25, k := 0, use := 0, tree := 5 },
    { i := 0, j := 25, k := 1, use := 0, tree := 5 },
    { i := 0, j := 25, k := 2, use := 0, tree := 5 },
    { i := 0, j := 25, k := 3, use := 0, tree := 5 },
    { i := 0, j := 25, k := 4, use := 0, tree := 5 },
    { i := 0, j := 26, k := 1, use := 0, tree := 5 },
    { i := 0, j := 26, k := 2, use := 0, tree := 5 },
    { i := 0, j := 26, k := 3, use := 0, tree := 5 },
    { i := 0, j := 26, k := 4, use := 0, tree := 5 },
    { i := 0, j := 27, k := 2, use := 0, tree := 5 },
    { i := 0, j := 27, k := 3, use := 0, tree := 5 },
    { i := 0, j := 27, k := 4, use := 0, tree := 5 },
    { i := 0, j := 28, k := 3, use := 0, tree := 5 },
    { i := 0, j := 28, k := 4, use := 0, tree := 5 }]

/-- The group 9: the cover of a box by its cells. -/
theorem g9_ok : boxOk run { e1 := 1, c1 := 0, e2 := 2, c2 := 7, e3 := 1, c3 := 3 } (hex% "3ef9f6fb9f6fbb9f6fbbb9e") cells9 = true := by
  decide +kernel

/-- The cells of the group 10. -/
noncomputable def cells10 : List Cell :=
  [{ i := 1, j := 0, k := 0, use := 0, tree := hex% "d00000000b2046a1f00000000000000000000000002b1f5f300000000000000558d1" },
    { i := 1, j := 0, k := 1, use := 0, tree := hex% "a0574700000000031b48c5cc" },
    { i := 1, j := 0, k := 2, use := 0, tree := hex% "bff51578000000055b38e9ec" },
    { i := 1, j := 0, k := 3, use := 0, tree := hex% "c72f94200000000739070b9c" },
    { i := 1, j := 0, k := 4, use := 0, tree := 3 }]

/-- The group 10: the cover of a box by its cells. -/
theorem g10_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 3 } (4124398) cells10 = true := by
  decide +kernel

/-- The cells of the group 11. -/
noncomputable def cells11 : List Cell :=
  [{ i := 1, j := 1, k := 0, use := 0, tree := hex% "150ec68200000000000000000000000000677d4cc0000000000000001000000002a288cc6000000000000000000000000000000000000000000000000207400000002a358b4440000000000000000000000000000000000000000000000022203a800000002d0ebb058000000000000000000000000000000000000000000000002100000000b5e9232d00000000000000000000000006974271000000000000000081a" },
    { i := 1, j := 1, k := 1, use := 0, tree := 3 },
    { i := 1, j := 1, k := 2, use := 0, tree := 3 },
    { i := 1, j := 1, k := 3, use := 0, tree := 3 },
    { i := 1, j := 1, k := 4, use := 0, tree := 3 }]

/-- The group 11: the cover of a box by its cells. -/
theorem g11_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 1, c3 := 3 } (4124398) cells11 = true := by
  decide +kernel

/-- The cells of the group 12. -/
noncomputable def cells12 : List Cell :=
  [{ i := 1, j := 2, k := 0, use := 0, tree := hex% "175e52c7800000000000000000000000000000000000000000d5a9d8b0000000035051bd40000000000000000000000000000000000000000000000002000000005a0c1e2280000000000000000000000000000000000000000000000c4688" },
    { i := 1, j := 2, k := 1, use := 0, tree := 3 },
    { i := 1, j := 2, k := 2, use := 0, tree := 3 },
    { i := 1, j := 2, k := 3, use := 0, tree := 3 },
    { i := 1, j := 2, k := 4, use := 0, tree := 3 }]

/-- The group 12: the cover of a box by its cells. -/
theorem g12_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 2, e3 := 1, c3 := 3 } (4124398) cells12 = true := by
  decide +kernel

/-- The cells of the group 13. -/
noncomputable def cells13 : List Cell :=
  [{ i := 5, j := 9, k := 0, use := 0, tree := 5 },
    { i := 16, j := 9, k := 0, use := 0, tree := hex% "19e9af6a4000000000000000000000000000000000000000034df2ded000000002cc334a340000000000000000000000000000000000000000291573ea102a029" },
    { i := 17, j := 22, k := 0, use := 0, tree := hex% "7400000002a88273fc00000000000000000000000000000000000000001aadb72e014000000005672e361000000000000000000000000000000000000000001d5bf6bc2d00000000545effb9000000000000000000000000000000000000000002337dfc400000000a382874100000000000000000000000000000000000000000000000081a00000000a6c7ec7700000000000000000000000000000000000000000000000b8420e81400000002a52abd9c00000000000000000000000000000000000000001845ac960443a8000000000000000000000000000000000000000000000000000000002ec1695a2" },
    { i := 17, j := 23, k := 0, use := 0, tree := 347523420202 },
    { i := 1, j := 9, k := 1, use := 0, tree := 5 },
    { i := 1, j := 9, k := 2, use := 0, tree := 5 },
    { i := 1, j := 9, k := 3, use := 0, tree := 5 },
    { i := 1, j := 9, k := 4, use := 0, tree := 5 }]

/-- The group 13: the cover of a box by its cells. -/
theorem g13_ok : boxOk run { e1 := 1, c1 := 1, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (16893571886) cells13 = true := by
  decide +kernel

end N14Cert.Case0Close

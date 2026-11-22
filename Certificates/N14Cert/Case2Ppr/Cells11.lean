module

public import N14Cert.Case2Ppr.Run
public import N14.Box.MasterKernel
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.Case2Ppr

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The cells of the group 80. -/
noncomputable def cells80 : List Cell :=
  [{ i := 1, j := 7, k := 7, use := 0, tree := hex% "542a0000000000000000000000000000000000000000d555c0820000000000000000000000000000001b18000000000061b108000000000000000000000000698dc3c3000000000000000000000000000000008c20000000000000000000000000000000000000000698dc3c3000000000000000000000000000000008c0000000000000000000000000000000000000000335b64ec8000000000000000000000000000000046110a80000000000000000000000000000000000000000658c5c820000000000000000000000000000000e8c340000000000000000000000000000000000000000cefcadc60000000000000000000000000000001718000000000000000000000000000000000000000060e55a51000000000000000000000000000000228c22150983400000000000000000000000000000000000000000000000000000000000000030000000005b86331c40000000001c9cb2740000000000000000000000013f67c3e80000000000000000000000000000003e05400000000020a09218000000000000000000000000000000000000000000000030000000005b86331c0c2a190284400a8" },
    { i := 1, j := 7, k := 8, use := 0, tree := 5922524753100968 },
    { i := 1, j := 8, k := 2, use := 0, tree := hex% "5400000005e9c6a89000000000000000000000001a461dbbcc00000000000002e800000002880c0cc200a80a8140150542" }]

/-- The group 80: the cover of a box by its cells. -/
theorem g80_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 1, c3 := 2 } (16356) cells80 = true := by
  decide +kernel

/-- The cells of the group 81. -/
noncomputable def cells81 : List Cell :=
  [{ i := 0, j := 2, k := 9, use := 0, tree := 1443780268200 },
    { i := 0, j := 2, k := 24, use := 0, tree := hex% "2f0b5880c7b80000000000053da000000ed04f310cfc" },
    { i := 0, j := 2, k := 55, use := 0, tree := 5 },
    { i := 0, j := 2, k := 118, use := 0, tree := 5 },
    { i := 0, j := 2, k := 245, use := 0, tree := 5 },
    { i := 0, j := 2, k := 246, use := 0, tree := 5 }]

/-- The group 81: the cover of a box by its cells. -/
theorem g81_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 1, c3 := 3 } (4124398) cells81 = true := by
  decide +kernel

/-- The cells of the group 82. -/
noncomputable def cells82 : List Cell :=
  [{ i := 0, j := 9, k := 2, use := 0, tree := hex% "25cd5b3de28000000000000000000001520d8236e000000000000010268000000b52f81f37c" }]

/-- The group 82: the cover of a box by its cells. -/
theorem g82_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 3, e3 := 1, c3 := 2 } (61) cells82 = true := by
  decide +kernel

/-- The cells of the group 83. -/
noncomputable def cells83 : List Cell :=
  [{ i := 0, j := 9, k := 9, use := 0, tree := hex% "1e33800000000000000000000167adb5994b0000000000004c28000000000000144f4" },
    { i := 0, j := 9, k := 24, use := 0, tree := 5 },
    { i := 0, j := 9, k := 55, use := 0, tree := 5 },
    { i := 0, j := 9, k := 118, use := 0, tree := 5 },
    { i := 0, j := 9, k := 245, use := 0, tree := 5 },
    { i := 0, j := 9, k := 246, use := 0, tree := 5 }]

/-- The group 83: the cover of a box by its cells. -/
theorem g83_ok : boxOk run { e1 := 1, c1 := 0, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (4124398) cells83 = true := by
  decide +kernel

/-- The cells of the group 84. -/
noncomputable def cells84 : List Cell :=
  [{ i := 0, j := 24, k := 9, use := 0, tree := 5 },
    { i := 0, j := 24, k := 24, use := 0, tree := 5 },
    { i := 0, j := 24, k := 55, use := 0, tree := 5 },
    { i := 0, j := 24, k := 118, use := 0, tree := 5 },
    { i := 0, j := 24, k := 245, use := 0, tree := 5 },
    { i := 0, j := 24, k := 246, use := 0, tree := 5 },
    { i := 0, j := 55, k := 24, use := 0, tree := 5 },
    { i := 0, j := 55, k := 55, use := 0, tree := 5 },
    { i := 0, j := 55, k := 118, use := 0, tree := 5 },
    { i := 0, j := 55, k := 245, use := 0, tree := 5 },
    { i := 0, j := 55, k := 246, use := 0, tree := 5 },
    { i := 0, j := 118, k := 55, use := 0, tree := 5 },
    { i := 0, j := 118, k := 118, use := 0, tree := 5 },
    { i := 0, j := 118, k := 245, use := 0, tree := 5 },
    { i := 0, j := 118, k := 246, use := 0, tree := 5 },
    { i := 0, j := 245, k := 118, use := 0, tree := 5 },
    { i := 0, j := 245, k := 245, use := 0, tree := 5 },
    { i := 0, j := 245, k := 246, use := 0, tree := 5 },
    { i := 0, j := 246, k := 245, use := 0, tree := 5 },
    { i := 0, j := 246, k := 246, use := 0, tree := 5 }]

/-- The group 84: the cover of a box by its cells. -/
theorem g84_ok : boxOk run { e1 := 1, c1 := 0, e2 := 2, c2 := 7, e3 := 1, c3 := 3 } (hex% "3ef9f6fb9f6fbb9f6fbbb9f6") cells84 = true := by
  decide +kernel

end N14Cert.Case2Ppr

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

/-- The cells of the group 41. -/
noncomputable def cells41 : List Cell :=
  [{ i := 0, j := 25, k := 24, use := 0, tree := 5 },
    { i := 0, j := 26, k := 24, use := 0, tree := 5 },
    { i := 0, j := 27, k := 24, use := 0, tree := 5 },
    { i := 0, j := 28, k := 24, use := 0, tree := 5 },
    { i := 0, j := 25, k := 25, use := 0, tree := 5 },
    { i := 0, j := 25, k := 26, use := 0, tree := 5 },
    { i := 0, j := 25, k := 27, use := 0, tree := 5 },
    { i := 0, j := 25, k := 28, use := 0, tree := 5 },
    { i := 0, j := 26, k := 25, use := 0, tree := 5 },
    { i := 0, j := 27, k := 25, use := 0, tree := 5 },
    { i := 0, j := 28, k := 25, use := 0, tree := 5 },
    { i := 0, j := 26, k := 26, use := 0, tree := 5 },
    { i := 0, j := 26, k := 27, use := 0, tree := 5 },
    { i := 0, j := 26, k := 28, use := 0, tree := 5 },
    { i := 0, j := 27, k := 26, use := 0, tree := 5 },
    { i := 0, j := 28, k := 26, use := 0, tree := 5 },
    { i := 0, j := 27, k := 27, use := 0, tree := 5 },
    { i := 0, j := 27, k := 28, use := 0, tree := 5 },
    { i := 0, j := 28, k := 27, use := 0, tree := 5 },
    { i := 0, j := 28, k := 28, use := 0, tree := 5 }]

/-- The group 41: the cover of a box by its cells. -/
theorem g41_ok : boxOk run { e1 := 1, c1 := 0, e2 := 3, c2 := 15, e3 := 2, c3 := 7 } (hex% "3ef9f6fb9f76fbb9f776") cells41 = true := by
  decide +kernel

/-- The cells of the group 42. -/
noncomputable def cells42 : List Cell :=
  [{ i := 5, j := 4, k := 0, use := 0, tree := hex% "1b57d470000000000000002000000000000000000000000012e4c5dc" }]

/-- The group 42: the cover of a box by its cells. -/
theorem g42_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 0 } (1012) cells42 = true := by
  decide +kernel

/-- The cells of the group 43. -/
noncomputable def cells43 : List Cell :=
  [{ i := 5, j := 4, k := 1, use := 0, tree := hex% "1d0e8740000000000d7d4800000000000000000000000000000000000000000002b6956100000000000369a06000000000000000000000000000000000000000000000001110e8" }]

/-- The group 43: the cover of a box by its cells. -/
theorem g43_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 1 } (1012) cells43 = true := by
  decide +kernel

/-- The cells of the group 44. -/
noncomputable def cells44 : List Cell :=
  [{ i := 1, j := 0, k := 2, use := 0, tree := hex% "554374f800000000000000000000000000000000000000000000004c" }]

/-- The group 44: the cover of a box by its cells. -/
theorem g44_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 2 } (3) cells44 = true := by
  decide +kernel

/-- The cells of the group 45. -/
noncomputable def cells45 : List Cell :=
  [{ i := 1, j := 0, k := 9, use := 0, tree := hex% "743a1d0e8000000000034b3e0000000000000000000000000000000000000000000000004000000000010d60e00000000000000000000000000000000000000000000000088821d0000000000037cc9c00000000000000000000000000000000000000000000000311" },
    { i := 1, j := 0, k := 24, use := 0, tree := hex% "740000000001d8e398000000000000000000000000000000000000000002ae1caa1" },
    { i := 1, j := 0, k := 25, use := 0, tree := 1881 },
    { i := 1, j := 0, k := 26, use := 0, tree := hex% "24efbe2800000000000000000000000000000000000000011ef118dc" },
    { i := 1, j := 0, k := 27, use := 0, tree := 3 },
    { i := 1, j := 0, k := 28, use := 0, tree := 3 }]

/-- The group 45: the cover of a box by its cells. -/
theorem g45_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 3 } (4124398) cells45 = true := by
  decide +kernel

/-- The cells of the group 46. -/
noncomputable def cells46 : List Cell :=
  [{ i := 5, j := 5, k := 3, use := 0, tree := hex% "36db6d104000000000000000000000000000000000000000000000000000000000008f9de4600000000000000000000000000000000000000000000000000000000000665d918212" },
    { i := 14, j := 14, k := 4, use := 0, tree := hex% "667f70000000000001c8dc0000000000000000000000000000000000000000000d03b60000000000000000000000000000000000000000000000000000000000008437988000000000000803c0000000000000000000000000000000000000000000d701e00000000000000000000000000000000000000000000000000000000000443a2c000000000000024d00000000000000000000000000000000000000000000c3edf0000000000000000000000000000000000000000000000000000000000018d10e000000000000000000000000000000000000000000000000000000000006575242100000000000000000000000000000000000000000000000000000000000197fe42000000000000000000000000000000000000000000000000000000000003dadd02" },
    { i := 14, j := 15, k := 4, use := 0, tree := 222050586 },
    { i := 15, j := 5, k := 4, use := 0, tree := hex% "f8da0000000000000000000000000000000000000000000d3c390000000000000000000000000000000000000000000000000000000000017387e16ca" }]

/-- The group 46: the cover of a box by its cells. -/
theorem g46_ok : boxOk run { e1 := 2, c1 := 2, e2 := 2, c2 := 2, e3 := 1, c3 := 0 } (16206) cells46 = true := by
  decide +kernel

/-- The cells of the group 47. -/
noncomputable def cells47 : List Cell :=
  [{ i := 14, j := 6, k := 3, use := 0, tree := 218 },
    { i := 15, j := 16, k := 3, use := 0, tree := 14844118802642 },
    { i := 15, j := 17, k := 10, use := 0, tree := hex% "d80000000000000000000000000000000000000000000000000000000000f2c85c00000000000000000000000000000000000000000000000000000000000111f5b00000000000000000000000000000000000000000000000000000000000bf252e34081506d84d9682" },
    { i := 15, j := 17, k := 11, use := 0, tree := 13850 },
    { i := 5, j := 6, k := 4, use := 0, tree := 235554846288 }]

/-- The group 47: the cover of a box by its cells. -/
theorem g47_ok : boxOk run { e1 := 2, c1 := 2, e2 := 2, c2 := 3, e3 := 1, c3 := 0 } (260978) cells47 = true := by
  decide +kernel

end N14Cert.Case2Prr

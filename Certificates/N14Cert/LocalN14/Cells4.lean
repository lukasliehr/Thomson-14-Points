module

public import N14Cert.LocalN14.Run
public import N14.Box.MasterKernel
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.LocalN14

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The cells of the group 25. -/
noncomputable def cells25 : List Cell :=
  [{ i := 19, j := 23, k := 24, use := 3, tree := hex% "36db21a21b6d90996136d161b0d96da21361a2db09b65b21108b6c34c86cb0da65b6884db4cb08b65b21b2c26d90da6d16da21109b4da2da6436c86c2658442" },
    { i := 19, j := 23, k := 25, use := 3, tree := hex% "db4da2db44345b2da6434da6586cb64221b4cb6990db45b4da2136996c34da21b6422da6d16c869909b6da2c265b2db44369b45b4c84db6422116db69909b68b69b0d10db09b0d16c34c845b6db08b0884c86d90d32c2" }]

/-- The group 25: the cover of a box by its cells. -/
theorem g25_ok : boxOk run { e1 := 9, c1 := 52, e2 := 9, c2 := 56, e3 := 8, c3 := 410 } (62) cells25 = true := by
  decide +kernel

/-- The cells of the group 26. -/
noncomputable def cells26 : List Cell :=
  [{ i := 19, j := 24, k := 24, use := 3, tree := hex% "7ee5a700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011869b64345b2c34da21b68b6990db61a21361a2d961a642" },
    { i := 19, j := 24, k := 25, use := 3, tree := 3 }]

/-- The group 26: the cover of a box by its cells. -/
theorem g26_ok : boxOk run { e1 := 9, c1 := 52, e2 := 9, c2 := 57, e3 := 8, c3 := 410 } (62) cells26 = true := by
  decide +kernel

/-- The cells of the group 27. -/
noncomputable def cells27 : List Cell :=
  [{ i := 20, j := 23, k := 24, use := 3, tree := hex% "365869b2d90d845b2d90d84da21b4d868b61a6c34436d96c86db4422136c868b6d161a642" },
    { i := 20, j := 23, k := 25, use := 3, tree := 3 },
    { i := 20, j := 24, k := 15, use := 3, tree := 3679236250 }]

/-- The group 27: the cover of a box by its cells. -/
theorem g27_ok : boxOk run { e1 := 9, c1 := 53, e2 := 8, c2 := 28, e3 := 8, c3 := 410 } (1017) cells27 = true := by
  decide +kernel

/-- The cells of the group 28. -/
noncomputable def cells28 : List Cell :=
  [{ i := 12, j := 14, k := 16, use := 3, tree := 3 }]

/-- The group 28: the cover of a box by its cells. -/
theorem g28_ok : boxOk run { e1 := 8, c1 := 26, e2 := 8, c2 := 28, e3 := 8, c3 := 411 } (3) cells28 = true := by
  decide +kernel

/-- The cells of the group 29. -/
noncomputable def cells29 : List Cell :=
  [{ i := 12, j := 15, k := 10, use := 3, tree := 965055668334746 }]

/-- The group 29: the cover of a box by its cells. -/
theorem g29_ok : boxOk run { e1 := 8, c1 := 26, e2 := 8, c2 := 29, e3 := 7, c3 := 205 } (3) cells29 = true := by
  decide +kernel

/-- The cells of the group 30. -/
noncomputable def cells30 : List Cell :=
  [{ i := 13, j := 9, k := 10, use := 3, tree := 3952873512761042522 }]

/-- The group 30: the cover of a box by its cells. -/
theorem g30_ok : boxOk run { e1 := 8, c1 := 27, e2 := 7, c2 := 14, e3 := 7, c3 := 205 } (3) cells30 = true := by
  decide +kernel

/-- The cells of the group 31. -/
noncomputable def cells31 : List Cell :=
  [{ i := 5, j := 6, k := 7, use := 3, tree := hex% "9c00000000032e90f4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e8ca800000000007ae79c" }]

/-- The group 31: the cover of a box by its cells. -/
theorem g31_ok : boxOk run { e1 := 6, c1 := 6, e2 := 6, c2 := 7, e3 := 6, c3 := 103 } (3) cells31 = true := by
  decide +kernel

/-- The cells of the group 32. -/
noncomputable def cells32 : List Cell :=
  [{ i := 6, j := 4, k := 4, use := 3, tree := hex% "3e5a00000000000000240000000000354cc8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000107a3d0000000000002de80000000000000000000000000002bb5f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000e400000000000000000000000000064a6800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011020000000000001164000000000000005c00000000003a4716000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000110540f4a6db6da05a04000000000000044400000000123df570000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000b50800000000247bead8000000000015b61800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000046c360b40a0a812944000000000000071000000000000000f80000000001e666f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a2" }]

/-- The group 32: the cover of a box by its cells. -/
theorem g32_ok : boxOk run { e1 := 6, c1 := 7, e2 := 5, c2 := 3, e3 := 5, c3 := 51 } (3) cells32 = true := by
  decide +kernel

end N14Cert.LocalN14

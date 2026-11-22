module

public import N14Cert.Case1.Run
public import N14.Box.MasterKernel
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.Case1

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The cells of the group 47. -/
noncomputable def cells47 : List Cell :=
  [{ i := 0, j := 0, k := 55, use := 0, tree := hex% "db00000000000000000000000000000000000000000000000000000003ab25451884b0000000000000000000000000000000000000000000000000000000691525536800000000000000000000000000000000000000000000042a000000344c4ace9100000000000000000000000000000000000000000000000000000000c89cd4312c0284406152c8" }]

/-- The group 47: the cover of a box by its cells. -/
theorem g47_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 4, c3 := 30 } (3) cells47 = true := by
  decide +kernel

/-- The cells of the group 48. -/
noncomputable def cells48 : List Cell :=
  [{ i := 0, j := 0, k := 118, use := 0, tree := hex% "c0000000000000000000000074c6a9bfc0000000000000000000000408a9d0cb616580000000000000000000000000000000000000000000000000000007c43d43e442000000000000000000000000000000bc00000000000001d6000000273107803700a406152c8" }]

/-- The group 48: the cover of a box by its cells. -/
theorem g48_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 5, c3 := 62 } (3) cells48 = true := by
  decide +kernel

/-- The cells of the group 49. -/
noncomputable def cells49 : List Cell :=
  [{ i := 0, j := 0, k := 245, use := 0, tree := hex% "30000000000000000000000026c43f9f300000000000000000000002bcbc5f71a8590000000000000000000000000000017300000000000000000000001b5c3bb63880000000000000000000000000000019000000000000003e8000000605153b0ff00a406152c8" },
    { i := 0, j := 0, k := 246, use := 0, tree := hex% "73180000000000000000000000c5ae17480719000000000000000000000000000002a200000000000000000000003391e960ed80000000000000000000000000000031000000000000007a8000000e161aef08500a406052c8" }]

/-- The group 49: the cover of a box by its cells. -/
theorem g49_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 5, c3 := 63 } (62) cells49 = true := by
  decide +kernel

/-- The cells of the group 50. -/
noncomputable def cells50 : List Cell :=
  [{ i := 0, j := 1, k := 0, use := 0, tree := hex% "44e89048c78ce000000000000000000000000877d211a000275f9b03aff1d0000168767efdac34000000000000000000000000000000000000f04efd961b2a0" }]

/-- The group 50: the cover of a box by its cells. -/
theorem g50_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 1, e3 := 1, c3 := 0 } (3) cells50 = true := by
  decide +kernel

/-- The cells of the group 51. -/
noncomputable def cells51 : List Cell :=
  [{ i := 10, j := 5, k := 5, use := 0, tree := hex% "11310000000000000000000000000000abeb800001599430a4cd4" }]

/-- The group 51: the cover of a box by its cells. -/
theorem g51_ok : boxOk run { e1 := 3, c1 := 0, e2 := 2, c2 := 2, e3 := 2, c3 := 2 } (3) cells51 = true := by
  decide +kernel

/-- The cells of the group 52. -/
noncomputable def cells52 : List Cell :=
  [{ i := 11, j := 14, k := 14, use := 0, tree := 5 }]

/-- The group 52: the cover of a box by its cells. -/
theorem g52_ok : boxOk run { e1 := 3, c1 := 1, e2 := 3, c2 := 4, e3 := 3, c3 := 4 } (3) cells52 = true := by
  decide +kernel

/-- The cells of the group 53. -/
noncomputable def cells53 : List Cell :=
  [{ i := 27, j := 14, k := 15, use := 0, tree := 5 }]

/-- The group 53: the cover of a box by its cells. -/
theorem g53_ok : boxOk run { e1 := 4, c1 := 2, e2 := 3, c2 := 4, e3 := 3, c3 := 5 } (3) cells53 = true := by
  decide +kernel

/-- The cells of the group 54. -/
noncomputable def cells54 : List Cell :=
  [{ i := 28, j := 33, k := 15, use := 0, tree := hex% "140a0502800000000000000000000000000000000000000000000000000000000177fa6d4210" }]

/-- The group 54: the cover of a box by its cells. -/
theorem g54_ok : boxOk run { e1 := 4, c1 := 3, e2 := 4, c2 := 8, e3 := 3, c3 := 5 } (3) cells54 = true := by
  decide +kernel

/-- The cells of the group 55. -/
noncomputable def cells55 : List Cell :=
  [{ i := 28, j := 34, k := 35, use := 0, tree := hex% "140a05028140000000000000000000000000000000000000000000000000000000000c4542e014802800000000000000000000000000000000000000000000000000000000018add3c000000000000000000000000000000000000000000000000000000000016c5418500000000000000000000000000000000000000000000000000000000000bb002c0000000000000000000000000000000000000000000000000000000000086192841088" }]

/-- The group 55: the cover of a box by its cells. -/
theorem g55_ok : boxOk run { e1 := 4, c1 := 3, e2 := 4, c2 := 9, e3 := 4, c3 := 10 } (3) cells55 = true := by
  decide +kernel

end N14Cert.Case1

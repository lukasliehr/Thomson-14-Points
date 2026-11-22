module

public import N14Cert.Case0Pos.Run
public import N14.Box.MasterKernel
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.Case0Pos

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The cells of the group 26. -/
noncomputable def cells26 : List Cell :=
  [{ i := 0, j := 9, k := 9, use := 0, tree := hex% "a800000000000000000000000056b5e6cc" },
    { i := 0, j := 9, k := 24, use := 0, tree := 5 },
    { i := 0, j := 9, k := 25, use := 0, tree := 5 },
    { i := 0, j := 9, k := 26, use := 0, tree := 5 },
    { i := 0, j := 9, k := 27, use := 0, tree := 5 },
    { i := 0, j := 9, k := 28, use := 0, tree := 5 }]

/-- The group 26: the cover of a box by its cells. -/
theorem g26_ok : boxOk run { e1 := 1, c1 := 0, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (4124398) cells26 = true := by
  decide +kernel

/-- The cells of the group 27. -/
noncomputable def cells27 : List Cell :=
  [{ i := 0, j := 24, k := 9, use := 0, tree := 5 },
    { i := 0, j := 24, k := 24, use := 0, tree := 5 },
    { i := 0, j := 24, k := 25, use := 0, tree := 5 },
    { i := 0, j := 24, k := 26, use := 0, tree := 5 },
    { i := 0, j := 24, k := 27, use := 0, tree := 5 },
    { i := 0, j := 24, k := 28, use := 0, tree := 5 },
    { i := 0, j := 25, k := 24, use := 0, tree := 5 },
    { i := 0, j := 25, k := 25, use := 0, tree := 5 },
    { i := 0, j := 25, k := 26, use := 0, tree := 5 },
    { i := 0, j := 25, k := 27, use := 0, tree := 5 },
    { i := 0, j := 25, k := 28, use := 0, tree := 5 },
    { i := 0, j := 26, k := 25, use := 0, tree := 5 },
    { i := 0, j := 26, k := 26, use := 0, tree := 5 },
    { i := 0, j := 26, k := 27, use := 0, tree := 5 },
    { i := 0, j := 26, k := 28, use := 0, tree := 5 },
    { i := 0, j := 27, k := 26, use := 0, tree := 5 },
    { i := 0, j := 27, k := 27, use := 0, tree := 5 },
    { i := 0, j := 27, k := 28, use := 0, tree := 5 },
    { i := 0, j := 28, k := 27, use := 0, tree := 5 },
    { i := 0, j := 28, k := 28, use := 0, tree := 5 }]

/-- The group 27: the cover of a box by its cells. -/
theorem g27_ok : boxOk run { e1 := 1, c1 := 0, e2 := 2, c2 := 7, e3 := 1, c3 := 3 } (hex% "3ef9f6fb9f6fbb9f6fbbb9f6") cells27 = true := by
  decide +kernel

/-- The cells of the group 28. -/
noncomputable def cells28 : List Cell :=
  [{ i := 1, j := 0, k := 0, use := 0, tree := hex% "98b0c1480000000337ab3b18000000011d567c24" }]

/-- The group 28: the cover of a box by its cells. -/
theorem g28_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 0 } (3) cells28 = true := by
  decide +kernel

/-- The cells of the group 29. -/
noncomputable def cells29 : List Cell :=
  [{ i := 1, j := 0, k := 1, use := 0, tree := hex% "d06b60d6c1a00000000000000000000000006b8d97200000000032decdd0a0502000000000000000000000000004677da000000000000000110341" }]

/-- The group 29: the cover of a box by its cells. -/
theorem g29_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 1 } (3) cells29 = true := by
  decide +kernel

/-- The cells of the group 30. -/
noncomputable def cells30 : List Cell :=
  [{ i := 1, j := 0, k := 2, use := 0, tree := hex% "47a67f00000000000000014068" }]

/-- The group 30: the cover of a box by its cells. -/
theorem g30_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 2 } (3) cells30 = true := by
  decide +kernel

/-- The cells of the group 31. -/
noncomputable def cells31 : List Cell :=
  [{ i := 1, j := 0, k := 9, use := 0, tree := hex% "3400000000000000000000000001cb1d6000000000000000061" },
    { i := 1, j := 0, k := 24, use := 0, tree := 857 },
    { i := 1, j := 0, k := 25, use := 0, tree := hex% "a05746f8000000031b48c5cc" },
    { i := 1, j := 0, k := 26, use := 0, tree := hex% "bff51500000000055b38e2f4" },
    { i := 1, j := 0, k := 27, use := 0, tree := hex% "c72f9590000000073907355c" },
    { i := 1, j := 0, k := 28, use := 0, tree := 3 }]

/-- The group 31: the cover of a box by its cells. -/
theorem g31_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 3 } (4124398) cells31 = true := by
  decide +kernel

/-- The cells of the group 32. -/
noncomputable def cells32 : List Cell :=
  [{ i := 1, j := 1, k := 0, use := 0, tree := hex% "542ad855800000000260af7400000000000000000000000000d4ecd64088415200000000011be37000000000005e2146000000000000000102" }]

/-- The group 32: the cover of a box by its cells. -/
theorem g32_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 1, c3 := 0 } (3) cells32 = true := by
  decide +kernel

/-- The cells of the group 33. -/
noncomputable def cells33 : List Cell :=
  [{ i := 1, j := 1, k := 1, use := 0, tree := hex% "c00000000003f86a8000000000000000000000000000000021000000000000000000000000001b7aac00000000000000008c8" }]

/-- The group 33: the cover of a box by its cells. -/
theorem g33_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 1, c3 := 1 } (3) cells33 = true := by
  decide +kernel

/-- The cells of the group 34. -/
noncomputable def cells34 : List Cell :=
  [{ i := 1, j := 1, k := 2, use := 0, tree := 233411752146 }]

/-- The group 34: the cover of a box by its cells. -/
theorem g34_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 1, c3 := 2 } (3) cells34 = true := by
  decide +kernel

/-- The cells of the group 35. -/
noncomputable def cells35 : List Cell :=
  [{ i := 1, j := 1, k := 9, use := 0, tree := 13978 },
    { i := 1, j := 1, k := 24, use := 0, tree := 3 },
    { i := 1, j := 1, k := 25, use := 0, tree := 3 },
    { i := 1, j := 1, k := 26, use := 0, tree := 3 },
    { i := 1, j := 1, k := 27, use := 0, tree := 3 },
    { i := 1, j := 1, k := 28, use := 0, tree := 3 }]

/-- The group 35: the cover of a box by its cells. -/
theorem g35_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 1, c3 := 3 } (4124398) cells35 = true := by
  decide +kernel

/-- The cells of the group 36. -/
noncomputable def cells36 : List Cell :=
  [{ i := 1, j := 2, k := 1, use := 0, tree := hex% "930533000000000000000000000000000000004" }]

/-- The group 36: the cover of a box by its cells. -/
theorem g36_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 2, e3 := 1, c3 := 1 } (3) cells36 = true := by
  decide +kernel

/-- The cells of the group 37. -/
noncomputable def cells37 : List Cell :=
  [{ i := 1, j := 2, k := 2, use := 0, tree := hex% "db4800000000053b6e080000000000000000000000000000000236d1611" }]

/-- The group 37: the cover of a box by its cells. -/
theorem g37_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 2, e3 := 1, c3 := 2 } (3) cells37 = true := by
  decide +kernel

end N14Cert.Case0Pos

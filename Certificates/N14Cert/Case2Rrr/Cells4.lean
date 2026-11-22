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

/-- The cells of the group 33. -/
noncomputable def cells33 : List Cell :=
  [{ i := 0, j := 9, k := 9, use := 0, tree := 3 },
    { i := 0, j := 9, k := 24, use := 0, tree := 5 },
    { i := 0, j := 9, k := 25, use := 0, tree := 5 },
    { i := 0, j := 9, k := 26, use := 0, tree := 5 },
    { i := 0, j := 9, k := 27, use := 0, tree := 5 },
    { i := 0, j := 9, k := 28, use := 0, tree := 5 }]

/-- The group 33: the cover of a box by its cells. -/
theorem g33_ok : boxOk run { e1 := 1, c1 := 0, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (4124398) cells33 = true := by
  decide +kernel

/-- The cells of the group 34. -/
noncomputable def cells34 : List Cell :=
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

/-- The group 34: the cover of a box by its cells. -/
theorem g34_ok : boxOk run { e1 := 1, c1 := 0, e2 := 2, c2 := 7, e3 := 1, c3 := 3 } (hex% "3ef9f6fb9f6fbb9f6fbbb9f6") cells34 = true := by
  decide +kernel

/-- The cells of the group 35. -/
noncomputable def cells35 : List Cell :=
  [{ i := 1, j := 0, k := 0, use := 0, tree := hex% "d0000000000c95dfd800000000000000000000000007cbafb4" }]

/-- The group 35: the cover of a box by its cells. -/
theorem g35_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 0 } (3) cells35 = true := by
  decide +kernel

/-- The cells of the group 36. -/
noncomputable def cells36 : List Cell :=
  [{ i := 1, j := 0, k := 1, use := 0, tree := hex% "542a15642aca04000000000000000000000000003cd6500000000000000000000000000000003e20a8" }]

/-- The group 36: the cover of a box by its cells. -/
theorem g36_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 1 } (3) cells36 = true := by
  decide +kernel

/-- The cells of the group 37. -/
noncomputable def cells37 : List Cell :=
  [{ i := 1, j := 0, k := 2, use := 0, tree := hex% "fbed5800000000000000000000000000000004" }]

/-- The group 37: the cover of a box by its cells. -/
theorem g37_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 2 } (3) cells37 = true := by
  decide +kernel

/-- The cells of the group 38. -/
noncomputable def cells38 : List Cell :=
  [{ i := 1, j := 0, k := 9, use := 0, tree := hex% "d3009000000000000000000000000000075a6c" },
    { i := 1, j := 0, k := 24, use := 0, tree := 3 },
    { i := 1, j := 0, k := 25, use := 0, tree := 3 },
    { i := 1, j := 0, k := 26, use := 0, tree := 3 },
    { i := 1, j := 0, k := 27, use := 0, tree := 3 },
    { i := 1, j := 0, k := 28, use := 0, tree := 3 }]

/-- The group 38: the cover of a box by its cells. -/
theorem g38_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 3 } (4124398) cells38 = true := by
  decide +kernel

/-- The cells of the group 39. -/
noncomputable def cells39 : List Cell :=
  [{ i := 1, j := 1, k := 0, use := 0, tree := hex% "1aa82820000000000cc153a0000000000000000000000000085c50100000000000814c3800000000004433c0000000000000000000000000001f042a0" }]

/-- The group 39: the cover of a box by its cells. -/
theorem g39_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 1, c3 := 0 } (3) cells39 = true := by
  decide +kernel

/-- The cells of the group 40. -/
noncomputable def cells40 : List Cell :=
  [{ i := 1, j := 1, k := 1, use := 0, tree := hex% "369b4400000000000000000000000000097dd40000000000000000000000000000000236d9088" }]

/-- The group 40: the cover of a box by its cells. -/
theorem g40_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 1, c3 := 1 } (3) cells40 = true := by
  decide +kernel

/-- The cells of the group 41. -/
noncomputable def cells41 : List Cell :=
  [{ i := 1, j := 1, k := 2, use := 0, tree := hex% "36c86d3688000000000000000000000000000bea5000000000000000000000000000000004642" }]

/-- The group 41: the cover of a box by its cells. -/
theorem g41_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 1, c3 := 2 } (3) cells41 = true := by
  decide +kernel

/-- The cells of the group 42. -/
noncomputable def cells42 : List Cell :=
  [{ i := 1, j := 1, k := 9, use := 0, tree := 60914688391483546 },
    { i := 1, j := 1, k := 24, use := 0, tree := 3 },
    { i := 1, j := 1, k := 25, use := 0, tree := 3 },
    { i := 1, j := 1, k := 26, use := 0, tree := 3 },
    { i := 1, j := 1, k := 27, use := 0, tree := 3 },
    { i := 1, j := 1, k := 28, use := 0, tree := 3 }]

/-- The group 42: the cover of a box by its cells. -/
theorem g42_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 1, c3 := 3 } (4124398) cells42 = true := by
  decide +kernel

/-- The cells of the group 43. -/
noncomputable def cells43 : List Cell :=
  [{ i := 1, j := 2, k := 1, use := 0, tree := hex% "c00000000001115cc00000000000000000000000000000000000000000000000200e9" }]

/-- The group 43: the cover of a box by its cells. -/
theorem g43_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 2, e3 := 1, c3 := 1 } (3) cells43 = true := by
  decide +kernel

/-- The cells of the group 44. -/
noncomputable def cells44 : List Cell :=
  [{ i := 1, j := 2, k := 2, use := 0, tree := hex% "d861b0c26c30d8611" }]

/-- The group 44: the cover of a box by its cells. -/
theorem g44_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 2, e3 := 1, c3 := 2 } (3) cells44 = true := by
  decide +kernel

/-- The cells of the group 45. -/
noncomputable def cells45 : List Cell :=
  [{ i := 1, j := 2, k := 9, use := 0, tree := 960641668850384 },
    { i := 1, j := 2, k := 24, use := 0, tree := 3 },
    { i := 1, j := 2, k := 25, use := 0, tree := 3 },
    { i := 1, j := 2, k := 26, use := 0, tree := 3 },
    { i := 1, j := 2, k := 27, use := 0, tree := 3 },
    { i := 1, j := 2, k := 28, use := 0, tree := 3 }]

/-- The group 45: the cover of a box by its cells. -/
theorem g45_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 2, e3 := 1, c3 := 3 } (4124398) cells45 = true := by
  decide +kernel

/-- The cells of the group 46. -/
noncomputable def cells46 : List Cell :=
  [{ i := 1, j := 9, k := 2, use := 0, tree := hex% "1d00000000000424db0000000000000000000000000000000000000000000000048800000000001391ac0000000000000000000000000000000000000000000000060" }]

/-- The group 46: the cover of a box by its cells. -/
theorem g46_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 3, e3 := 1, c3 := 2 } (61) cells46 = true := by
  decide +kernel

end N14Cert.Case2Rrr

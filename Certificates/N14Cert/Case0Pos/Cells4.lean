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

/-- The cells of the group 38. -/
noncomputable def cells38 : List Cell :=
  [{ i := 1, j := 2, k := 9, use := 0, tree := 3647582928 },
    { i := 1, j := 2, k := 24, use := 0, tree := 3 },
    { i := 1, j := 2, k := 25, use := 0, tree := 3 },
    { i := 1, j := 2, k := 26, use := 0, tree := 3 },
    { i := 1, j := 2, k := 27, use := 0, tree := 3 },
    { i := 1, j := 2, k := 28, use := 0, tree := 3 }]

/-- The group 38: the cover of a box by its cells. -/
theorem g38_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 2, e3 := 1, c3 := 3 } (4124398) cells38 = true := by
  decide +kernel

/-- The cells of the group 39. -/
noncomputable def cells39 : List Cell :=
  [{ i := 1, j := 9, k := 2, use := 0, tree := hex% "27106cc0000000000000000000000000000005f00000000002b82f14000000000000000000000000000000060" }]

/-- The group 39: the cover of a box by its cells. -/
theorem g39_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 3, e3 := 1, c3 := 2 } (61) cells39 = true := by
  decide +kernel

/-- The cells of the group 40. -/
noncomputable def cells40 : List Cell :=
  [{ i := 1, j := 9, k := 9, use := 0, tree := hex% "d81516c000000000000000400000000000000000000000011414256000000000000001200000000000000000000000009cfb13e4288" },
    { i := 1, j := 9, k := 24, use := 0, tree := hex% "56000000000000000000000000000000000000000086e06e8508" },
    { i := 1, j := 9, k := 25, use := 0, tree := 5 },
    { i := 1, j := 9, k := 26, use := 0, tree := 5 },
    { i := 1, j := 9, k := 27, use := 0, tree := 5 },
    { i := 1, j := 9, k := 28, use := 0, tree := 5 }]

/-- The group 40: the cover of a box by its cells. -/
theorem g40_ok : boxOk run { e1 := 1, c1 := 1, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (4124398) cells40 = true := by
  decide +kernel

/-- The cells of the group 41. -/
noncomputable def cells41 : List Cell :=
  [{ i := 1, j := 24, k := 9, use := 0, tree := hex% "7f752997000000000000000000000000295ac3b24" }]

/-- The group 41: the cover of a box by its cells. -/
theorem g41_ok : boxOk run { e1 := 1, c1 := 1, e2 := 2, c2 := 7, e3 := 2, c3 := 6 } (61) cells41 = true := by
  decide +kernel

/-- The cells of the group 42. -/
noncomputable def cells42 : List Cell :=
  [{ i := 1, j := 24, k := 24, use := 0, tree := 5 },
    { i := 1, j := 24, k := 25, use := 0, tree := 5 },
    { i := 1, j := 24, k := 26, use := 0, tree := 5 },
    { i := 1, j := 24, k := 27, use := 0, tree := 5 },
    { i := 1, j := 24, k := 28, use := 0, tree := 5 },
    { i := 1, j := 25, k := 24, use := 0, tree := 5 },
    { i := 1, j := 25, k := 25, use := 0, tree := 5 },
    { i := 1, j := 25, k := 26, use := 0, tree := 5 },
    { i := 1, j := 25, k := 27, use := 0, tree := 5 },
    { i := 1, j := 25, k := 28, use := 0, tree := 5 },
    { i := 1, j := 26, k := 25, use := 0, tree := 5 },
    { i := 1, j := 26, k := 26, use := 0, tree := 5 },
    { i := 1, j := 26, k := 27, use := 0, tree := 5 },
    { i := 1, j := 26, k := 28, use := 0, tree := 5 },
    { i := 1, j := 27, k := 26, use := 0, tree := 5 },
    { i := 1, j := 27, k := 27, use := 0, tree := 5 },
    { i := 1, j := 27, k := 28, use := 0, tree := 5 },
    { i := 1, j := 28, k := 27, use := 0, tree := 5 },
    { i := 1, j := 28, k := 28, use := 0, tree := 5 }]

/-- The group 42: the cover of a box by its cells. -/
theorem g42_ok : boxOk run { e1 := 1, c1 := 1, e2 := 2, c2 := 7, e3 := 2, c3 := 7 } (hex% "3ef9f6fb9f6fbb9f6fbbb9") cells42 = true := by
  decide +kernel

/-- The cells of the group 43. -/
noncomputable def cells43 : List Cell :=
  [{ i := 2, j := 1, k := 0, use := 0, tree := hex% "87217a00000000005224cd00000000004ba8fc4" }]

/-- The group 43: the cover of a box by its cells. -/
theorem g43_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 0 } (3) cells43 = true := by
  decide +kernel

/-- The cells of the group 44. -/
noncomputable def cells44 : List Cell :=
  [{ i := 2, j := 1, k := 1, use := 0, tree := hex% "2eb802000000000093053300000000000000004" }]

/-- The group 44: the cover of a box by its cells. -/
theorem g44_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 1 } (3) cells44 = true := by
  decide +kernel

/-- The cells of the group 45. -/
noncomputable def cells45 : List Cell :=
  [{ i := 2, j := 1, k := 2, use := 0, tree := hex% "c000000000000000000000000005e564400000000000000022068" }]

/-- The group 45: the cover of a box by its cells. -/
theorem g45_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 2 } (3) cells45 = true := by
  decide +kernel

/-- The cells of the group 46. -/
noncomputable def cells46 : List Cell :=
  [{ i := 2, j := 1, k := 9, use := 0, tree := hex% "25339780000000000000024" },
    { i := 2, j := 1, k := 24, use := 0, tree := 3 },
    { i := 2, j := 1, k := 25, use := 0, tree := 3 },
    { i := 2, j := 1, k := 26, use := 0, tree := 3 },
    { i := 2, j := 1, k := 27, use := 0, tree := 3 },
    { i := 2, j := 1, k := 28, use := 0, tree := 3 }]

/-- The group 46: the cover of a box by its cells. -/
theorem g46_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 3 } (4124398) cells46 = true := by
  decide +kernel

/-- The cells of the group 47. -/
noncomputable def cells47 : List Cell :=
  [{ i := 2, j := 2, k := 1, use := 0, tree := hex% "24e52b0000000000000000000000000000000010000000000183dab400000000010d11c000000000000000020" }]

/-- The group 47: the cover of a box by its cells. -/
theorem g47_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 1 } (3) cells47 = true := by
  decide +kernel

/-- The cells of the group 48. -/
noncomputable def cells48 : List Cell :=
  [{ i := 2, j := 2, k := 2, use := 0, tree := hex% "36d20000000000ca8f63000000000000000000000000000000008d100000000000000000000000000d843fb00000000000000008c8" }]

/-- The group 48: the cover of a box by its cells. -/
theorem g48_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 2 } (3) cells48 = true := by
  decide +kernel

/-- The cells of the group 49. -/
noncomputable def cells49 : List Cell :=
  [{ i := 2, j := 2, k := 9, use := 0, tree := 218 },
    { i := 2, j := 2, k := 24, use := 0, tree := 3 },
    { i := 2, j := 2, k := 25, use := 0, tree := 3 },
    { i := 2, j := 2, k := 26, use := 0, tree := 3 },
    { i := 2, j := 2, k := 27, use := 0, tree := 3 },
    { i := 2, j := 2, k := 28, use := 0, tree := 3 }]

/-- The group 49: the cover of a box by its cells. -/
theorem g49_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 3 } (4124398) cells49 = true := by
  decide +kernel

/-- The cells of the group 50. -/
noncomputable def cells50 : List Cell :=
  [{ i := 2, j := 9, k := 2, use := 0, tree := hex% "7a689f800000000000000000000000000000004" }]

/-- The group 50: the cover of a box by its cells. -/
theorem g50_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 3, e3 := 1, c3 := 2 } (61) cells50 = true := by
  decide +kernel

/-- The cells of the group 51. -/
noncomputable def cells51 : List Cell :=
  [{ i := 2, j := 9, k := 9, use := 0, tree := 3664098504 },
    { i := 2, j := 9, k := 24, use := 0, tree := 3 },
    { i := 2, j := 9, k := 25, use := 0, tree := 3 },
    { i := 2, j := 9, k := 26, use := 0, tree := 3 },
    { i := 2, j := 9, k := 27, use := 0, tree := 3 },
    { i := 2, j := 9, k := 28, use := 0, tree := 3 }]

/-- The group 51: the cover of a box by its cells. -/
theorem g51_ok : boxOk run { e1 := 1, c1 := 2, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (4124398) cells51 = true := by
  decide +kernel

end N14Cert.Case0Pos

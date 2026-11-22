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

/-- The cells of the group 47. -/
noncomputable def cells47 : List Cell :=
  [{ i := 5, j := 9, k := 9, use := 0, tree := 3681060505 },
    { i := 16, j := 9, k := 9, use := 0, tree := 894673 },
    { i := 17, j := 9, k := 9, use := 0, tree := 894673 },
    { i := 1, j := 9, k := 24, use := 0, tree := 3 },
    { i := 1, j := 9, k := 25, use := 0, tree := 5 },
    { i := 1, j := 9, k := 26, use := 0, tree := 5 },
    { i := 1, j := 9, k := 27, use := 0, tree := 5 },
    { i := 1, j := 9, k := 28, use := 0, tree := 5 }]

/-- The group 47: the cover of a box by its cells. -/
theorem g47_ok : boxOk run { e1 := 1, c1 := 1, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (1055846194) cells47 = true := by
  decide +kernel

/-- The cells of the group 48. -/
noncomputable def cells48 : List Cell :=
  [{ i := 1, j := 24, k := 9, use := 0, tree := 3 },
    { i := 1, j := 24, k := 24, use := 0, tree := 5 },
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

/-- The group 48: the cover of a box by its cells. -/
theorem g48_ok : boxOk run { e1 := 1, c1 := 1, e2 := 2, c2 := 7, e3 := 1, c3 := 3 } (hex% "3ef9f6fb9f6fbb9f6fbbb9f6") cells48 = true := by
  decide +kernel

/-- The cells of the group 49. -/
noncomputable def cells49 : List Cell :=
  [{ i := 2, j := 1, k := 0, use := 0, tree := hex% "ebd8580000000000e7239000000000000000000000000000000004" }]

/-- The group 49: the cover of a box by its cells. -/
theorem g49_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 0 } (3) cells49 = true := by
  decide +kernel

/-- The cells of the group 50. -/
noncomputable def cells50 : List Cell :=
  [{ i := 2, j := 1, k := 1, use := 0, tree := hex% "c0000000000129a84000000000014e1940000000000000000000000000000000210a8" }]

/-- The group 50: the cover of a box by its cells. -/
theorem g50_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 1 } (3) cells50 = true := by
  decide +kernel

/-- The cells of the group 51. -/
noncomputable def cells51 : List Cell :=
  [{ i := 2, j := 1, k := 2, use := 0, tree := hex% "198ac6800000000000000000000000000000004" }]

/-- The group 51: the cover of a box by its cells. -/
theorem g51_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 2 } (3) cells51 = true := by
  decide +kernel

/-- The cells of the group 52. -/
noncomputable def cells52 : List Cell :=
  [{ i := 2, j := 1, k := 9, use := 0, tree := hex% "81bba00000000000000000000000000005fc14" },
    { i := 2, j := 1, k := 24, use := 0, tree := 3 },
    { i := 2, j := 1, k := 25, use := 0, tree := 3 },
    { i := 2, j := 1, k := 26, use := 0, tree := 3 },
    { i := 2, j := 1, k := 27, use := 0, tree := 3 },
    { i := 2, j := 1, k := 28, use := 0, tree := 3 }]

/-- The group 52: the cover of a box by its cells. -/
theorem g52_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 3 } (4124398) cells52 = true := by
  decide +kernel

/-- The cells of the group 53. -/
noncomputable def cells53 : List Cell :=
  [{ i := 2, j := 2, k := 1, use := 0, tree := hex% "198ac68000000000000000000000000000000000000000000000004" }]

/-- The group 53: the cover of a box by its cells. -/
theorem g53_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 1 } (3) cells53 = true := by
  decide +kernel

/-- The cells of the group 54. -/
noncomputable def cells54 : List Cell :=
  [{ i := 2, j := 2, k := 2, use := 0, tree := 3 }]

/-- The group 54: the cover of a box by its cells. -/
theorem g54_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 2 } (3) cells54 = true := by
  decide +kernel

/-- The cells of the group 55. -/
noncomputable def cells55 : List Cell :=
  [{ i := 7, j := 2, k := 9, use := 0, tree := 3681358546 },
    { i := 8, j := 7, k := 9, use := 0, tree := hex% "c00000000000000000000000000318638000000000000000000000000000000022" },
    { i := 20, j := 8, k := 9, use := 0, tree := 15068277088978 },
    { i := 21, j := 20, k := 9, use := 0, tree := hex% "33fbda000000000000000000000000000000011b4d2" },
    { i := 21, j := 21, k := 22, use := 0, tree := hex% "db65000000000000000000000000000334810000000000000000000000000000000046d8442" },
    { i := 21, j := 21, k := 23, use := 0, tree := 57454746 },
    { i := 2, j := 2, k := 24, use := 0, tree := 3 },
    { i := 2, j := 2, k := 25, use := 0, tree := 3 },
    { i := 2, j := 2, k := 26, use := 0, tree := 3 },
    { i := 2, j := 2, k := 27, use := 0, tree := 3 },
    { i := 2, j := 2, k := 28, use := 0, tree := 3 }]

/-- The group 55: the cover of a box by its cells. -/
theorem g55_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 3 } (4324746556274) cells55 = true := by
  decide +kernel

/-- The cells of the group 56. -/
noncomputable def cells56 : List Cell :=
  [{ i := 2, j := 9, k := 2, use := 0, tree := hex% "20a4c98000000000000000000000000000000000000000000000004" }]

/-- The group 56: the cover of a box by its cells. -/
theorem g56_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 3, e3 := 1, c3 := 2 } (61) cells56 = true := by
  decide +kernel

end N14Cert.Case2Rrr

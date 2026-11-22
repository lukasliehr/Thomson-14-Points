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

/-- The cells of the group 126. -/
noncomputable def cells126 : List Cell :=
  [{ i := 24, j := 25, k := 24, use := 0, tree := 3 },
    { i := 24, j := 26, k := 24, use := 0, tree := 3 },
    { i := 24, j := 27, k := 24, use := 0, tree := 3 },
    { i := 24, j := 28, k := 24, use := 0, tree := 3 },
    { i := 24, j := 25, k := 25, use := 0, tree := 3 },
    { i := 24, j := 25, k := 26, use := 0, tree := 3 },
    { i := 24, j := 25, k := 27, use := 0, tree := 3 },
    { i := 24, j := 25, k := 28, use := 0, tree := 3 },
    { i := 24, j := 26, k := 25, use := 0, tree := 3 },
    { i := 24, j := 27, k := 25, use := 0, tree := 3 },
    { i := 24, j := 28, k := 25, use := 0, tree := 3 },
    { i := 24, j := 26, k := 26, use := 0, tree := 3 },
    { i := 24, j := 26, k := 27, use := 0, tree := 3 },
    { i := 24, j := 26, k := 28, use := 0, tree := 3 },
    { i := 24, j := 27, k := 26, use := 0, tree := 3 },
    { i := 24, j := 28, k := 26, use := 0, tree := 3 },
    { i := 24, j := 27, k := 27, use := 0, tree := 5 },
    { i := 24, j := 27, k := 28, use := 0, tree := 5 },
    { i := 24, j := 28, k := 27, use := 0, tree := 5 },
    { i := 24, j := 28, k := 28, use := 0, tree := 5 }]

/-- The group 126: the cover of a box by its cells. -/
theorem g126_ok : boxOk run { e1 := 3, c1 := 14, e2 := 3, c2 := 15, e3 := 2, c3 := 7 } (hex% "3ef9f6fb9f76fbb9f776") cells126 = true := by
  decide +kernel

/-- The cells of the group 127. -/
noncomputable def cells127 : List Cell :=
  [{ i := 25, j := 24, k := 24, use := 0, tree := 3 },
    { i := 25, j := 24, k := 25, use := 0, tree := 3 },
    { i := 25, j := 24, k := 26, use := 0, tree := 3 },
    { i := 25, j := 24, k := 27, use := 0, tree := 3 },
    { i := 25, j := 24, k := 28, use := 0, tree := 3 }]

/-- The group 127: the cover of a box by its cells. -/
theorem g127_ok : boxOk run { e1 := 3, c1 := 15, e2 := 3, c2 := 14, e3 := 2, c3 := 7 } (66828530) cells127 = true := by
  decide +kernel

/-- The cells of the group 128. -/
noncomputable def cells128 : List Cell :=
  [{ i := 25, j := 25, k := 24, use := 0, tree := 3 },
    { i := 25, j := 26, k := 24, use := 0, tree := 3 },
    { i := 25, j := 27, k := 24, use := 0, tree := 3 },
    { i := 25, j := 28, k := 24, use := 0, tree := 3 },
    { i := 26, j := 25, k := 24, use := 0, tree := 3 },
    { i := 26, j := 26, k := 24, use := 0, tree := 3 },
    { i := 26, j := 27, k := 24, use := 0, tree := 3 },
    { i := 26, j := 28, k := 24, use := 0, tree := 3 },
    { i := 27, j := 26, k := 24, use := 0, tree := 3 },
    { i := 27, j := 27, k := 24, use := 0, tree := 5 },
    { i := 27, j := 28, k := 24, use := 0, tree := 5 },
    { i := 28, j := 27, k := 24, use := 0, tree := 5 },
    { i := 28, j := 28, k := 24, use := 0, tree := 5 }]

/-- The group 128: the cover of a box by its cells. -/
theorem g128_ok : boxOk run { e1 := 3, c1 := 15, e2 := 3, c2 := 15, e3 := 3, c3 := 14 } (279028698444855156) cells128 = true := by
  decide +kernel

/-- The cells of the group 129. -/
noncomputable def cells129 : List Cell :=
  [{ i := 25, j := 25, k := 25, use := 0, tree := 3 },
    { i := 25, j := 25, k := 26, use := 0, tree := 3 },
    { i := 25, j := 25, k := 27, use := 0, tree := 3 },
    { i := 25, j := 25, k := 28, use := 0, tree := 3 },
    { i := 25, j := 26, k := 25, use := 0, tree := 3 },
    { i := 25, j := 27, k := 25, use := 0, tree := 3 },
    { i := 25, j := 28, k := 25, use := 0, tree := 3 },
    { i := 25, j := 26, k := 26, use := 0, tree := 3 },
    { i := 25, j := 26, k := 27, use := 0, tree := 3 },
    { i := 25, j := 26, k := 28, use := 0, tree := 3 },
    { i := 25, j := 27, k := 26, use := 0, tree := 3 },
    { i := 25, j := 28, k := 26, use := 0, tree := 3 },
    { i := 25, j := 27, k := 27, use := 0, tree := 3 },
    { i := 25, j := 27, k := 28, use := 0, tree := 3 },
    { i := 25, j := 28, k := 27, use := 0, tree := 3 },
    { i := 25, j := 28, k := 28, use := 0, tree := 5 }]

/-- The group 129: the cover of a box by its cells. -/
theorem g129_ok : boxOk run { e1 := 4, c1 := 30, e2 := 3, c2 := 15, e3 := 3, c3 := 15 } (4537929660125084601) cells129 = true := by
  decide +kernel

/-- The cells of the group 130. -/
noncomputable def cells130 : List Cell :=
  [{ i := 26, j := 25, k := 25, use := 0, tree := 3 },
    { i := 26, j := 25, k := 26, use := 0, tree := 3 },
    { i := 26, j := 25, k := 27, use := 0, tree := 3 },
    { i := 26, j := 25, k := 28, use := 0, tree := 3 }]

/-- The group 130: the cover of a box by its cells. -/
theorem g130_ok : boxOk run { e1 := 4, c1 := 31, e2 := 4, c2 := 30, e3 := 3, c3 := 15 } (4176114) cells130 = true := by
  decide +kernel

/-- The cells of the group 131. -/
noncomputable def cells131 : List Cell :=
  [{ i := 26, j := 26, k := 25, use := 0, tree := 3 },
    { i := 26, j := 27, k := 25, use := 0, tree := 3 },
    { i := 26, j := 28, k := 25, use := 0, tree := 3 },
    { i := 27, j := 26, k := 25, use := 0, tree := 3 },
    { i := 27, j := 27, k := 25, use := 0, tree := 3 },
    { i := 27, j := 28, k := 25, use := 0, tree := 3 },
    { i := 28, j := 27, k := 25, use := 0, tree := 3 },
    { i := 28, j := 28, k := 25, use := 0, tree := 5 }]

/-- The group 131: the cover of a box by its cells. -/
theorem g131_ok : boxOk run { e1 := 4, c1 := 31, e2 := 4, c2 := 31, e3 := 4, c3 := 30 } (16631406452) cells131 = true := by
  decide +kernel

/-- The cells of the group 132. -/
noncomputable def cells132 : List Cell :=
  [{ i := 26, j := 26, k := 26, use := 0, tree := 3 },
    { i := 26, j := 26, k := 27, use := 0, tree := 3 },
    { i := 26, j := 26, k := 28, use := 0, tree := 3 },
    { i := 26, j := 27, k := 26, use := 0, tree := 3 },
    { i := 26, j := 28, k := 26, use := 0, tree := 3 },
    { i := 26, j := 27, k := 27, use := 0, tree := 3 },
    { i := 26, j := 27, k := 28, use := 0, tree := 3 },
    { i := 26, j := 28, k := 27, use := 0, tree := 3 },
    { i := 26, j := 28, k := 28, use := 0, tree := 3 }]

/-- The group 132: the cover of a box by its cells. -/
theorem g132_ok : boxOk run { e1 := 5, c1 := 62, e2 := 4, c2 := 31, e3 := 4, c3 := 31 } (16905105337) cells132 = true := by
  decide +kernel

end N14Cert.Case2Prr

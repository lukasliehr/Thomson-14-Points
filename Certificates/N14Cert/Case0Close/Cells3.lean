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

/-- The cells of the group 20. -/
noncomputable def cells20 : List Cell :=
  [{ i := 9, j := 2, k := 0, use := 0, tree := hex% "5858cf51000000000000000000000000066f715d0000000000000011c" },
    { i := 9, j := 2, k := 1, use := 0, tree := 3 },
    { i := 9, j := 2, k := 2, use := 0, tree := 3 },
    { i := 9, j := 2, k := 3, use := 0, tree := 3 },
    { i := 9, j := 2, k := 4, use := 0, tree := 3 }]

/-- The group 20: the cover of a box by its cells. -/
theorem g20_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 3 } (66829240) cells20 = true := by
  decide +kernel

/-- The cells of the group 21. -/
noncomputable def cells21 : List Cell :=
  [{ i := 9, j := 9, k := 0, use := 0, tree := hex% "5c6e149b0000000000000000000000000000000180000000000000004" },
    { i := 9, j := 9, k := 1, use := 0, tree := 3 },
    { i := 9, j := 9, k := 2, use := 0, tree := 3 },
    { i := 9, j := 9, k := 3, use := 0, tree := 3 },
    { i := 9, j := 9, k := 4, use := 0, tree := 3 }]

/-- The group 21: the cover of a box by its cells. -/
theorem g21_ok : boxOk run { e1 := 2, c1 := 6, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (4124398) cells21 = true := by
  decide +kernel

/-- The cells of the group 22. -/
noncomputable def cells22 : List Cell :=
  [{ i := 9, j := 24, k := 0, use := 0, tree := 3 },
    { i := 9, j := 24, k := 1, use := 0, tree := 3 },
    { i := 9, j := 24, k := 2, use := 0, tree := 3 },
    { i := 9, j := 24, k := 3, use := 0, tree := 3 },
    { i := 9, j := 24, k := 4, use := 0, tree := 3 },
    { i := 9, j := 25, k := 0, use := 0, tree := 3 },
    { i := 9, j := 25, k := 1, use := 0, tree := 3 },
    { i := 9, j := 25, k := 2, use := 0, tree := 3 },
    { i := 9, j := 25, k := 3, use := 0, tree := 3 },
    { i := 9, j := 25, k := 4, use := 0, tree := 5 },
    { i := 9, j := 26, k := 1, use := 0, tree := 3 },
    { i := 9, j := 26, k := 2, use := 0, tree := 5 },
    { i := 9, j := 26, k := 3, use := 0, tree := 5 },
    { i := 9, j := 26, k := 4, use := 0, tree := 5 },
    { i := 9, j := 27, k := 2, use := 0, tree := 5 },
    { i := 9, j := 27, k := 3, use := 0, tree := 5 },
    { i := 9, j := 27, k := 4, use := 0, tree := 5 },
    { i := 9, j := 28, k := 3, use := 0, tree := 5 },
    { i := 9, j := 28, k := 4, use := 0, tree := 5 }]

/-- The group 22: the cover of a box by its cells. -/
theorem g22_ok : boxOk run { e1 := 2, c1 := 6, e2 := 2, c2 := 7, e3 := 1, c3 := 3 } (hex% "3ef9f6fb9f6fbb9f6fbbb9e") cells22 = true := by
  decide +kernel

/-- The cells of the group 23. -/
noncomputable def cells23 : List Cell :=
  [{ i := 24, j := 9, k := 0, use := 0, tree := 3 },
    { i := 24, j := 9, k := 1, use := 0, tree := 3 },
    { i := 24, j := 9, k := 2, use := 0, tree := 3 },
    { i := 24, j := 9, k := 3, use := 0, tree := 3 },
    { i := 24, j := 9, k := 4, use := 0, tree := 3 }]

/-- The group 23: the cover of a box by its cells. -/
theorem g23_ok : boxOk run { e1 := 2, c1 := 7, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (66829198) cells23 = true := by
  decide +kernel

/-- The cells of the group 24. -/
noncomputable def cells24 : List Cell :=
  [{ i := 24, j := 24, k := 0, use := 0, tree := 3 },
    { i := 24, j := 24, k := 1, use := 0, tree := 3 },
    { i := 24, j := 24, k := 2, use := 0, tree := 3 },
    { i := 24, j := 24, k := 3, use := 0, tree := 3 },
    { i := 24, j := 24, k := 4, use := 0, tree := 3 },
    { i := 24, j := 25, k := 0, use := 0, tree := 3 },
    { i := 24, j := 25, k := 1, use := 0, tree := 3 },
    { i := 24, j := 25, k := 2, use := 0, tree := 3 },
    { i := 24, j := 25, k := 3, use := 0, tree := 3 },
    { i := 24, j := 25, k := 4, use := 0, tree := 3 },
    { i := 24, j := 26, k := 1, use := 0, tree := 3 },
    { i := 24, j := 26, k := 2, use := 0, tree := 3 },
    { i := 24, j := 26, k := 3, use := 0, tree := 3 },
    { i := 24, j := 26, k := 4, use := 0, tree := 3 },
    { i := 24, j := 27, k := 2, use := 0, tree := 3 },
    { i := 24, j := 27, k := 3, use := 0, tree := 5 },
    { i := 24, j := 27, k := 4, use := 0, tree := 5 },
    { i := 24, j := 28, k := 3, use := 0, tree := 5 },
    { i := 24, j := 28, k := 4, use := 0, tree := 5 }]

/-- The group 24: the cover of a box by its cells. -/
theorem g24_ok : boxOk run { e1 := 3, c1 := 14, e2 := 2, c2 := 7, e3 := 2, c3 := 7 } (hex% "3ef9f6fb9f6fbb9f6fbbb9") cells24 = true := by
  decide +kernel

/-- The cells of the group 25. -/
noncomputable def cells25 : List Cell :=
  [{ i := 25, j := 24, k := 0, use := 0, tree := 3 },
    { i := 25, j := 24, k := 1, use := 0, tree := 3 },
    { i := 25, j := 24, k := 2, use := 0, tree := 3 },
    { i := 25, j := 24, k := 3, use := 0, tree := 3 },
    { i := 25, j := 24, k := 4, use := 0, tree := 3 }]

/-- The group 25: the cover of a box by its cells. -/
theorem g25_ok : boxOk run { e1 := 3, c1 := 15, e2 := 3, c2 := 14, e3 := 2, c3 := 7 } (66828530) cells25 = true := by
  decide +kernel

/-- The cells of the group 26. -/
noncomputable def cells26 : List Cell :=
  [{ i := 25, j := 25, k := 0, use := 0, tree := 3 },
    { i := 26, j := 25, k := 0, use := 0, tree := 3 }]

/-- The group 26: the cover of a box by its cells. -/
theorem g26_ok : boxOk run { e1 := 3, c1 := 15, e2 := 3, c2 := 15, e3 := 3, c3 := 14 } (258548) cells26 = true := by
  decide +kernel

/-- The cells of the group 27. -/
noncomputable def cells27 : List Cell :=
  [{ i := 25, j := 25, k := 1, use := 0, tree := 3 },
    { i := 25, j := 25, k := 2, use := 0, tree := 3 },
    { i := 25, j := 25, k := 3, use := 0, tree := 3 },
    { i := 25, j := 25, k := 4, use := 0, tree := 3 },
    { i := 25, j := 26, k := 1, use := 0, tree := 3 },
    { i := 25, j := 26, k := 2, use := 0, tree := 3 },
    { i := 25, j := 26, k := 3, use := 0, tree := 3 },
    { i := 25, j := 26, k := 4, use := 0, tree := 3 },
    { i := 25, j := 27, k := 2, use := 0, tree := 3 },
    { i := 25, j := 27, k := 3, use := 0, tree := 3 },
    { i := 25, j := 27, k := 4, use := 0, tree := 3 },
    { i := 25, j := 28, k := 3, use := 0, tree := 3 },
    { i := 25, j := 28, k := 4, use := 0, tree := 5 }]

/-- The group 27: the cover of a box by its cells. -/
theorem g27_ok : boxOk run { e1 := 4, c1 := 30, e2 := 3, c2 := 15, e3 := 3, c3 := 15 } (283620603757788089) cells27 = true := by
  decide +kernel

end N14Cert.Case0Close

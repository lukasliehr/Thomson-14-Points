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

/-- The cells of the group 115. -/
noncomputable def cells115 : List Cell :=
  [{ i := 9, j := 9, k := 5, use := 0, tree := hex% "db2180000000000163f080000000000000000000000000000000000000000000000042da6426400000000020dfdf80000000000000000000000000000000000000000000001f20" },
    { i := 9, j := 9, k := 6, use := 0, tree := hex% "162c5c0000000000000000000000000000000000000000000000011b6506d9040000000001bce64400000000000000000000000000000000000000000000008e0" },
    { i := 9, j := 24, k := 1, use := 0, tree := 3 },
    { i := 9, j := 25, k := 1, use := 0, tree := 5 },
    { i := 9, j := 26, k := 1, use := 0, tree := 5 },
    { i := 9, j := 27, k := 1, use := 0, tree := 5 },
    { i := 9, j := 28, k := 1, use := 0, tree := 5 }]

/-- The group 115: the cover of a box by its cells. -/
theorem g115_ok : boxOk run { e1 := 2, c1 := 6, e2 := 1, c2 := 3, e3 := 1, c3 := 1 } (64871929) cells115 = true := by
  decide +kernel

/-- The cells of the group 116. -/
noncomputable def cells116 : List Cell :=
  [{ i := 24, j := 9, k := 1, use := 0, tree := 3 },
    { i := 24, j := 24, k := 1, use := 0, tree := 5 },
    { i := 24, j := 25, k := 1, use := 0, tree := 5 },
    { i := 24, j := 26, k := 1, use := 0, tree := 5 },
    { i := 24, j := 27, k := 1, use := 0, tree := 5 },
    { i := 24, j := 28, k := 1, use := 0, tree := 5 },
    { i := 25, j := 24, k := 1, use := 0, tree := 5 },
    { i := 25, j := 25, k := 1, use := 0, tree := 5 },
    { i := 25, j := 26, k := 1, use := 0, tree := 5 },
    { i := 25, j := 27, k := 1, use := 0, tree := 5 },
    { i := 25, j := 28, k := 1, use := 0, tree := 5 },
    { i := 26, j := 25, k := 1, use := 0, tree := 5 },
    { i := 26, j := 26, k := 1, use := 0, tree := 5 },
    { i := 26, j := 27, k := 1, use := 0, tree := 5 },
    { i := 26, j := 28, k := 1, use := 0, tree := 5 },
    { i := 27, j := 26, k := 1, use := 0, tree := 5 },
    { i := 27, j := 27, k := 1, use := 0, tree := 5 },
    { i := 27, j := 28, k := 1, use := 0, tree := 5 },
    { i := 28, j := 27, k := 1, use := 0, tree := 5 },
    { i := 28, j := 28, k := 1, use := 0, tree := 5 }]

/-- The group 116: the cover of a box by its cells. -/
theorem g116_ok : boxOk run { e1 := 2, c1 := 7, e2 := 1, c2 := 3, e3 := 1, c3 := 1 } (hex% "3df4f1f74f1f774f1f7774f1") cells116 = true := by
  decide +kernel

/-- The cells of the group 117. -/
noncomputable def cells117 : List Cell :=
  [{ i := 9, j := 9, k := 7, use := 0, tree := hex% "d960000000000020f34800000000000000000000000000000000000000000000000216d94c8640000000001c6ac200000000000000000000000000000000000000000000000260" },
    { i := 22, j := 22, k := 20, use := 0, tree := hex% "36c900000000004d32400000000000000000000000000000000000000000000000008d9608" },
    { i := 22, j := 22, k := 21, use := 0, tree := hex% "db4cb6426cb6d0651000000000015141e0000000000000000000000000000000000000000000000008d8688" },
    { i := 22, j := 23, k := 8, use := 0, tree := 13977 },
    { i := 23, j := 9, k := 8, use := 0, tree := hex% "6a66310000000000000000000000000000000000000000000000004" },
    { i := 9, j := 24, k := 2, use := 0, tree := 3 },
    { i := 9, j := 25, k := 2, use := 0, tree := 3 },
    { i := 9, j := 26, k := 2, use := 0, tree := 3 },
    { i := 9, j := 27, k := 2, use := 0, tree := 3 },
    { i := 9, j := 28, k := 2, use := 0, tree := 3 }]

/-- The group 117: the cover of a box by its cells. -/
theorem g117_ok : boxOk run { e1 := 2, c1 := 6, e2 := 1, c2 := 3, e3 := 1, c3 := 2 } (265715448121) cells117 = true := by
  decide +kernel

/-- The cells of the group 118. -/
noncomputable def cells118 : List Cell :=
  [{ i := 24, j := 9, k := 2, use := 0, tree := 3 },
    { i := 24, j := 24, k := 2, use := 0, tree := 3 },
    { i := 24, j := 25, k := 2, use := 0, tree := 3 },
    { i := 24, j := 26, k := 2, use := 0, tree := 3 },
    { i := 24, j := 27, k := 2, use := 0, tree := 5 },
    { i := 24, j := 28, k := 2, use := 0, tree := 5 },
    { i := 25, j := 24, k := 2, use := 0, tree := 3 },
    { i := 25, j := 25, k := 2, use := 0, tree := 5 },
    { i := 25, j := 26, k := 2, use := 0, tree := 5 },
    { i := 25, j := 27, k := 2, use := 0, tree := 5 },
    { i := 25, j := 28, k := 2, use := 0, tree := 5 },
    { i := 26, j := 25, k := 2, use := 0, tree := 5 },
    { i := 26, j := 26, k := 2, use := 0, tree := 5 },
    { i := 26, j := 27, k := 2, use := 0, tree := 5 },
    { i := 26, j := 28, k := 2, use := 0, tree := 5 },
    { i := 27, j := 26, k := 2, use := 0, tree := 5 },
    { i := 27, j := 27, k := 2, use := 0, tree := 5 },
    { i := 27, j := 28, k := 2, use := 0, tree := 5 },
    { i := 28, j := 27, k := 2, use := 0, tree := 5 },
    { i := 28, j := 28, k := 2, use := 0, tree := 5 }]

/-- The group 118: the cover of a box by its cells. -/
theorem g118_ok : boxOk run { e1 := 2, c1 := 7, e2 := 1, c2 := 3, e3 := 1, c3 := 2 } (hex% "3df4f1f74f1f774f1f7774f1") cells118 = true := by
  decide +kernel

end N14Cert.Case2Prr

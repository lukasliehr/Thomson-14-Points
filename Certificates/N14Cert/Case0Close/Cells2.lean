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

/-- The cells of the group 14. -/
noncomputable def cells14 : List Cell :=
  [{ i := 1, j := 24, k := 0, use := 0, tree := 5 },
    { i := 1, j := 24, k := 1, use := 0, tree := 5 },
    { i := 1, j := 24, k := 2, use := 0, tree := 5 },
    { i := 1, j := 24, k := 3, use := 0, tree := 5 },
    { i := 1, j := 24, k := 4, use := 0, tree := 5 },
    { i := 1, j := 25, k := 0, use := 0, tree := 5 },
    { i := 1, j := 25, k := 1, use := 0, tree := 5 },
    { i := 1, j := 25, k := 2, use := 0, tree := 5 },
    { i := 1, j := 25, k := 3, use := 0, tree := 5 },
    { i := 1, j := 25, k := 4, use := 0, tree := 5 },
    { i := 1, j := 26, k := 1, use := 0, tree := 5 },
    { i := 1, j := 26, k := 2, use := 0, tree := 5 },
    { i := 1, j := 26, k := 3, use := 0, tree := 5 },
    { i := 1, j := 26, k := 4, use := 0, tree := 5 },
    { i := 1, j := 27, k := 2, use := 0, tree := 5 },
    { i := 1, j := 27, k := 3, use := 0, tree := 5 },
    { i := 1, j := 27, k := 4, use := 0, tree := 5 },
    { i := 1, j := 28, k := 3, use := 0, tree := 5 },
    { i := 1, j := 28, k := 4, use := 0, tree := 5 }]

/-- The group 14: the cover of a box by its cells. -/
theorem g14_ok : boxOk run { e1 := 1, c1 := 1, e2 := 2, c2 := 7, e3 := 1, c3 := 3 } (hex% "3ef9f6fb9f6fbb9f6fbbb9e") cells14 = true := by
  decide +kernel

/-- The cells of the group 15. -/
noncomputable def cells15 : List Cell :=
  [{ i := 2, j := 1, k := 0, use := 0, tree := hex% "5ccdff7300000000000000000000000004bab6af80000000005327944" },
    { i := 2, j := 1, k := 1, use := 0, tree := 3 },
    { i := 2, j := 1, k := 2, use := 0, tree := 3 },
    { i := 2, j := 1, k := 3, use := 0, tree := 3 },
    { i := 2, j := 1, k := 4, use := 0, tree := 3 }]

/-- The group 15: the cover of a box by its cells. -/
theorem g15_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 3 } (4124398) cells15 = true := by
  decide +kernel

/-- The cells of the group 16. -/
noncomputable def cells16 : List Cell :=
  [{ i := 7, j := 2, k := 0, use := 0, tree := hex% "16553d3b40000000000000000000000000000000000000000000000011a" },
    { i := 8, j := 7, k := 0, use := 0, tree := hex% "58f69f880000000000000000000000000593bd0d00000000000000014" },
    { i := 20, j := 8, k := 0, use := 0, tree := hex% "173e59a08000000000000000000000000000000000000000000000001000000002b591e55c00000000000000000000000000000000000000000000000207400000002b1788228000000000000000000000000000000000000000000000002221d45a" },
    { i := 21, j := 8, k := 0, use := 0, tree := hex% "16ed13f800000000000000000000000000a9e899e000000000000000103a000000015b9a501600000000000000000000000000000000000000000000000110000000056b3800e80000000000000000000000000b9ee0d0000000000000000401d00000000ad4194ee0000000000000000000000000000000000000000000000008800000002b617a024000000000000000000000000000000000000000000000002021d45a" },
    { i := 2, j := 2, k := 1, use := 0, tree := 3 },
    { i := 2, j := 2, k := 2, use := 0, tree := 3 },
    { i := 2, j := 2, k := 3, use := 0, tree := 3 },
    { i := 2, j := 2, k := 4, use := 0, tree := 3 }]

/-- The group 16: the cover of a box by its cells. -/
theorem g16_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 3 } (16893556526) cells16 = true := by
  decide +kernel

/-- The cells of the group 17. -/
noncomputable def cells17 : List Cell :=
  [{ i := 2, j := 9, k := 0, use := 0, tree := hex% "58b75356000000000000000000000000000000000000000000000009c680000000200fe48f80000000000000000000000000000000000000000000000de100000000aa8453b400000000000000000000000000000000000000000000000081d4000000016ad6cb6e00000000000000000000000000000000000000000000000100000000058fb208e00000000000000000000000000000000000000000000000042d0" },
    { i := 2, j := 9, k := 1, use := 0, tree := 3 },
    { i := 2, j := 9, k := 2, use := 0, tree := 3 },
    { i := 2, j := 9, k := 3, use := 0, tree := 3 },
    { i := 2, j := 9, k := 4, use := 0, tree := 3 }]

/-- The group 17: the cover of a box by its cells. -/
theorem g17_ok : boxOk run { e1 := 1, c1 := 2, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (4124398) cells17 = true := by
  decide +kernel

/-- The cells of the group 18. -/
noncomputable def cells18 : List Cell :=
  [{ i := 2, j := 24, k := 0, use := 0, tree := hex% "a40000000000000008000000000000000000000000776c3ffd18" },
    { i := 2, j := 24, k := 1, use := 0, tree := 20974882156 },
    { i := 2, j := 24, k := 2, use := 0, tree := 57881441484 },
    { i := 2, j := 24, k := 3, use := 0, tree := 5 },
    { i := 2, j := 24, k := 4, use := 0, tree := 5 }]

/-- The group 18: the cover of a box by its cells. -/
theorem g18_ok : boxOk run { e1 := 1, c1 := 2, e2 := 3, c2 := 14, e3 := 2, c3 := 7 } (257774) cells18 = true := by
  decide +kernel

/-- The cells of the group 19. -/
noncomputable def cells19 : List Cell :=
  [{ i := 2, j := 25, k := 0, use := 0, tree := hex% "1b80000000aaeae7c98000000000000000000000004e2334d6c" },
    { i := 2, j := 25, k := 1, use := 0, tree := 5 },
    { i := 2, j := 25, k := 2, use := 0, tree := 5 },
    { i := 2, j := 25, k := 3, use := 0, tree := 5 },
    { i := 2, j := 25, k := 4, use := 0, tree := 5 },
    { i := 2, j := 26, k := 1, use := 0, tree := 5 },
    { i := 2, j := 26, k := 2, use := 0, tree := 5 },
    { i := 2, j := 26, k := 3, use := 0, tree := 5 },
    { i := 2, j := 26, k := 4, use := 0, tree := 5 },
    { i := 2, j := 27, k := 2, use := 0, tree := 5 },
    { i := 2, j := 27, k := 3, use := 0, tree := 5 },
    { i := 2, j := 27, k := 4, use := 0, tree := 5 },
    { i := 2, j := 28, k := 3, use := 0, tree := 5 },
    { i := 2, j := 28, k := 4, use := 0, tree := 5 }]

/-- The group 19: the cover of a box by its cells. -/
theorem g19_ok : boxOk run { e1 := 1, c1 := 2, e2 := 3, c2 := 15, e3 := 2, c3 := 7 } (hex% "3ef9f6fb9f6fbb9f6") cells19 = true := by
  decide +kernel

end N14Cert.Case0Close

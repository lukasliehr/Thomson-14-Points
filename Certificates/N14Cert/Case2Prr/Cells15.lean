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

/-- The cells of the group 106. -/
noncomputable def cells106 : List Cell :=
  [{ i := 2, j := 24, k := 9, use := 0, tree := 4668068634 },
    { i := 2, j := 25, k := 9, use := 0, tree := 485984948 },
    { i := 2, j := 26, k := 9, use := 0, tree := 3 },
    { i := 2, j := 27, k := 9, use := 0, tree := 3 },
    { i := 2, j := 28, k := 9, use := 0, tree := 3 }]

/-- The group 106: the cover of a box by its cells. -/
theorem g106_ok : boxOk run { e1 := 1, c1 := 2, e2 := 2, c2 := 7, e3 := 2, c3 := 6 } (253405) cells106 = true := by
  decide +kernel

/-- The cells of the group 107. -/
noncomputable def cells107 : List Cell :=
  [{ i := 2, j := 24, k := 24, use := 0, tree := 3 },
    { i := 2, j := 24, k := 25, use := 0, tree := 3 },
    { i := 2, j := 24, k := 26, use := 0, tree := 3 },
    { i := 2, j := 24, k := 27, use := 0, tree := 5 },
    { i := 2, j := 24, k := 28, use := 0, tree := 5 }]

/-- The group 107: the cover of a box by its cells. -/
theorem g107_ok : boxOk run { e1 := 1, c1 := 2, e2 := 3, c2 := 14, e3 := 2, c3 := 7 } (257774) cells107 = true := by
  decide +kernel

/-- The cells of the group 108. -/
noncomputable def cells108 : List Cell :=
  [{ i := 2, j := 25, k := 24, use := 0, tree := 3 },
    { i := 2, j := 26, k := 24, use := 0, tree := 3 },
    { i := 2, j := 27, k := 24, use := 0, tree := 5 },
    { i := 2, j := 28, k := 24, use := 0, tree := 5 },
    { i := 2, j := 25, k := 25, use := 0, tree := 5 },
    { i := 2, j := 25, k := 26, use := 0, tree := 5 },
    { i := 2, j := 25, k := 27, use := 0, tree := 5 },
    { i := 2, j := 25, k := 28, use := 0, tree := 5 },
    { i := 2, j := 26, k := 25, use := 0, tree := 5 },
    { i := 2, j := 27, k := 25, use := 0, tree := 5 },
    { i := 2, j := 28, k := 25, use := 0, tree := 5 },
    { i := 2, j := 26, k := 26, use := 0, tree := 5 },
    { i := 2, j := 26, k := 27, use := 0, tree := 5 },
    { i := 2, j := 26, k := 28, use := 0, tree := 5 },
    { i := 2, j := 27, k := 26, use := 0, tree := 5 },
    { i := 2, j := 28, k := 26, use := 0, tree := 5 },
    { i := 2, j := 27, k := 27, use := 0, tree := 5 },
    { i := 2, j := 27, k := 28, use := 0, tree := 5 },
    { i := 2, j := 28, k := 27, use := 0, tree := 5 },
    { i := 2, j := 28, k := 28, use := 0, tree := 5 }]

/-- The group 108: the cover of a box by its cells. -/
theorem g108_ok : boxOk run { e1 := 1, c1 := 2, e2 := 3, c2 := 15, e3 := 2, c3 := 7 } (hex% "3ef9f6fb9f76fbb9f776") cells108 = true := by
  decide +kernel

/-- The cells of the group 109. -/
noncomputable def cells109 : List Cell :=
  [{ i := 9, j := 2, k := 0, use := 0, tree := hex% "e602dcf8000000000000003000000000000000000000000098c1dcec" }]

/-- The group 109: the cover of a box by its cells. -/
theorem g109_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 0 } (60) cells109 = true := by
  decide +kernel

/-- The cells of the group 110. -/
noncomputable def cells110 : List Cell :=
  [{ i := 9, j := 2, k := 1, use := 0, tree := hex% "1d0eb000000000004990200000000000000000000000000000000000000000000000188b058000000000020b0e80000000000000000000000000000000000000000000000040000000000142a9f000000000000000000000000000000000000000000000000888742" }]

/-- The group 110: the cover of a box by its cells. -/
theorem g110_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 1 } (60) cells110 = true := by
  decide +kernel

/-- The cells of the group 111. -/
noncomputable def cells111 : List Cell :=
  [{ i := 9, j := 2, k := 2, use := 0, tree := hex% "4645268000000000000000000000000000000000000000000000004" }]

/-- The group 111: the cover of a box by its cells. -/
theorem g111_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 2 } (60) cells111 = true := by
  decide +kernel

/-- The cells of the group 112. -/
noncomputable def cells112 : List Cell :=
  [{ i := 9, j := 2, k := 9, use := 0, tree := hex% "743a1d00000000000e4fb40000000000000000000000000000000000000000000000008000000000018c57600000000000000000000000000000000000000000000000110243a000000000026cd2a000000000000000000000000000000000000000000000000a2" },
    { i := 9, j := 2, k := 24, use := 0, tree := 3 },
    { i := 9, j := 2, k := 25, use := 0, tree := 3 },
    { i := 9, j := 2, k := 26, use := 0, tree := 3 },
    { i := 9, j := 2, k := 27, use := 0, tree := 3 },
    { i := 9, j := 2, k := 28, use := 0, tree := 3 }]

/-- The group 112: the cover of a box by its cells. -/
theorem g112_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 3 } (66829240) cells112 = true := by
  decide +kernel

/-- The cells of the group 113. -/
noncomputable def cells113 : List Cell :=
  [{ i := 9, j := 9, k := 0, use := 0, tree := hex% "11000000000000002b00000000000000000000000007ef6dea4" },
    { i := 9, j := 24, k := 0, use := 0, tree := 5 },
    { i := 9, j := 25, k := 0, use := 0, tree := 5 },
    { i := 9, j := 26, k := 0, use := 0, tree := 5 },
    { i := 9, j := 27, k := 0, use := 0, tree := 5 },
    { i := 9, j := 28, k := 0, use := 0, tree := 5 }]

/-- The group 113: the cover of a box by its cells. -/
theorem g113_ok : boxOk run { e1 := 2, c1 := 6, e2 := 1, c2 := 3, e3 := 1, c3 := 0 } (4054493) cells113 = true := by
  decide +kernel

/-- The cells of the group 114. -/
noncomputable def cells114 : List Cell :=
  [{ i := 24, j := 9, k := 0, use := 0, tree := 5 },
    { i := 24, j := 24, k := 0, use := 0, tree := 5 },
    { i := 24, j := 25, k := 0, use := 0, tree := 5 },
    { i := 24, j := 26, k := 0, use := 0, tree := 5 },
    { i := 24, j := 27, k := 0, use := 0, tree := 5 },
    { i := 24, j := 28, k := 0, use := 0, tree := 5 },
    { i := 25, j := 24, k := 0, use := 0, tree := 5 },
    { i := 25, j := 25, k := 0, use := 0, tree := 5 },
    { i := 25, j := 26, k := 0, use := 0, tree := 5 },
    { i := 25, j := 27, k := 0, use := 0, tree := 5 },
    { i := 25, j := 28, k := 0, use := 0, tree := 5 },
    { i := 26, j := 25, k := 0, use := 0, tree := 5 },
    { i := 26, j := 26, k := 0, use := 0, tree := 5 },
    { i := 26, j := 27, k := 0, use := 0, tree := 5 },
    { i := 26, j := 28, k := 0, use := 0, tree := 5 },
    { i := 27, j := 26, k := 0, use := 0, tree := 5 },
    { i := 27, j := 27, k := 0, use := 0, tree := 5 },
    { i := 27, j := 28, k := 0, use := 0, tree := 5 },
    { i := 28, j := 27, k := 0, use := 0, tree := 5 },
    { i := 28, j := 28, k := 0, use := 0, tree := 5 }]

/-- The group 114: the cover of a box by its cells. -/
theorem g114_ok : boxOk run { e1 := 2, c1 := 7, e2 := 1, c2 := 3, e3 := 1, c3 := 0 } (hex% "3df4f1f74f1f774f1f7774f1") cells114 = true := by
  decide +kernel

end N14Cert.Case2Prr

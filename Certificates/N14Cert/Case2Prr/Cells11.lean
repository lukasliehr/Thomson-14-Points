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

/-- The cells of the group 72. -/
noncomputable def cells72 : List Cell :=
  [{ i := 14, j := 9, k := 9, use := 0, tree := 97393308959150122 },
    { i := 15, j := 22, k := 22, use := 0, tree := hex% "36c0000000000000000000000000000000000000000000000000000000000617a9a01501416000000000000000000000000000000000000000000000000000000000015869d00000000000000000000000000000000000000000000000000000000000571f1216000000000000000000000000000000000000000000000000000000000014f4a108000000000000000000000000000000000000000000000000000000000003f7648800000000000000000000000000000000000000000000000000000000006100a60000000000000000000000000000000000000000000000000000000000064cc846000000000000000000000000000000000000000000000000000000000004365aa2005000000000000000000000000000000000000000000000000000000000018d0f8800000000000000000000000000000000000000000000000000000000001fcb9b00000000000000000000000000000000000000000000000000000000000110e17440a20a" },
    { i := 15, j := 22, k := 23, use := 0, tree := hex% "30280000000000000000000000000000000000000000000000000000000002b1e4cc600000000000000000000000000000000000000000000000000000000007ec07b0a0400000000000000000000000000000000000000000000000000000000022c74122" },
    { i := 15, j := 23, k := 9, use := 0, tree := hex% "140000000000000000000000000000000000000000000000000000000001d4339a000000000000000000000000000000000000000000000000000000000011e5df402800000000000000000000000000000000000000000000000000000000008f4c840000000000000000000000000000000000000000000000000000000000016cbbb110280000000000000000000000000000000000000000000000000000000001c47c540886800000000000000000000000000000000000000000000000000000000036cfc0e102a" }]

/-- The group 72: the cover of a box by its cells. -/
theorem g72_ok : boxOk run { e1 := 2, c1 := 2, e2 := 2, c2 := 6, e3 := 2, c3 := 6 } (16284) cells72 = true := by
  decide +kernel

/-- The cells of the group 73. -/
noncomputable def cells73 : List Cell :=
  [{ i := 16, j := 22, k := 22, use := 0, tree := hex% "36db6c00000000000000000000000000000000000000000000000000000000002debba0211611" },
    { i := 16, j := 22, k := 23, use := 0, tree := hex% "d80000000000000000000000000000000000000000000000000000000000e3029c2c3600000000000000000000000000000000000000000000000000000000002fae1f000000000000000000000000000000000000000000000000000000000003efe5e20584400000000000000000000000000000000000000000000000000000000004110362" },
    { i := 16, j := 23, k := 22, use := 0, tree := hex% "c00000000000000000000000000000000000000000000000000000000006e552e3600000000000000000000000000000000000000000000000000000000003d9d51000000000000000000000000000000000000000000000000000000000004dae7e108b08000000000000000000000000000000000000000000000000000000000082301e1" },
    { i := 16, j := 23, k := 23, use := 0, tree := hex% "502800000000000000000000000000000000000000000000000000000000016b6e3c29800000000000000000000000000000000000000000000000000000000007f1f768400000000000000000000000000000000000000000000000000000000022698922" },
    { i := 17, j := 9, k := 9, use := 0, tree := 233444848330 }]

/-- The group 73: the cover of a box by its cells. -/
theorem g73_ok : boxOk run { e1 := 2, c1 := 3, e2 := 2, c2 := 6, e3 := 2, c3 := 6 } (261092) cells73 = true := by
  decide +kernel

/-- The cells of the group 74. -/
noncomputable def cells74 : List Cell :=
  [{ i := 1, j := 9, k := 24, use := 0, tree := hex% "560000000000000000000000000000000000000000000000000000000001a85e7708" },
    { i := 1, j := 9, k := 25, use := 0, tree := 5 },
    { i := 1, j := 9, k := 26, use := 0, tree := 5 },
    { i := 1, j := 9, k := 27, use := 0, tree := 5 },
    { i := 1, j := 9, k := 28, use := 0, tree := 5 }]

/-- The group 74: the cover of a box by its cells. -/
theorem g74_ok : boxOk run { e1 := 1, c1 := 1, e2 := 2, c2 := 6, e3 := 2, c3 := 7 } (257774) cells74 = true := by
  decide +kernel

/-- The cells of the group 75. -/
noncomputable def cells75 : List Cell :=
  [{ i := 1, j := 24, k := 9, use := 0, tree := hex% "5600000000000000000000000000000000000000000000000000000000015ed4c310" },
    { i := 1, j := 25, k := 9, use := 0, tree := 5 },
    { i := 1, j := 26, k := 9, use := 0, tree := 5 },
    { i := 1, j := 27, k := 9, use := 0, tree := 5 },
    { i := 1, j := 28, k := 9, use := 0, tree := 5 }]

/-- The group 75: the cover of a box by its cells. -/
theorem g75_ok : boxOk run { e1 := 1, c1 := 1, e2 := 2, c2 := 7, e3 := 2, c3 := 6 } (253405) cells75 = true := by
  decide +kernel

/-- The cells of the group 76. -/
noncomputable def cells76 : List Cell :=
  [{ i := 1, j := 24, k := 24, use := 0, tree := 5 },
    { i := 1, j := 24, k := 25, use := 0, tree := 5 },
    { i := 1, j := 24, k := 26, use := 0, tree := 5 },
    { i := 1, j := 24, k := 27, use := 0, tree := 5 },
    { i := 1, j := 24, k := 28, use := 0, tree := 5 }]

/-- The group 76: the cover of a box by its cells. -/
theorem g76_ok : boxOk run { e1 := 1, c1 := 1, e2 := 3, c2 := 14, e3 := 2, c3 := 7 } (257774) cells76 = true := by
  decide +kernel

/-- The cells of the group 77. -/
noncomputable def cells77 : List Cell :=
  [{ i := 1, j := 25, k := 24, use := 0, tree := 5 },
    { i := 1, j := 26, k := 24, use := 0, tree := 5 },
    { i := 1, j := 27, k := 24, use := 0, tree := 5 },
    { i := 1, j := 28, k := 24, use := 0, tree := 5 },
    { i := 1, j := 25, k := 25, use := 0, tree := 5 },
    { i := 1, j := 25, k := 26, use := 0, tree := 5 },
    { i := 1, j := 25, k := 27, use := 0, tree := 5 },
    { i := 1, j := 25, k := 28, use := 0, tree := 5 },
    { i := 1, j := 26, k := 25, use := 0, tree := 5 },
    { i := 1, j := 27, k := 25, use := 0, tree := 5 },
    { i := 1, j := 28, k := 25, use := 0, tree := 5 },
    { i := 1, j := 26, k := 26, use := 0, tree := 5 },
    { i := 1, j := 26, k := 27, use := 0, tree := 5 },
    { i := 1, j := 26, k := 28, use := 0, tree := 5 },
    { i := 1, j := 27, k := 26, use := 0, tree := 5 },
    { i := 1, j := 28, k := 26, use := 0, tree := 5 },
    { i := 1, j := 27, k := 27, use := 0, tree := 5 },
    { i := 1, j := 27, k := 28, use := 0, tree := 5 },
    { i := 1, j := 28, k := 27, use := 0, tree := 5 },
    { i := 1, j := 28, k := 28, use := 0, tree := 5 }]

/-- The group 77: the cover of a box by its cells. -/
theorem g77_ok : boxOk run { e1 := 1, c1 := 1, e2 := 3, c2 := 15, e3 := 2, c3 := 7 } (hex% "3ef9f6fb9f76fbb9f776") cells77 = true := by
  decide +kernel

/-- The cells of the group 78. -/
noncomputable def cells78 : List Cell :=
  [{ i := 2, j := 1, k := 0, use := 0, tree := hex% "4473dc0000000000000000000000000000000000000000000000004" }]

/-- The group 78: the cover of a box by its cells. -/
theorem g78_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 0 } (3) cells78 = true := by
  decide +kernel

/-- The cells of the group 79. -/
noncomputable def cells79 : List Cell :=
  [{ i := 2, j := 1, k := 1, use := 0, tree := hex% "8b59000000000000000000000000000000000000000000000000040e800000000001b48d8000000000000000000000000000000000000000000000004688742" }]

/-- The group 79: the cover of a box by its cells. -/
theorem g79_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 1 } (3) cells79 = true := by
  decide +kernel

/-- The cells of the group 80. -/
noncomputable def cells80 : List Cell :=
  [{ i := 2, j := 1, k := 2, use := 0, tree := hex% "119f5cc000000000000000000000000000000000000000000000001000000000002a65e00000000000000000000000000000000000000000000000022" }]

/-- The group 80: the cover of a box by its cells. -/
theorem g80_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 2 } (3) cells80 = true := by
  decide +kernel

/-- The cells of the group 81. -/
noncomputable def cells81 : List Cell :=
  [{ i := 2, j := 1, k := 9, use := 0, tree := hex% "1a5d5d000000000000000000000000000000000000000000000004c" },
    { i := 2, j := 1, k := 24, use := 0, tree := 3 },
    { i := 2, j := 1, k := 25, use := 0, tree := 3 },
    { i := 2, j := 1, k := 26, use := 0, tree := 3 },
    { i := 2, j := 1, k := 27, use := 0, tree := 3 },
    { i := 2, j := 1, k := 28, use := 0, tree := 3 }]

/-- The group 81: the cover of a box by its cells. -/
theorem g81_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 3 } (4124398) cells81 = true := by
  decide +kernel

end N14Cert.Case2Prr

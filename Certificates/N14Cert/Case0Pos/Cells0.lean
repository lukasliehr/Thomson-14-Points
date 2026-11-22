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

/-- The cells of the group 0. -/
noncomputable def cells0 : List Cell :=
  [{ i := 0, j := 0, k := 0, use := 0, tree := hex% "5400000000000000540000000020320ade4" }]

/-- The group 0: the cover of a box by its cells. -/
theorem g0_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 1, c3 := 0 } (3) cells0 = true := by
  decide +kernel

/-- The cells of the group 1. -/
noncomputable def cells1 : List Cell :=
  [{ i := 3, j := 0, k := 1, use := 0, tree := hex% "140ac0a00000000000000000000000000000000000000000678bbff03451" }]

/-- The group 1: the cover of a box by its cells. -/
theorem g1_ok : boxOk run { e1 := 2, c1 := 0, e2 := 1, c2 := 0, e3 := 1, c3 := 1 } (3) cells1 = true := by
  decide +kernel

/-- The cells of the group 2. -/
noncomputable def cells2 : List Cell :=
  [{ i := 4, j := 3, k := 1, use := 0, tree := hex% "32ec62a60000000014c707644" }]

/-- The group 2: the cover of a box by its cells. -/
theorem g2_ok : boxOk run { e1 := 2, c1 := 1, e2 := 2, c2 := 0, e3 := 1, c3 := 1 } (3) cells2 = true := by
  decide +kernel

/-- The cells of the group 3. -/
noncomputable def cells3 : List Cell :=
  [{ i := 12, j := 4, k := 5, use := 0, tree := hex% "140a050280000000000000000000000000000000000000000210b339c000000000000000000000000000000000000000002ba717a800a000000000000000000000000000000000000000009011c6702200000000000000000000000000000000000000000119d02ce000000000000000000000000000000000000000001a53f50c000000000000000000000000000000000000000001e18a928d108a" }]

/-- The group 3: the cover of a box by its cells. -/
theorem g3_ok : boxOk run { e1 := 3, c1 := 2, e2 := 2, c2 := 1, e3 := 2, c3 := 2 } (3) cells3 = true := by
  decide +kernel

/-- The cells of the group 4. -/
noncomputable def cells4 : List Cell :=
  [{ i := 13, j := 12, k := 5, use := 0, tree := hex% "eab3f3e00000000097079ac4" },
    { i := 13, j := 13, k := 14, use := 0, tree := hex% "50281400000000000000000000000000000000000000000f5e5946000000000000000000000000000000000000000001b48a18c000000000000000000000000000000000000000002b0b6058501400000000000000000000000000000000000000000f51cc8a20054400000000000000000000000010590688000000001417ba42000000000000000000000000000000000000000001b57309c000000000000000000000000000000000000000002af9931880000000000000000000000000000000000000000099d437a100000000000000000000000001670ef300000000026750de8c802800000000000000000000000000000000000000001b5ef8ec02a200000000000000000000000003ad8cfe0000000007bbab61000000000000000000000000000000000000000000ac49a8e000000000000000000000000000000000000000001b5e371c4422080281400000000000000000000000000000000000000001155c5320000000000000000000000000000000000000000018296124000000000000000000000000000000000000000003cfa45e88102800000000000000000000000000000000000000000418543080000000000000000000000000000000000000000067f080510000000000000000000000000000000000000000017e787540000000000000000000000000000000000000000025294758000000000000000000000000000000000000000000811df1622050000000000000000000000000000000000000000037721e4800000000000000000000000000000000000000000898606b010880000000000000000000000002c43c020000000002a7bb3c400000000000000000000000000000008000000000301583380000000000000000000000000000000000000000077e652700000000000000000000000000000000000000000021cfd36c40000000000000000000000000000000000000000043b3dff0000000000000000000000000000000000000000009654b86000000000000000000000000000000000000000001857c5044080000000000000000000000000f0a64a80000000013b5c8e46400000000000000000000000000000000000000000127d6724000000000000000000000000000000000000000002f4c0b980000000000000000000000000000000000000000007f45e662658442" },
    { i := 13, j := 13, k := 15, use := 0, tree := hex% "541fe59000000000000000000000000000000000000000000f6494f200000000000000000000000000000000000000000045e989b80509800000000000000000000000000000000000000000cfacc4c000000000000000000000000000000000000000000494a62719000000000000000000000000000000000000000003a46bc28000000000000000000000000000000000000000004b8636d08440000000000000000000000000c3da23400000000086437ae320000000000000000000000000000000000000000005b8d37632c2" }]

/-- The group 4: the cover of a box by its cells. -/
theorem g4_ok : boxOk run { e1 := 3, c1 := 3, e2 := 2, c2 := 1, e3 := 2, c3 := 2 } (1005) cells4 = true := by
  decide +kernel

/-- The cells of the group 5. -/
noncomputable def cells5 : List Cell :=
  [{ i := 4, j := 4, k := 6, use := 0, tree := 3 }]

/-- The group 5: the cover of a box by its cells. -/
theorem g5_ok : boxOk run { e1 := 2, c1 := 1, e2 := 2, c2 := 1, e3 := 2, c3 := 3 } (3) cells5 = true := by
  decide +kernel

/-- The cells of the group 6. -/
noncomputable def cells6 : List Cell :=
  [{ i := 3, j := 0, k := 2, use := 0, tree := 15070403604617 },
    { i := 4, j := 0, k := 2, use := 0, tree := hex% "3890e00000000000000013c6d368b681" }]

/-- The group 6: the cover of a box by its cells. -/
theorem g6_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 1, c3 := 2 } (60) cells6 = true := by
  decide +kernel

/-- The cells of the group 7. -/
noncomputable def cells7 : List Cell :=
  [{ i := 10, j := 10, k := 9, use := 0, tree := hex% "502b000000000000000000000000000000000000000002cad24e8886800000000000000000000000000000004000000013dc1b876000000000000000000000000000000000000000005b7b1e4c000000000000000000000000000000000000000004f8373d112" },
    { i := 10, j := 11, k := 9, use := 0, tree := hex% "c00000000000000000000000000000000000000000b8bc66220000000000000000000000000000000000000000003ba24d81b0800000000000000000000000000000000000000001d488eae2" },
    { i := 11, j := 3, k := 9, use := 0, tree := hex% "4b9b08000000000056565ec00000000000000000000000000ab820b000000000000001989b44000000000000000000000000000000000000000015aebe662" },
    { i := 3, j := 4, k := 9, use := 0, tree := 3674838554 },
    { i := 4, j := 0, k := 9, use := 0, tree := hex% "1d86a400000000000bcb66319" }]

/-- The group 7: the cover of a box by its cells. -/
theorem g7_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 2, c3 := 6 } (261956) cells7 = true := by
  decide +kernel

/-- The cells of the group 8. -/
noncomputable def cells8 : List Cell :=
  [{ i := 0, j := 0, k := 24, use := 0, tree := hex% "8000000008738c024" },
    { i := 0, j := 0, k := 25, use := 0, tree := 3 },
    { i := 0, j := 0, k := 26, use := 0, tree := 3 },
    { i := 0, j := 0, k := 27, use := 0, tree := 3 },
    { i := 0, j := 0, k := 28, use := 0, tree := 3 }]

/-- The group 8: the cover of a box by its cells. -/
theorem g8_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 2, c3 := 7 } (257774) cells8 = true := by
  decide +kernel

/-- The cells of the group 9. -/
noncomputable def cells9 : List Cell :=
  [{ i := 0, j := 1, k := 0, use := 0, tree := hex% "2b21009d80000000000000000000000016023d82c" }]

/-- The group 9: the cover of a box by its cells. -/
theorem g9_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 1, e3 := 1, c3 := 0 } (3) cells9 = true := by
  decide +kernel

/-- The cells of the group 10. -/
noncomputable def cells10 : List Cell :=
  [{ i := 10, j := 5, k := 5, use := 0, tree := hex% "8000000000000000000000001603734a4" }]

/-- The group 10: the cover of a box by its cells. -/
theorem g10_ok : boxOk run { e1 := 3, c1 := 0, e2 := 2, c2 := 2, e3 := 2, c3 := 2 } (3) cells10 = true := by
  decide +kernel

end N14Cert.Case0Pos

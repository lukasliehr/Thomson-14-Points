module

public import N14Cert.CapRrr.Run
public import N14.Box.MasterKernel
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.CapRrr

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The cells of the group 0. -/
noncomputable def cells0 : List Cell :=
  [{ i := 0, j := 0, k := 0, use := 0, tree := 3 }]

/-- The group 0: the cover of a box by its cells. -/
theorem g0_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 1, c3 := 0 } (3) cells0 = true := by
  decide +kernel

/-- The cells of the group 1. -/
noncomputable def cells1 : List Cell :=
  [{ i := 0, j := 0, k := 1, use := 0, tree := hex% "c0ad1000000000000000000000000000000000000000008a1643f00000000006bfb1c8db4da61b6d82982d00000000000000000000000000000000000000000000000000000000000fb7a8408b440000000000000000000000000000000000000000016f773000000000001b42e6368b41b088" }]

/-- The group 1: the cover of a box by its cells. -/
theorem g1_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 1, c3 := 1 } (3) cells1 = true := by
  decide +kernel

/-- The cells of the group 2. -/
noncomputable def cells2 : List Cell :=
  [{ i := 3, j := 3, k := 2, use := 0, tree := hex% "36db6d2200000000000000000000000000000000000000000078ce82000000000000003b1b691042" }]

/-- The group 2: the cover of a box by its cells. -/
theorem g2_ok : boxOk run { e1 := 2, c1 := 0, e2 := 2, c2 := 0, e3 := 1, c3 := 2 } (3) cells2 = true := by
  decide +kernel

/-- The cells of the group 3. -/
noncomputable def cells3 : List Cell :=
  [{ i := 3, j := 4, k := 7, use := 0, tree := 3 }]

/-- The group 3: the cover of a box by its cells. -/
theorem g3_ok : boxOk run { e1 := 2, c1 := 0, e2 := 2, c2 := 1, e3 := 2, c3 := 4 } (3) cells3 = true := by
  decide +kernel

/-- The cells of the group 4. -/
noncomputable def cells4 : List Cell :=
  [{ i := 10, j := 12, k := 8, use := 0, tree := 235609588872 }]

/-- The group 4: the cover of a box by its cells. -/
theorem g4_ok : boxOk run { e1 := 3, c1 := 0, e2 := 3, c2 := 2, e3 := 2, c3 := 5 } (3) cells4 = true := by
  decide +kernel

/-- The cells of the group 5. -/
noncomputable def cells5 : List Cell :=
  [{ i := 10, j := 13, k := 20, use := 0, tree := 3 },
    { i := 25, j := 13, k := 21, use := 0, tree := 898641 },
    { i := 26, j := 31, k := 47, use := 0, tree := 3 },
    { i := 58, j := 31, k := 48, use := 2, tree := hex% "36da0db6136d308a6db21a2db4c86c26d32db28361140a" },
    { i := 59, j := 68, k := 48, use := 2, tree := hex% "d80000000000910470000000000000000000000000000000000000000000000000000000000000000468b6d30d8443612" },
    { i := 59, j := 69, k := 100, use := 2, tree := 3 },
    { i := 125, j := 69, k := 101, use := 2, tree := hex% "37e010000000000000000000000000000000000000000000000000000000000000000400000000000738a100000000000000000000000000000000000000000000000000000000000000008d36820000000000153ddd000000000000000000000000000000000000000000000000000000000000000084000000000174d53c0000000000000000000000000000000000000000000000000000000000000002000000000004578ea000000000000000000000000000000000000000000000000000000000000000089b6132da0d16d94c32d2" },
    { i := 126, j := 69, k := 101, use := 2, tree := hex% "dc5d28000000000000000000000000000000000000000000000000000000000000000118000000000060d628000000000000000000000000000000000000000000000000000000000000000405a60000000000035c8e400000000000000000000000000000000000000000000000000000000000000020000000000040ab50000000000000000000000000000000000000000000000000000000000000000468b09b45a" },
    { i := 26, j := 32, k := 21, use := 0, tree := 3952591496907928194 }]

/-- The group 5: the cover of a box by its cells. -/
theorem g5_ok : boxOk run { e1 := 3, c1 := 0, e2 := 3, c2 := 3, e3 := 2, c3 := 5 } (16973773262) cells5 = true := by
  decide +kernel

/-- The cells of the group 6. -/
noncomputable def cells6 : List Cell :=
  [{ i := 11, j := 4, k := 8, use := 2, tree := hex% "36da6d049b6916da6d141b6d90db6d02d049b453681" }]

/-- The group 6: the cover of a box by its cells. -/
theorem g6_ok : boxOk run { e1 := 3, c1 := 1, e2 := 2, c2 := 1, e3 := 2, c3 := 5 } (3) cells6 = true := by
  decide +kernel

/-- The cells of the group 7. -/
noncomputable def cells7 : List Cell :=
  [{ i := 4, j := 3, k := 2, use := 0, tree := hex% "3068358000000000000000000000000000000000000000000404390000000000000000444a068" },
    { i := 4, j := 4, k := 2, use := 0, tree := hex% "da6586d26db21368b6d10d361a44000000000000000000000000000000000000000000228c5c000000000000000234db6426586880000000000000000000000000000000000000000001b4d900000000000000004650" }]

/-- The group 7: the cover of a box by its cells. -/
theorem g7_ok : boxOk run { e1 := 2, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 2 } (61) cells7 = true := by
  decide +kernel

/-- The cells of the group 8. -/
noncomputable def cells8 : List Cell :=
  [{ i := 25, j := 10, k := 22, use := 0, tree := 5 }]

/-- The group 8: the cover of a box by its cells. -/
theorem g8_ok : boxOk run { e1 := 4, c1 := 0, e2 := 3, c2 := 0, e3 := 3, c3 := 12 } (3) cells8 = true := by
  decide +kernel

/-- The cells of the group 9. -/
noncomputable def cells9 : List Cell :=
  [{ i := 26, j := 25, k := 22, use := 0, tree := 5 }]

/-- The group 9: the cover of a box by its cells. -/
theorem g9_ok : boxOk run { e1 := 4, c1 := 1, e2 := 4, c2 := 0, e3 := 3, c3 := 12 } (3) cells9 = true := by
  decide +kernel

/-- The cells of the group 10. -/
noncomputable def cells10 : List Cell :=
  [{ i := 26, j := 26, k := 49, use := 0, tree := 3 }]

/-- The group 10: the cover of a box by its cells. -/
theorem g10_ok : boxOk run { e1 := 4, c1 := 1, e2 := 4, c2 := 1, e3 := 4, c3 := 24 } (3) cells10 = true := by
  decide +kernel

/-- The cells of the group 11. -/
noncomputable def cells11 : List Cell :=
  [{ i := 58, j := 58, k := 50, use := 1, tree := 5 },
    { i := 58, j := 59, k := 104, use := 1, tree := 3 },
    { i := 123, j := 59, k := 105, use := 0, tree := 362185348 },
    { i := 124, j := 125, k := 105, use := 1, tree := 165249900 },
    { i := 124, j := 126, k := 214, use := 1, tree := hex% "36db6d90886886c0adb20000000000000000000000000000000000000000000000000000000000000000000000000003c4202220508b6db6c84434c8000000000000000000000000000000000000000000000000000000000000000000000000005a54f98c0000000000000000000000000000000000000000000000000000000000000000000000000004f99e345b0d361b2d9088000000000000000000000000000000000000000000000000000000000000000000000000000ac5a68000000000000000000000000000000000000000000000000000000000000000000000000000fa40902000000000000000000000000000000000000000000000000000000000000000000000000003138ff8426d369b45b21b08b6cb09b45b2d90d36c86cb6d10886d869909b0d32c369b45b0d368844369b45b200000000000000000000000000000000000000000000000000000000000000000000000000028414226d32da64345b61361b2c22db6584434c8442" },
    { i := 124, j := 126, k := 215, use := 1, tree := hex% "15f201c0000000000000000000000000000000000000000000000000000000000000000000000000024e4d680000000000000000000000000000000000000000000000000000000000000000000000000024f90162" }]

/-- The group 11: the cover of a box by its cells. -/
theorem g11_ok : boxOk run { e1 := 5, c1 := 2, e2 := 4, c2 := 1, e3 := 4, c3 := 25 } (4119789) cells11 = true := by
  decide +kernel

/-- The cells of the group 12. -/
noncomputable def cells12 : List Cell :=
  [{ i := 59, j := 58, k := 50, use := 1, tree := hex% "2b800000000000000000000000000000000000000000329a6500000000003760184" }]

/-- The group 12: the cover of a box by its cells. -/
theorem g12_ok : boxOk run { e1 := 5, c1 := 3, e2 := 5, c2 := 2, e3 := 4, c3 := 25 } (3) cells12 = true := by
  decide +kernel

/-- The cells of the group 13. -/
noncomputable def cells13 : List Cell :=
  [{ i := 125, j := 59, k := 104, use := 1, tree := 61763652010709130 },
    { i := 126, j := 59, k := 104, use := 1, tree := hex% "3000000000000000000000000000000000000000000000000000000000057c2c8000000000000000b8db6c16816da6000000000000000000000000000000000000000000000000000000000002a3f9000000000000000021400000000000000000000000000000000000000000000000000000000000a1ab60000000000000001000000000000000000000000000000000000000000000000000000000001588fc000000000000000220d961b2da6426c32d028a" }]

/-- The group 13: the cover of a box by its cells. -/
theorem g13_ok : boxOk run { e1 := 5, c1 := 3, e2 := 5, c2 := 3, e3 := 5, c3 := 50 } (60) cells13 = true := by
  decide +kernel

end N14Cert.CapRrr

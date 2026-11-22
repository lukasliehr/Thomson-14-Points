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

/-- The cells of the group 0. -/
noncomputable def cells0 : List Cell :=
  [{ i := 10, j := 10, k := 0, use := 0, tree := hex% "1d02800000000000000c8000000000000000000000000000000000000001d79b5042c00000000963871f50000000000000000000000000000000000000000826d8cab84000000000000009c000000000000000000000000000000000000000f79a5091e0000000000000000000000000000000000000000000000000000000009661e52c888000000044207c6780000000000000000000000001249aba800000004541b318c000000000000000000000000000000000000000000000000000000008156e9b68000000012cd863a00000000000000000000000000000000000000001044af16b000000002710cd2200000000000000000000000000000000000000001ee6e71821000000009cf4f00f00000000000000000000000000000037000000007829ce778134420290280ea0e800000004a76d51280000000000000000000000000000000000000003d5817b3c00000000b52c6f9d00000000000000000000000000000000000000000000000081941d000000007a33e49c00000000000000000000000000000000000000008efea493800000001247919140000000000000000000000000000000000000000e8ffd0bd0a01d44000000026ebb20c000000000000000000000000014e97ad400000001676bf022034875000000005dcdfd368000000000000000000000000000000080000000166b851642000000000000000000000000000000000000000000000000400000002deb361d200000000000000000000000000000000000000000000002e000000003909fcbec0d2" },
    { i := 10, j := 11, k := 0, use := 0, tree := hex% "16a893ea40000000000000000000000000000000000000000471737251a" },
    { i := 11, j := 3, k := 0, use := 0, tree := hex% "16ea0b0d8000000000000000000000000000000b6000000002a7317cd1a" }]

/-- The group 0: the cover of a box by its cells. -/
theorem g0_ok : boxOk run { e1 := 2, c1 := 0, e2 := 2, c2 := 0, e3 := 3, c3 := 14 } (1012) cells0 = true := by
  decide +kernel

/-- The cells of the group 1. -/
noncomputable def cells1 : List Cell :=
  [{ i := 3, j := 4, k := 0, use := 0, tree := hex% "142c908d80000000000000000000000000000000000000000000001a5000000002017ecf2c0000000000000000000000000000000000000000923b82360000000000000000000000000000000000000000000000000000000002d10e9e58800000002e0dc5bcc00000000000000000000000000000000000000000000003a0" }]

/-- The group 1: the cover of a box by its cells. -/
theorem g1_ok : boxOk run { e1 := 2, c1 := 0, e2 := 2, c2 := 1, e3 := 3, c3 := 14 } (3) cells1 = true := by
  decide +kernel

/-- The cells of the group 2. -/
noncomputable def cells2 : List Cell :=
  [{ i := 4, j := 0, k := 0, use := 0, tree := hex% "3eafe12180000000000000000000000004316db68000000003277f22c00000000b425ebf40000000000000000000000000000000000000000000000008d1" }]

/-- The group 2: the cover of a box by its cells. -/
theorem g2_ok : boxOk run { e1 := 2, c1 := 1, e2 := 1, c2 := 0, e3 := 3, c3 := 14 } (3) cells2 = true := by
  decide +kernel

/-- The cells of the group 3. -/
noncomputable def cells3 : List Cell :=
  [{ i := 0, j := 0, k := 1, use := 0, tree := 3 },
    { i := 0, j := 0, k := 2, use := 0, tree := 3 },
    { i := 0, j := 0, k := 3, use := 0, tree := 3 },
    { i := 0, j := 0, k := 4, use := 0, tree := 3 }]

/-- The group 3: the cover of a box by its cells. -/
theorem g3_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 3, c3 := 15 } (16110) cells3 = true := by
  decide +kernel

/-- The cells of the group 4. -/
noncomputable def cells4 : List Cell :=
  [{ i := 10, j := 5, k := 0, use := 0, tree := hex% "e2fca8ae00000000000000000000000000000000000000004a5ab29500a40a00000000224e96eb80000000000000000000000000000000000000000941e7922000000004f184d3080000000000000000000000000000000000000000dbdf6bcc01d400000000000000000000000000000000000000000000000000000000109cf18d22" },
    { i := 11, j := 14, k := 0, use := 0, tree := hex% "1416996aa0000000000000000000000000000000000000000000000351a" },
    { i := 11, j := 15, k := 0, use := 0, tree := hex% "1d00000000a459406100000000000000000000000000000000000000000b5cf84588000000025e0edbf8000000000000000000000000000000000000000041860c1200ea0e8000000051f02896800000000000000000000000000000000000000000000001c00000000acdd9b7d0000000000000000000000000000000000000000050d2a8d80000000157ce71ca00000000000000000000000000000000000000000e7fd3910344000000029c6f3d1000000000000000000000000000000000000000000000000a041d4000000000000000000000000000000000000000000000000000000000368286122" },
    { i := 3, j := 6, k := 0, use := 0, tree := hex% "140000000327c4635000000000000000000000000000000000000000006e3eca8607400000002a5872d6800000000000000000000000000000000000000001cb5381200000000556c77e2000000000000000000000000000000000000000001845d9e4083a800000002cbd73ecc00000000000000000000000000000000000000001438efca1000000000000000000000000000000000000000000000000000000000221ca8cf10" }]

/-- The group 4: the cover of a box by its cells. -/
theorem g4_ok : boxOk run { e1 := 2, c1 := 0, e2 := 1, c2 := 1, e3 := 3, c3 := 14 } (16241) cells4 = true := by
  decide +kernel

/-- The cells of the group 5. -/
noncomputable def cells5 : List Cell :=
  [{ i := 4, j := 1, k := 0, use := 0, tree := hex% "1541bbda0000000000000000000000000000000000000000000000001000000002aaf4a2f400000000000000000000000000000000000000000000000210e8000000054c88b9d000000000000000000000000000000000000000000000000441d00000000a94d3f270000000000000000000000000000000000000000000000008880ea00000000b4669b5b00000000000000000000000000000000000000000000001185a" }]

/-- The group 5: the cover of a box by its cells. -/
theorem g5_ok : boxOk run { e1 := 2, c1 := 1, e2 := 1, c2 := 1, e3 := 3, c3 := 14 } (3) cells5 = true := by
  decide +kernel

/-- The cells of the group 6. -/
noncomputable def cells6 : List Cell :=
  [{ i := 0, j := 1, k := 1, use := 0, tree := 13342655948 },
    { i := 0, j := 1, k := 2, use := 0, tree := 23005293036 },
    { i := 0, j := 1, k := 3, use := 0, tree := 31021534108 },
    { i := 0, j := 1, k := 4, use := 0, tree := 3 }]

/-- The group 6: the cover of a box by its cells. -/
theorem g6_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 1, e3 := 3, c3 := 15 } (16110) cells6 = true := by
  decide +kernel

/-- The cells of the group 7. -/
noncomputable def cells7 : List Cell :=
  [{ i := 0, j := 2, k := 0, use := 0, tree := hex% "14000000032a189b5000000000000000000000000000000000000000000351c2160" },
    { i := 0, j := 2, k := 1, use := 0, tree := 5 },
    { i := 0, j := 2, k := 2, use := 0, tree := 5 },
    { i := 0, j := 2, k := 3, use := 0, tree := 5 },
    { i := 0, j := 2, k := 4, use := 0, tree := 5 }]

/-- The group 7: the cover of a box by its cells. -/
theorem g7_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 1, c3 := 3 } (4124398) cells7 = true := by
  decide +kernel

/-- The cells of the group 8. -/
noncomputable def cells8 : List Cell :=
  [{ i := 0, j := 9, k := 0, use := 0, tree := 5 },
    { i := 0, j := 9, k := 1, use := 0, tree := 5 },
    { i := 0, j := 9, k := 2, use := 0, tree := 5 },
    { i := 0, j := 9, k := 3, use := 0, tree := 5 },
    { i := 0, j := 9, k := 4, use := 0, tree := 5 }]

/-- The group 8: the cover of a box by its cells. -/
theorem g8_ok : boxOk run { e1 := 1, c1 := 0, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (4124398) cells8 = true := by
  decide +kernel

end N14Cert.Case0Close

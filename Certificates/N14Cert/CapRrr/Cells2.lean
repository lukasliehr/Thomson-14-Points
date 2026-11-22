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

/-- The cells of the group 22. -/
noncomputable def cells22 : List Cell :=
  [{ i := 125, j := 60, k := 104, use := 1, tree := hex% "db45b6990db09b65845b4d86cb64221365b21b4cb08a" },
    { i := 126, j := 60, k := 104, use := 1, tree := hex% "db4c869b2da6436c845b4d868b6d84436c34584d868a" },
    { i := 59, j := 60, k := 105, use := 1, tree := hex% "36da2da6db0d10db45b4da21109961a" },
    { i := 59, j := 61, k := 50, use := 0, tree := 61187499080913050 }]

/-- The group 22: the cover of a box by its cells. -/
theorem g22_ok : boxOk run { e1 := 5, c1 := 3, e2 := 4, c2 := 2, e3 := 4, c3 := 25 } (16329) cells22 = true := by
  decide +kernel

/-- The cells of the group 23. -/
noncomputable def cells23 : List Cell :=
  [{ i := 26, j := 28, k := 22, use := 0, tree := hex% "369b45b4cb41b4cb0d2" }]

/-- The group 23: the cover of a box by its cells. -/
theorem g23_ok : boxOk run { e1 := 4, c1 := 1, e2 := 4, c2 := 3, e3 := 3, c3 := 12 } (3) cells23 = true := by
  decide +kernel

/-- The cells of the group 24. -/
noncomputable def cells24 : List Cell :=
  [{ i := 10, j := 11, k := 23, use := 0, tree := 736605324826 }]

/-- The group 24: the cover of a box by its cells. -/
theorem g24_ok : boxOk run { e1 := 3, c1 := 0, e2 := 3, c2 := 1, e3 := 3, c3 := 13 } (3) cells24 = true := by
  decide +kernel

/-- The cells of the group 25. -/
noncomputable def cells25 : List Cell :=
  [{ i := 11, j := 10, k := 9, use := 1, tree := hex% "d068341a0d06b6000000000000000000000000000000000000000000000000000000000005db5800000000000000011020000000000000000000000000000000000000000000000000000000000748690000000000000000110200000000000000000000000000000000000000000000000000000000003a5a5c0000000000000005100000000000000000000000000000000000000000000000000000000000894324000000000000000088800000000000000000000000000000000000000000000000000000000073c1628000000000000048c40d040000000000000000000000000000000000000000000000000000000002473f2400000000059945522" }]

/-- The group 25: the cover of a box by its cells. -/
theorem g25_ok : boxOk run { e1 := 3, c1 := 1, e2 := 3, c2 := 0, e3 := 2, c3 := 6 } (3) cells25 = true := by
  decide +kernel

/-- The cells of the group 26. -/
noncomputable def cells26 : List Cell :=
  [{ i := 60, j := 60, k := 102, use := 0, tree := 3 },
    { i := 127, j := 60, k := 103, use := 0, tree := 965039866318986 },
    { i := 128, j := 60, k := 103, use := 0, tree := hex% "db6d02d10000000000000000000000000000000000000000000d64e200000000000000008c0000000000000000000000000000000000000000001202c4000000000000000206cb0d36196c360a05b0cb650000000000000000000000000000000000000000000298cb800000000000000040d869828a" },
    { i := 60, j := 61, k := 49, use := 0, tree := hex% "db2d96d36d908869b4436586c26d16da2db6110d3212" },
    { i := 61, j := 60, k := 49, use := 0, tree := hex% "3068341ac00000000000000000000000000000000000000000006a31c0000000000000002205a068200000000000000000000000000000000000000000015a99c000000000000000112" },
    { i := 61, j := 61, k := 49, use := 0, tree := hex% "db440000000000000000000000000000000000000000000f323400000000000000023688680000000000000000000000000000000000000000001bc3240000000000000002369b0d84430000000000000000000000000000000000000000000188e3000000000000000085b4c84db0880000000000000000000000000000000000000000002a927800000000000000040d2" }]

/-- The group 26: the cover of a box by its cells. -/
theorem g26_ok : boxOk run { e1 := 4, c1 := 2, e2 := 4, c2 := 2, e3 := 4, c3 := 24 } (4062436) cells26 = true := by
  decide +kernel

/-- The cells of the group 27. -/
noncomputable def cells27 : List Cell :=
  [{ i := 27, j := 27, k := 50, use := 1, tree := hex% "db6da21a218000000000000000000000000000000000000000000000000000000000064ad4000000000000000042db4cb699098000000000000000000000000000000000000000000000000000000000022416800000000000000042da6d844368000000000000000000000000000000000000000000000000000000000031273c000000000000000216d321109900000000000000000000000000000000000000000000000000000000006529f9000000000000000081a" }]

/-- The group 27: the cover of a box by its cells. -/
theorem g27_ok : boxOk run { e1 := 4, c1 := 2, e2 := 4, c2 := 2, e3 := 4, c3 := 25 } (3) cells27 = true := by
  decide +kernel

/-- The cells of the group 28. -/
noncomputable def cells28 : List Cell :=
  [{ i := 27, j := 28, k := 22, use := 0, tree := hex% "361a6586d32d869909a" }]

/-- The group 28: the cover of a box by its cells. -/
theorem g28_ok : boxOk run { e1 := 4, c1 := 2, e2 := 4, c2 := 3, e3 := 3, c3 := 12 } (3) cells28 = true := by
  decide +kernel

/-- The cells of the group 29. -/
noncomputable def cells29 : List Cell :=
  [{ i := 28, j := 11, k := 22, use := 0, tree := hex% "6cf1e20000000000000001000000000000000000000000000000000000000000020e30c000000000000000234c034a6da61945a" }]

/-- The group 29: the cover of a box by its cells. -/
theorem g29_ok : boxOk run { e1 := 4, c1 := 3, e2 := 3, c2 := 1, e3 := 3, c3 := 12 } (3) cells29 = true := by
  decide +kernel

/-- The cells of the group 30. -/
noncomputable def cells30 : List Cell :=
  [{ i := 11, j := 11, k := 23, use := 0, tree := 3 }]

/-- The group 30: the cover of a box by its cells. -/
theorem g30_ok : boxOk run { e1 := 3, c1 := 1, e2 := 3, c2 := 1, e3 := 3, c3 := 13 } (3) cells30 = true := by
  decide +kernel

/-- The cells of the group 31. -/
noncomputable def cells31 : List Cell :=
  [{ i := 10, j := 12, k := 9, use := 0, tree := hex% "da6d06d309b6c00000000000000000000000000000000000000000000000000000000002cb532000000000000000000000000000000000000000000000000000000000002bb1bc4110d36c345a6da2d045b69b41b4c141a" },
    { i := 56, j := 31, k := 49, use := 0, tree := hex% "db6000000000000000000000000000000000000000000000000000000000010a11b00000000000000000000000000000000000000000000000000000000000256a8e209b00000000000000000000000000000000000000000000000000000000000826be811613600000000000000000000000000000000000000000000000000000000001019531308a" },
    { i := 57, j := 31, k := 49, use := 0, tree := hex% "365a6c34da2d06d361969b0d368a05b4c32d2" },
    { i := 25, j := 31, k := 50, use := 0, tree := hex% "d800000000000000000000000000000000000000000000000000000000008a615c00000000000000000000000000000000000000000000000000000000000b5bbc8c00000000000000000000000000000000000000000000000000000000002f47be000000000000000000000000000000000000000000000000000000000004cea1c40a0ca61a" },
    { i := 25, j := 32, k := 22, use := 0, tree := 57259034 },
    { i := 26, j := 13, k := 22, use := 0, tree := hex% "36db6136c22136da6422c329a" },
    { i := 10, j := 13, k := 23, use := 0, tree := 3 },
    { i := 11, j := 4, k := 9, use := 0, tree := 235588563610 }]

/-- The group 31: the cover of a box by its cells. -/
theorem g31_ok : boxOk run { e1 := 2, c1 := 0, e2 := 2, c2 := 1, e3 := 2, c3 := 6 } (1073685684) cells31 = true := by
  decide +kernel

/-- The cells of the group 32. -/
noncomputable def cells32 : List Cell :=
  [{ i := 4, j := 0, k := 9, use := 0, tree := hex% "909a06000000000000000719" }]

/-- The group 32: the cover of a box by its cells. -/
theorem g32_ok : boxOk run { e1 := 2, c1 := 1, e2 := 1, c2 := 0, e3 := 2, c3 := 6 } (3) cells32 = true := by
  decide +kernel

/-- The cells of the group 33. -/
noncomputable def cells33 : List Cell :=
  [{ i := 0, j := 0, k := 24, use := 0, tree := hex% "2a00000000047c49734000000000000001500000000000000000000000000000000000000000bb3ff7d8000000000000000000000000000000000000000006eb0b68000000001b8635ff000000000000000000000000000000000000000000000000000000000465e7d8a0000000003767753800000000000000000000000000000000000000009b480f5c6190ea000000000678c4fe000000000000000000000000000000000000000017320c5d810000000000000000000000000000000000000000000000000000000009154f8bc0280000000039270ba80000000000000000000000000000000000000000a1369fb42000000000f92a9a400000000000000000000000000c8c61200000000284da7ed03a000000000e475a680000000000000000000000000000000000000000259812751101d405205088000000000000000000000000000000000000000000000000000000000d34ad5f8886580ea" }]

/-- The group 33: the cover of a box by its cells. -/
theorem g33_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 0, e3 := 2, c3 := 7 } (62) cells33 = true := by
  decide +kernel

/-- The cells of the group 34. -/
noncomputable def cells34 : List Cell :=
  [{ i := 0, j := 1, k := 0, use := 0, tree := hex% "f2f7d70000000000000000000000000047f0acc" }]

/-- The group 34: the cover of a box by its cells. -/
theorem g34_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 1, e3 := 1, c3 := 0 } (3) cells34 = true := by
  decide +kernel

end N14Cert.CapRrr

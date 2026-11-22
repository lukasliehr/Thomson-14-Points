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

/-- The cells of the group 245. -/
noncomputable def cells245 : List Cell :=
  [{ i := 2, j := 1, k := 0, use := 0, tree := hex% "6cac5000000000003cdfc280000000003891eac" }]

/-- The group 245: the cover of a box by its cells. -/
theorem g245_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 0 } (3) cells245 = true := by
  decide +kernel

/-- The cells of the group 246. -/
noncomputable def cells246 : List Cell :=
  [{ i := 2, j := 1, k := 1, use := 0, tree := hex% "8305200000000001060a400000000000000004" }]

/-- The group 246: the cover of a box by its cells. -/
theorem g246_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 1 } (3) cells246 = true := by
  decide +kernel

/-- The cells of the group 247. -/
noncomputable def cells247 : List Cell :=
  [{ i := 2, j := 1, k := 2, use := 0, tree := hex% "3b80e400000000000000004" }]

/-- The group 247: the cover of a box by its cells. -/
theorem g247_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 2 } (3) cells247 = true := by
  decide +kernel

/-- The cells of the group 248. -/
noncomputable def cells248 : List Cell :=
  [{ i := 2, j := 1, k := 9, use := 0, tree := hex% "1daaaa0000000000000002c" },
    { i := 2, j := 1, k := 24, use := 0, tree := hex% "80000000000000000000000000c87174000000000007aa10c" }]

/-- The group 248: the cover of a box by its cells. -/
theorem g248_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 3 } (1006) cells248 = true := by
  decide +kernel

/-- The cells of the group 249. -/
noncomputable def cells249 : List Cell :=
  [{ i := 2, j := 2, k := 1, use := 0, tree := hex% "3b80e4000000000000000000000000000000004" }]

/-- The group 249: the cover of a box by its cells. -/
theorem g249_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 1 } (3) cells249 = true := by
  decide +kernel

/-- The cells of the group 250. -/
noncomputable def cells250 : List Cell :=
  [{ i := 2, j := 2, k := 2, use := 0, tree := 3 }]

/-- The group 250: the cover of a box by its cells. -/
theorem g250_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 2 } (3) cells250 = true := by
  decide +kernel

/-- The cells of the group 251. -/
noncomputable def cells251 : List Cell :=
  [{ i := 7, j := 2, k := 9, use := 0, tree := hex% "36d36db6d10896d328a" },
    { i := 8, j := 7, k := 9, use := 0, tree := hex% "30000000000000000000000000000000000000000001097f90000000000000000800000000000000000000000000000000000000000025b202000000000000000112" },
    { i := 20, j := 8, k := 9, use := 0, tree := 964916383946378 },
    { i := 21, j := 8, k := 9, use := 2048, tree := hex% "36db6cb40b69b41b40000000000cf514800000000000000000000000000000000000000000000000000000000000000010000000000141880c000000000000000000000000000000000000000000039048000000000000000206d36816c328140b4400000000000000000000000000000000000000000000000000000000001ede54000000000000000236c168a" },
    { i := 2, j := 2, k := 24, use := 0, tree := 13850 }]

/-- The group 251: the cover of a box by its cells. -/
theorem g251_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 3 } (4125554) cells251 = true := by
  decide +kernel

/-- The cells of the group 252. -/
noncomputable def cells252 : List Cell :=
  [{ i := 2, j := 9, k := 2, use := 0, tree := hex% "1f03d4800000000000000000000000000000004" }]

/-- The group 252: the cover of a box by its cells. -/
theorem g252_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 3, e3 := 1, c3 := 2 } (61) cells252 = true := by
  decide +kernel

/-- The cells of the group 253. -/
noncomputable def cells253 : List Cell :=
  [{ i := 7, j := 9, k := 9, use := 0, tree := hex% "db6436100000000000000000000000000117de28000000000000000000000000000000042000000000000000000000000000e246480000000000000000000000000000000226db6ca0d828345b6db61108b48000000000000000000000000002224700000000000000000000000000000001a1" },
    { i := 8, j := 9, k := 9, use := 0, tree := hex% "36996000000000000000000000000000528e900000000000000000000000000000000226d94db05a0d16cb48000000000000000000000000021f7d70000000000000000000000000000000021" },
    { i := 2, j := 9, k := 24, use := 0, tree := 3 },
    { i := 2, j := 24, k := 9, use := 0, tree := 3 },
    { i := 2, j := 24, k := 24, use := 0, tree := 3 },
    { i := 2, j := 55, k := 24, use := 0, tree := 3 }]

/-- The group 253: the cover of a box by its cells. -/
theorem g253_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 3, e3 := 1, c3 := 3 } (4359290551241) cells253 = true := by
  decide +kernel

/-- The cells of the group 254. -/
noncomputable def cells254 : List Cell :=
  [{ i := 9, j := 2, k := 1, use := 0, tree := hex% "42f41580000000001bcbcf80000000001010b3c" }]

/-- The group 254: the cover of a box by its cells. -/
theorem g254_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 1 } (60) cells254 = true := by
  decide +kernel

/-- The cells of the group 255. -/
noncomputable def cells255 : List Cell :=
  [{ i := 9, j := 2, k := 2, use := 0, tree := hex% "1f03d480000000000000004" }]

/-- The group 255: the cover of a box by its cells. -/
theorem g255_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 2 } (60) cells255 = true := by
  decide +kernel

/-- The cells of the group 256. -/
noncomputable def cells256 : List Cell :=
  [{ i := 9, j := 2, k := 9, use := 0, tree := hex% "d0683400000000000000000000000000000000000000000008e6d40000000000000002345a040000000000000000000000000000000000000000005ea50800000000000000022068" },
    { i := 9, j := 2, k := 24, use := 0, tree := 3 }]

/-- The group 256: the cover of a box by its cells. -/
theorem g256_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 3 } (16312) cells256 = true := by
  decide +kernel

/-- The cells of the group 257. -/
noncomputable def cells257 : List Cell :=
  [{ i := 9, j := 9, k := 2, use := 0, tree := hex% "d078d00000000000683c680000000000000004" },
    { i := 24, j := 9, k := 2, use := 0, tree := 3 }]

/-- The group 257: the cover of a box by its cells. -/
theorem g257_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 3, e3 := 1, c3 := 2 } (258548) cells257 = true := by
  decide +kernel

/-- The cells of the group 258. -/
noncomputable def cells258 : List Cell :=
  [{ i := 9, j := 9, k := 9, use := 0, tree := hex% "8c97800000000002cd9c00000000000000004000000000000000000000000000773d8000000000000000000000000000000008da6d368b69b44221a658" },
    { i := 9, j := 9, k := 24, use := 0, tree := 3 },
    { i := 9, j := 24, k := 9, use := 0, tree := 3 },
    { i := 9, j := 24, k := 24, use := 0, tree := 3 },
    { i := 9, j := 55, k := 24, use := 0, tree := 3 }]

/-- The group 258: the cover of a box by its cells. -/
theorem g258_ok : boxOk run { e1 := 2, c1 := 6, e2 := 1, c2 := 3, e3 := 1, c3 := 3 } (272455659449) cells258 = true := by
  decide +kernel

/-- The cells of the group 259. -/
noncomputable def cells259 : List Cell :=
  [{ i := 24, j := 9, k := 9, use := 0, tree := 3 },
    { i := 24, j := 9, k := 24, use := 0, tree := 3 }]

/-- The group 259: the cover of a box by its cells. -/
theorem g259_ok : boxOk run { e1 := 2, c1 := 7, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (260338) cells259 = true := by
  decide +kernel

/-- The cells of the group 260. -/
noncomputable def cells260 : List Cell :=
  [{ i := 24, j := 24, k := 9, use := 0, tree := 3 },
    { i := 55, j := 24, k := 9, use := 0, tree := 3 }]

/-- The group 260: the cover of a box by its cells. -/
theorem g260_ok : boxOk run { e1 := 2, c1 := 7, e2 := 2, c2 := 7, e3 := 2, c3 := 6 } (258548) cells260 = true := by
  decide +kernel

/-- The cells of the group 261. -/
noncomputable def cells261 : List Cell :=
  [{ i := 24, j := 24, k := 24, use := 0, tree := hex% "c00000002d79f6a940000000000000008000000000000001000000000000000020" },
    { i := 24, j := 55, k := 24, use := 0, tree := hex% "143d3430a00000000bb3b9ef1800000000000000000000000000000004" }]

/-- The group 261: the cover of a box by its cells. -/
theorem g261_ok : boxOk run { e1 := 3, c1 := 14, e2 := 2, c2 := 7, e3 := 2, c3 := 7 } (259833) cells261 = true := by
  decide +kernel

end N14Cert.CapRrr

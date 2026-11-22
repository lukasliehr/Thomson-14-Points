module

public import N14Cert.CapPrr.Run
public import N14.Box.MasterKernel
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.CapPrr

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The cells of the group 252. -/
noncomputable def cells252 : List Cell :=
  [{ i := 9, j := 9, k := 0, use := 0, tree := hex% "32800000000ed36fda4" },
    { i := 9, j := 24, k := 0, use := 0, tree := 5 },
    { i := 24, j := 9, k := 0, use := 0, tree := 5 },
    { i := 24, j := 24, k := 0, use := 0, tree := 5 },
    { i := 55, j := 24, k := 0, use := 0, tree := 5 }]

/-- The group 252: the cover of a box by its cells. -/
theorem g252_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 3, e3 := 1, c3 := 0 } (271108218740) cells252 = true := by
  decide +kernel

/-- The cells of the group 253. -/
noncomputable def cells253 : List Cell :=
  [{ i := 22, j := 22, k := 14, use := 0, tree := hex% "134ca51b2d909b6db41941b05100000000000000000000000000000000000000000000000000000000005ce54a00000000000000038c8" },
    { i := 22, j := 22, k := 15, use := 0, tree := hex% "361a6db0ca0db2d86502db051000000000000000000000000000000000000000000000000000000000015a38b00000000000000008c8" },
    { i := 22, j := 23, k := 5, use := 0, tree := 3 },
    { i := 23, j := 9, k := 5, use := 0, tree := 3 },
    { i := 9, j := 9, k := 6, use := 0, tree := hex% "619018000000000000000c6cb4da21b6da05a0c9000000000000000000000000000000000000000000000000000000000008fc0700000000000000098c8" },
    { i := 9, j := 24, k := 1, use := 0, tree := hex% "36c000000000000000000000000000000000000000015ebe4ec0000000000000000000000000000001e3000000000000000000000000000000000000000009006ed20000000000000000000000000000000484328054b029602" }]

/-- The group 253: the cover of a box by its cells. -/
theorem g253_ok : boxOk run { e1 := 2, c1 := 6, e2 := 1, c2 := 3, e3 := 1, c3 := 1 } (65011273) cells253 = true := by
  decide +kernel

/-- The cells of the group 254. -/
noncomputable def cells254 : List Cell :=
  [{ i := 24, j := 9, k := 1, use := 0, tree := hex% "2b8bf4e50000000009b250f2c" },
    { i := 24, j := 24, k := 1, use := 0, tree := 5 },
    { i := 55, j := 24, k := 1, use := 0, tree := 5 }]

/-- The group 254: the cover of a box by its cells. -/
theorem g254_ok : boxOk run { e1 := 2, c1 := 7, e2 := 1, c2 := 3, e3 := 1, c3 := 1 } (66188529) cells254 = true := by
  decide +kernel

/-- The cells of the group 255. -/
noncomputable def cells255 : List Cell :=
  [{ i := 22, j := 9, k := 7, use := 0, tree := hex% "36d32c26d06da6584c00000000000000000000000000000000000000000000000000000000001972cc0000000000000002205a6db4590d1" },
    { i := 23, j := 9, k := 7, use := 0, tree := hex% "afcfc8000000000000000469b68000000000000000000000000000000000000000000000000000000000020a362000000000000000046d86902d32c1" },
    { i := 9, j := 9, k := 8, use := 0, tree := hex% "db688658680000000000000000000000000000000000000000000000000000000000fcb630000000000000000216cb4c32c86db2132c34000000000000000000000000000000000000000000000000000000000040012a00000000000000010b61969b442658" },
    { i := 9, j := 24, k := 2, use := 0, tree := hex% "3000000000000000000000000000000000000000005d448c3000000000000000000000000000000058ca000000000000000000000000000000000000000006f41cc6000000000000000000000000000000008cb00000000000000000000000000000000000000000a488aee000000000000000000000000000000008000000000000000000000000000000000000000010d49f020000000000000000000000000000000102a41600000000000000000000000000000000000000000ffd7bd00000000000000000000000000000000102a40000000000000000000000000000000000000000269ed37400000000000000000000000000000002200000000000000000000000000000000000000000842de8800000000000000000000000000000000800000000000000000000000000000000000000001090db6e000000000000000000000000000000010000000000000000000000000000000000000000003f2e62e00000000000000000000000000000000441520a650682a5854b0a90c2a50" }]

/-- The group 255: the cover of a box by its cells. -/
theorem g255_ok : boxOk run { e1 := 2, c1 := 6, e2 := 1, c2 := 3, e3 := 1, c3 := 2 } (253897) cells255 = true := by
  decide +kernel

/-- The cells of the group 256. -/
noncomputable def cells256 : List Cell :=
  [{ i := 24, j := 9, k := 2, use := 0, tree := hex% "7e0001500000000000000074" },
    { i := 24, j := 24, k := 2, use := 0, tree := hex% "36152800000000000000000000000000000000000000011a0f7d58000000010dda6f1800000000000001b60548" },
    { i := 55, j := 24, k := 2, use := 0, tree := 53417 }]

/-- The group 256: the cover of a box by its cells. -/
theorem g256_ok : boxOk run { e1 := 2, c1 := 7, e2 := 1, c2 := 3, e3 := 1, c3 := 2 } (66188529) cells256 = true := by
  decide +kernel

/-- The cells of the group 257. -/
noncomputable def cells257 : List Cell :=
  [{ i := 49, j := 49, k := 49, use := 0, tree := hex% "db2d90c000000000000000000000000000000000000000000000000000000000015f8f8000000000000000216cb4000000000000000000000000000000000000000000000000000000000000b12e0000000000000001186000000000000000000000000000000000000000000000000000000000001ed4e00000000000000010b6ca6d84422126da6510000000000000000000000000000000000000000000000000000000000108fd200000000000000008c8" },
    { i := 49, j := 49, k := 50, use := 0, tree := hex% "db6db6c221109961a" },
    { i := 49, j := 50, k := 22, use := 0, tree := 218 },
    { i := 50, j := 22, k := 22, use := 0, tree := hex% "48fb6c80000000000000004" },
    { i := 22, j := 22, k := 23, use := 0, tree := 3 },
    { i := 22, j := 23, k := 9, use := 0, tree := 3 },
    { i := 23, j := 9, k := 9, use := 0, tree := 3 },
    { i := 9, j := 9, k := 24, use := 0, tree := 12522 },
    { i := 9, j := 24, k := 9, use := 0, tree := hex% "658c740000000000000000000000000000000004" },
    { i := 9, j := 24, k := 24, use := 0, tree := 12522 }]

/-- The group 257: the cover of a box by its cells. -/
theorem g257_ok : boxOk run { e1 := 2, c1 := 6, e2 := 1, c2 := 3, e3 := 1, c3 := 3 } (17908225844154953) cells257 = true := by
  decide +kernel

end N14Cert.CapPrr

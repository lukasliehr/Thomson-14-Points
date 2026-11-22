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

/-- The cells of the group 242. -/
noncomputable def cells242 : List Cell :=
  [{ i := 7, j := 9, k := 1, use := 0, tree := 235586524825 },
    { i := 20, j := 9, k := 5, use := 0, tree := 235607433881 },
    { i := 47, j := 22, k := 14, use := 0, tree := hex% "db6d844265a6db6d02832d1" },
    { i := 48, j := 22, k := 14, use := 0, tree := hex% "db6d029b41969b2db6814da0cb6c32d86506da051" },
    { i := 21, j := 22, k := 15, use := 0, tree := 235609011265 },
    { i := 21, j := 23, k := 5, use := 0, tree := 14026 },
    { i := 20, j := 9, k := 6, use := 0, tree := 15010294208153 },
    { i := 21, j := 22, k := 6, use := 0, tree := hex% "d869b41b4c26d30d361a6582db4cb0436116ca" },
    { i := 21, j := 23, k := 6, use := 0, tree := 3950058979889095193 }]

/-- The group 242: the cover of a box by its cells. -/
theorem g242_ok : boxOk run { e1 := 1, c1 := 2, e2 := 2, c2 := 6, e3 := 1, c3 := 1 } (16592611116) cells242 = true := by
  decide +kernel

/-- The cells of the group 243. -/
noncomputable def cells243 : List Cell :=
  [{ i := 2, j := 24, k := 1, use := 0, tree := hex% "c2a5854b02902841854b6d80000000000000000000000000000000000000000486f6cb000000000000000000000000000000014283202a42" }]

/-- The group 243: the cover of a box by its cells. -/
theorem g243_ok : boxOk run { e1 := 1, c1 := 2, e2 := 2, c2 := 7, e3 := 1, c3 := 1 } (61) cells243 = true := by
  decide +kernel

/-- The cells of the group 244. -/
noncomputable def cells244 : List Cell :=
  [{ i := 7, j := 9, k := 2, use := 0, tree := 3 },
    { i := 8, j := 9, k := 7, use := 0, tree := hex% "36d90cb41b6d821a641" },
    { i := 8, j := 9, k := 8, use := 0, tree := hex% "db61941b65a6196ca6cb41b6816cb642641" },
    { i := 2, j := 24, k := 2, use := 0, tree := hex% "d8000000000000000000000000000000000000000036ec834800000000000000000000000000000004000000000000000000000000000000000000000005cfdef8000000000000000000000000000000008c000000000000000000000000000000000000000021980e40000000000000000000000000000000020548000000000000000000000000000000000000000050260c300000000000000000000000000000000400000000000000000000000000000000000000000849e8ba000000000000000000000000000000008152110990d00a9" }]

/-- The group 244: the cover of a box by its cells. -/
theorem g244_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 3, e3 := 1, c3 := 2 } (253873) cells244 = true := by
  decide +kernel

/-- The cells of the group 245. -/
noncomputable def cells245 : List Cell :=
  [{ i := 7, j := 9, k := 9, use := 0, tree := hex% "d969b65065b2c26db2834596cb4ca" },
    { i := 20, j := 9, k := 9, use := 0, tree := hex% "36996d321a6d96134596ca" },
    { i := 47, j := 49, k := 22, use := 0, tree := hex% "db68169b4da6db0502d2" },
    { i := 47, j := 50, k := 49, use := 0, tree := hex% "db4cb6d32da6426db29b2d941109b611" },
    { i := 47, j := 50, k := 50, use := 0, tree := 3950058978025178777 },
    { i := 48, j := 49, k := 49, use := 0, tree := hex% "d96db6c32836db41940a0db60a6cb69b41940a" },
    { i := 48, j := 49, k := 50, use := 0, tree := hex% "365b29b60b69b61941b4db05b6836d028141b6194da05a" },
    { i := 48, j := 50, k := 22, use := 0, tree := hex% "da6db41161a6d305a" },
    { i := 21, j := 22, k := 23, use := 0, tree := 3 },
    { i := 21, j := 23, k := 9, use := 0, tree := 3 }]

/-- The group 245: the cover of a box by its cells. -/
theorem g245_ok : boxOk run { e1 := 1, c1 := 2, e2 := 2, c2 := 6, e3 := 2, c3 := 6 } (274776934860) cells245 = true := by
  decide +kernel

/-- The cells of the group 246. -/
noncomputable def cells246 : List Cell :=
  [{ i := 2, j := 9, k := 24, use := 0, tree := hex% "300000000000000000000000037b54dfe00000000000000000000000000000000000000000000000080000000000000000000000005749324000000000000000000000000000000000000000000000000b03a8000000000000000000000000ab3b49380000000000000000000000000000000000000000021c2e260751098000000000000000000000001c3e858800000000000000000000000000000000000000000000000044400000000000000000000000076864da80000000000000000000000000000000000000000000000020698000000000000000000000001b17b53e00000000000000000000000000000000000000000084b4ea44d32c10ea" }]

/-- The group 246: the cover of a box by its cells. -/
theorem g246_ok : boxOk run { e1 := 1, c1 := 2, e2 := 2, c2 := 6, e3 := 2, c3 := 7 } (62) cells246 = true := by
  decide +kernel

/-- The cells of the group 247. -/
noncomputable def cells247 : List Cell :=
  [{ i := 2, j := 24, k := 9, use := 0, tree := hex% "36c000000000000000000000000000000000000000025c29a9400000000000000000000000006d24b8605482d80000000000000000000000000000000000000000226adde800000000000000000000000025ff08fc0a9000000000000000000000000000000000000000001761ae400000000000000000000000006ce18148814196980a900000000000000000000000000000000000000000000000c00000000000000000000000003087b928152c2a42" },
    { i := 2, j := 24, k := 24, use := 0, tree := 12522 }]

/-- The group 247: the cover of a box by its cells. -/
theorem g247_ok : boxOk run { e1 := 1, c1 := 2, e2 := 2, c2 := 7, e3 := 1, c3 := 3 } (260598) cells247 = true := by
  decide +kernel

/-- The cells of the group 248. -/
noncomputable def cells248 : List Cell :=
  [{ i := 9, j := 2, k := 0, use := 0, tree := hex% "340a000000000000000000000000000000000000000000000000000000000c52ae5c00000000019a255710341" }]

/-- The group 248: the cover of a box by its cells. -/
theorem g248_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 0 } (60) cells248 = true := by
  decide +kernel

/-- The cells of the group 249. -/
noncomputable def cells249 : List Cell :=
  [{ i := 9, j := 2, k := 1, use := 0, tree := hex% "340000000000000000000000000000000000000000000000000000000000ab20cc000000000018551a034000000000000000000000000000000000000000000000000000000000005e14800000000000000004000000000000000000000000000000000000000000000000000000000004bc700000000000000000881a11" }]

/-- The group 249: the cover of a box by its cells. -/
theorem g249_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 1 } (60) cells249 = true := by
  decide +kernel

/-- The cells of the group 250. -/
noncomputable def cells250 : List Cell :=
  [{ i := 9, j := 2, k := 2, use := 0, tree := hex% "4601cd80000000000000004" }]

/-- The group 250: the cover of a box by its cells. -/
theorem g250_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 2 } (60) cells250 = true := by
  decide +kernel

/-- The cells of the group 251. -/
noncomputable def cells251 : List Cell :=
  [{ i := 9, j := 2, k := 9, use := 0, tree := hex% "d068341a0d0680000000000000000000000000000000000000000000000000000000000cdb530000000000000000406834000000000000000000000000000000000000000000000000000000000013acec00000000000000020358000000000000000000000000000000000000000000000000000000000006650800000000000000040000000000000000000000000000000000000000000000000000000000054b58000000000000000088844221a200000000000000000000000000000000000000000000000000000000001ed1ec00000000000000011020d0400000000000000000000000000000000000000000000000000000000028991e0000000000000000e2" },
    { i := 9, j := 2, k := 24, use := 0, tree := hex% "80000000000000000000000001e0662380000000005eae9840ea" }]

/-- The group 251: the cover of a box by its cells. -/
theorem g251_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 3 } (16312) cells251 = true := by
  decide +kernel

end N14Cert.CapPrr

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

/-- The cells of the group 209. -/
noncomputable def cells209 : List Cell :=
  [{ i := 70, j := 48, k := 49, use := 0, tree := hex% "140a00000000000000000000000000000000000000000000000000000000006af24d00000000000000000000000000000000000000000000000000000000000a719ca20000000000000000000000000000000000000000000000000000000000404f6e80a0280000000000000000000000000000000000000000000000000000000001ce2d540000000000000000000000000000000000000000000000000000000000257e4f80000000000000000000000000000000000000000000000000000000000605c1310200000000000000000000000000000000000000000000000000000000006b215d000000000000000000000000000000000000000000000000000000000009fcafa000000000000000000000000000000000000000000000000000000000002776cc800000000000000000000000000000000000000000000000000000000003aa389100000000000000000000000000000000000000000000000000000000000c1769c05002902a" },
    { i := 71, j := 48, k := 49, use := 0, tree := hex% "15b04ac000000000000000000000000000000000000000000000000000000000016659c80000000000000000000000000000000000000000000000000000000000404e4101000000000000000000000000000000000000000000000000000000000018bfc68ca000000000000000000000000000000000000000000000000000000000010c2568d0028000000000000000000000000000000000000000000000000000000000141eac40294000000000000000000000000000000000000000000000000000000000052d7ed00000000000000000000000000000000000000000000000000000000000690aba2040a000000000000000000000000000000000000000000000000000000000058900f0000000000000000000000000000000000000000000000000000000000089f87e2000000000000000000000000000000000000000000000000000000000034ce5a80815014800000000000000000000000000000000000000000000000000000000013dd29c00000000000000000000000000000000000000000000000000000000001e3978800000000000000000000000000000000000000000000000000000000002b2dd701028000000000000000000000000000000000000000000000000000000000187bf340000000000000000000000000000000000000000000000000000000000208b328000000000000000000000000000000000000000000000000000000000052f02910280a42" },
    { i := 32, j := 48, k := 50, use := 0, tree := 5 }]

/-- The group 209: the cover of a box by its cells. -/
theorem g209_ok : boxOk run { e1 := 4, c1 := 7, e2 := 4, c2 := 23, e3 := 3, c3 := 12 } (1010) cells209 = true := by
  decide +kernel

/-- The cells of the group 210. -/
noncomputable def cells210 : List Cell :=
  [{ i := 13, j := 21, k := 23, use := 0, tree := 5 }]

/-- The group 210: the cover of a box by its cells. -/
theorem g210_ok : boxOk run { e1 := 3, c1 := 3, e2 := 3, c2 := 11, e3 := 3, c3 := 13 } (3) cells210 = true := by
  decide +kernel

/-- The cells of the group 211. -/
noncomputable def cells211 : List Cell :=
  [{ i := 0, j := 2, k := 24, use := 0, tree := hex% "288000000000000000000000000000000000000000016b8d5a4" }]

/-- The group 211: the cover of a box by its cells. -/
theorem g211_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 2, e3 := 2, c3 := 7 } (62) cells211 = true := by
  decide +kernel

/-- The cells of the group 212. -/
noncomputable def cells212 : List Cell :=
  [{ i := 0, j := 9, k := 2, use := 0, tree := hex% "28d9204200000000000000000000000019896703c" }]

/-- The group 212: the cover of a box by its cells. -/
theorem g212_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 3, e3 := 1, c3 := 2 } (61) cells212 = true := by
  decide +kernel

/-- The cells of the group 213. -/
noncomputable def cells213 : List Cell :=
  [{ i := 0, j := 9, k := 9, use := 0, tree := hex% "2f8000000000000000000000001b491a00c" },
    { i := 0, j := 9, k := 24, use := 0, tree := 5 },
    { i := 0, j := 24, k := 9, use := 0, tree := 5 },
    { i := 0, j := 24, k := 24, use := 0, tree := 5 },
    { i := 0, j := 55, k := 24, use := 0, tree := 5 }]

/-- The group 213: the cover of a box by its cells. -/
theorem g213_ok : boxOk run { e1 := 1, c1 := 0, e2 := 1, c2 := 3, e3 := 1, c3 := 3 } (272455659449) cells213 = true := by
  decide +kernel

/-- The cells of the group 214. -/
noncomputable def cells214 : List Cell :=
  [{ i := 1, j := 0, k := 0, use := 0, tree := hex% "3c8000000000f2f7d7000000000047f0acc" }]

/-- The group 214: the cover of a box by its cells. -/
theorem g214_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 0 } (3) cells214 = true := by
  decide +kernel

/-- The cells of the group 215. -/
noncomputable def cells215 : List Cell :=
  [{ i := 1, j := 0, k := 1, use := 0, tree := hex% "d0000000000000000000000000000000000000000000ffb9e0000000000000009841a00000000000000000000000000000000000000000025bb5c00000000000000010a068" }]

/-- The group 215: the cover of a box by its cells. -/
theorem g215_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 1 } (3) cells215 = true := by
  decide +kernel

/-- The cells of the group 216. -/
noncomputable def cells216 : List Cell :=
  [{ i := 1, j := 0, k := 2, use := 0, tree := hex% "3400000000000000000000000000000000000000000076fca800000000000000021" }]

/-- The group 216: the cover of a box by its cells. -/
theorem g216_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 2 } (3) cells216 = true := by
  decide +kernel

/-- The cells of the group 217. -/
noncomputable def cells217 : List Cell :=
  [{ i := 1, j := 0, k := 9, use := 0, tree := hex% "340000000000000000000000000000000000000000004dea6c00000000000000021" },
    { i := 1, j := 0, k := 24, use := 0, tree := hex% "200000000000000000000000000aa88fd8000000000e203234" }]

/-- The group 217: the cover of a box by its cells. -/
theorem g217_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 0, e3 := 1, c3 := 3 } (1006) cells217 = true := by
  decide +kernel

/-- The cells of the group 218. -/
noncomputable def cells218 : List Cell :=
  [{ i := 1, j := 1, k := 0, use := 0, tree := hex% "707da80000000000383ed4000000000022c26b02a40000000000000000000000000131910c00000000008fac7c000000000050e1960" }]

/-- The group 218: the cover of a box by its cells. -/
theorem g218_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 1, e3 := 1, c3 := 0 } (3) cells218 = true := by
  decide +kernel

/-- The cells of the group 219. -/
noncomputable def cells219 : List Cell :=
  [{ i := 5, j := 1, k := 1, use := 0, tree := hex% "c000000000000000000000000000056b8000000000000ad70000000000000000206cb0d20000000000000000000000000000980b000000000000000000000000000000008da651" }]

/-- The group 219: the cover of a box by its cells. -/
theorem g219_ok : boxOk run { e1 := 2, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 1 } (3) cells219 = true := by
  decide +kernel

/-- The cells of the group 220. -/
noncomputable def cells220 : List Cell :=
  [{ i := 6, j := 5, k := 1, use := 0, tree := hex% "12d6000000000000000010000000000000000000000000000000000000000000037c6400000000000000022" }]

/-- The group 220: the cover of a box by its cells. -/
theorem g220_ok : boxOk run { e1 := 2, c1 := 3, e2 := 2, c2 := 2, e3 := 1, c3 := 1 } (3) cells220 = true := by
  decide +kernel

/-- The cells of the group 221. -/
noncomputable def cells221 : List Cell :=
  [{ i := 6, j := 6, k := 5, use := 0, tree := hex% "6f8c800000000000000000000000000000004" },
    { i := 37, j := 16, k := 16, use := 512, tree := hex% "db0d84d86da6586c26c300000000000172db00000000000000000000000000000000000000000000000000000000000000008c095094844221b09b0d844000000000050882800000000000000000000000000000000000000000000000000000000000000022000000000016918700000000000000000000000000004f44000000000000000000000000000000008000000000024e99000000000000000000000000000000000000000000000000000000000000000011a651" },
    { i := 38, j := 16, k := 16, use := 512, tree := hex% "b48c38000000000000000000000000000000000000000000027a2000000000000000040000000000154c2c000000000000000000000000000000000000000000004d9900000000000000008800000000005530b0000000000000000000000000000136640000000000000000000000000000000230000000000000000000000000000000000000000000019700000000000000000000000000000000089b0db4da2da6da000000000002d5870000000000000000000000000000000000000000000002ed000000000000000085b400000000000977ea00000000000000000000000000000000000000000000000000000000000000010844045a65b211" },
    { i := 16, j := 16, k := 17, use := 0, tree := 3 },
    { i := 16, j := 17, k := 6, use := 0, tree := 218 },
    { i := 17, j := 6, k := 6, use := 0, tree := hex% "6acfa000000000000000119" }]

/-- The group 221: the cover of a box by its cells. -/
theorem g221_ok : boxOk run { e1 := 2, c1 := 3, e2 := 2, c2 := 3, e3 := 1, c3 := 1 } (4190798) cells221 = true := by
  decide +kernel

/-- The cells of the group 222. -/
noncomputable def cells222 : List Cell :=
  [{ i := 5, j := 1, k := 2, use := 0, tree := hex% "36d96130000000000000000000000000000000000000000000258b1000000000000000080b6d320a" }]

/-- The group 222: the cover of a box by its cells. -/
theorem g222_ok : boxOk run { e1 := 2, c1 := 2, e2 := 1, c2 := 1, e3 := 1, c3 := 2 } (3) cells222 = true := by
  decide +kernel

end N14Cert.CapRrr

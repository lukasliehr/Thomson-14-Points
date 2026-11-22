module

public import N14Cert.Case1.Run
public import N14.Box.MasterKernel
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.Case1

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The cells of the group 412. -/
noncomputable def cells412 : List Cell :=
  [{ i := 2, j := 9, k := 24, use := 0, tree := hex% "db000000000000000000000000000000000000000000000000000000005c6cf50b8ca09b6000000000000000000000000000000000000000000000000000000028e0a161510148458" }]

/-- The group 412: the cover of a box by its cells. -/
theorem g412_ok : boxOk run { e1 := 1, c1 := 2, e2 := 2, c2 := 6, e3 := 3, c3 := 14 } (3) cells412 = true := by
  decide +kernel

/-- The cells of the group 413. -/
noncomputable def cells413 : List Cell :=
  [{ i := 2, j := 9, k := 55, use := 0, tree := hex% "300000000000000000000000000000000000000000000000000000001cd7c2e328000000000000000000000000000000000000000000000000000000006fe54ce6a0142600000000000000000000000000000000000000000000000000000000e8e5c113000000000000000000000000000000000000000000000000000000007bb3698422040000000000000000000000000000000000000000000000000000000547dce422000000000000000000000000000000000000000000000000000000019db4136cc2050000000000000000000000000000000000000000000000000000000159f70badd00a116c0000000000000000000000000000000000000000000000000000000954464c021608" }]

/-- The group 413: the cover of a box by its cells. -/
theorem g413_ok : boxOk run { e1 := 1, c1 := 2, e2 := 2, c2 := 6, e3 := 4, c3 := 30 } (3) cells413 = true := by
  decide +kernel

/-- The cells of the group 414. -/
noncomputable def cells414 : List Cell :=
  [{ i := 2, j := 9, k := 118, use := 0, tree := hex% "5527516d640000000000000000000000000000000000000000000000000000000420345c8085802800000000000000000000000000000000000000000000000000000041aa808754601" },
    { i := 2, j := 9, k := 245, use := 0, tree := hex% "5600a0000000000000000000000000000000000000000000000000000001a4d524bef01" },
    { i := 2, j := 9, k := 246, use := 0, tree := hex% "2e5ff236bd000000000000000000000000000000000000000000000000000000238337c9b621" }]

/-- The group 414: the cover of a box by its cells. -/
theorem g414_ok : boxOk run { e1 := 1, c1 := 2, e2 := 2, c2 := 6, e3 := 4, c3 := 31 } (1006) cells414 = true := by
  decide +kernel

/-- The cells of the group 415. -/
noncomputable def cells415 : List Cell :=
  [{ i := 2, j := 24, k := 9, use := 0, tree := hex% "1d000000017fee7bab00000000000000000000000000000000000000006264e313898" }]

/-- The group 415: the cover of a box by its cells. -/
theorem g415_ok : boxOk run { e1 := 1, c1 := 2, e2 := 2, c2 := 7, e3 := 2, c3 := 6 } (61) cells415 = true := by
  decide +kernel

/-- The cells of the group 416. -/
noncomputable def cells416 : List Cell :=
  [{ i := 2, j := 24, k := 24, use := 0, tree := hex% "c00000000000003740000000000000000000000000000000000000002c9ebc6720000000047ff75bc50000000000000000000000000000000000000000df356aba80545b000000000000004f0000000000000000000000000000000000000000b2943e28800000007135c506000000000000000000000000000000000000000021833fcb700ac2288" }]

/-- The group 416: the cover of a box by its cells. -/
theorem g416_ok : boxOk run { e1 := 1, c1 := 2, e2 := 3, c2 := 14, e3 := 3, c3 := 14 } (3) cells416 = true := by
  decide +kernel

/-- The cells of the group 417. -/
noncomputable def cells417 : List Cell :=
  [{ i := 2, j := 24, k := 55, use := 0, tree := hex% "140a0000000000000000000000000000000000000000000000000000000a56df4419080000000000000000000000000000000000000000000000000000000df76db6cc005600000000000000000000000000000000000000000000000000000019e1c9a50310028000000000000000000000000000000000000000000000000000000668c7639f4005448" },
    { i := 2, j := 24, k := 118, use := 0, tree := hex% "140a00000000000000000000000000000000000000000000000000000013ddd4d94300029" },
    { i := 2, j := 24, k := 245, use := 0, tree := 5 },
    { i := 2, j := 24, k := 246, use := 0, tree := 5 }]

/-- The group 417: the cover of a box by its cells. -/
theorem g417_ok : boxOk run { e1 := 1, c1 := 2, e2 := 3, c2 := 14, e3 := 3, c3 := 15 } (16110) cells417 = true := by
  decide +kernel

/-- The cells of the group 418. -/
noncomputable def cells418 : List Cell :=
  [{ i := 2, j := 55, k := 24, use := 0, tree := hex% "c6ed3aebb600000000000000000000000000000000000000834081c4034" }]

/-- The group 418: the cover of a box by its cells. -/
theorem g418_ok : boxOk run { e1 := 1, c1 := 2, e2 := 3, c2 := 15, e3 := 3, c3 := 14 } (61) cells418 = true := by
  decide +kernel

/-- The cells of the group 419. -/
noncomputable def cells419 : List Cell :=
  [{ i := 2, j := 55, k := 55, use := 0, tree := 5 },
    { i := 2, j := 55, k := 118, use := 0, tree := 5 },
    { i := 2, j := 55, k := 245, use := 0, tree := 5 },
    { i := 2, j := 55, k := 246, use := 0, tree := 5 }]

/-- The group 419: the cover of a box by its cells. -/
theorem g419_ok : boxOk run { e1 := 1, c1 := 2, e2 := 4, c2 := 30, e3 := 3, c3 := 15 } (16110) cells419 = true := by
  decide +kernel

end N14Cert.Case1

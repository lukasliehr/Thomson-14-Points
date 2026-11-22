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

/-- The cells of the group 420. -/
noncomputable def cells420 : List Cell :=
  [{ i := 2, j := 118, k := 55, use := 0, tree := 5 },
    { i := 2, j := 118, k := 118, use := 0, tree := 5 },
    { i := 2, j := 118, k := 245, use := 0, tree := 5 },
    { i := 2, j := 118, k := 246, use := 0, tree := 5 },
    { i := 2, j := 245, k := 118, use := 0, tree := 5 },
    { i := 2, j := 245, k := 245, use := 0, tree := 5 },
    { i := 2, j := 245, k := 246, use := 0, tree := 5 },
    { i := 2, j := 246, k := 245, use := 0, tree := 5 },
    { i := 2, j := 246, k := 246, use := 0, tree := 5 }]

/-- The group 420: the cover of a box by its cells. -/
theorem g420_ok : boxOk run { e1 := 1, c1 := 2, e2 := 4, c2 := 31, e3 := 3, c3 := 15 } (4327706966518) cells420 = true := by
  decide +kernel

/-- The cells of the group 421. -/
noncomputable def cells421 : List Cell :=
  [{ i := 9, j := 2, k := 1, use := 0, tree := hex% "155cf1a700000000166ac88080000000000000000000000007947d9ac" }]

/-- The group 421: the cover of a box by its cells. -/
theorem g421_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 1 } (60) cells421 = true := by
  decide +kernel

/-- The cells of the group 422. -/
noncomputable def cells422 : List Cell :=
  [{ i := 9, j := 2, k := 2, use := 0, tree := hex% "94d980000000000e187ae000000000000000000000000000000004" }]

/-- The group 422: the cover of a box by its cells. -/
theorem g422_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 2, e3 := 1, c3 := 2 } (60) cells422 = true := by
  decide +kernel

/-- The cells of the group 423. -/
noncomputable def cells423 : List Cell :=
  [{ i := 9, j := 2, k := 9, use := 0, tree := hex% "150a85400000000000000000000000000532d6800000000000000000000000000000002000000000000000000000000003d7cdd80000000000000000000000000000000444000000000000000000000000028111a0000000000000000000000000000000022040000000000000000000000000484e1cc0000000000000000000000000000000220a8" }]

/-- The group 423: the cover of a box by its cells. -/
theorem g423_ok : boxOk run { e1 := 2, c1 := 6, e2 := 1, c2 := 2, e3 := 2, c3 := 6 } (3) cells423 = true := by
  decide +kernel

/-- The cells of the group 424. -/
noncomputable def cells424 : List Cell :=
  [{ i := 9, j := 2, k := 24, use := 0, tree := 1369 }]

/-- The group 424: the cover of a box by its cells. -/
theorem g424_ok : boxOk run { e1 := 2, c1 := 6, e2 := 1, c2 := 2, e3 := 3, c3 := 14 } (3) cells424 = true := by
  decide +kernel

/-- The cells of the group 425. -/
noncomputable def cells425 : List Cell :=
  [{ i := 9, j := 2, k := 55, use := 0, tree := hex% "54000000000000000000000001dd4333ec00000000000000000000000330213c161" }]

/-- The group 425: the cover of a box by its cells. -/
theorem g425_ok : boxOk run { e1 := 2, c1 := 6, e2 := 1, c2 := 2, e3 := 4, c3 := 30 } (3) cells425 = true := by
  decide +kernel

/-- The cells of the group 426. -/
noncomputable def cells426 : List Cell :=
  [{ i := 9, j := 2, k := 118, use := 0, tree := 5607592 },
    { i := 9, j := 2, k := 245, use := 0, tree := hex% "77fb64a8800000000000000000000006fbbdc363c0a8" },
    { i := 9, j := 2, k := 246, use := 0, tree := hex% "6ae76db080000000000000000000000b97fc8daf40a8" }]

/-- The group 426: the cover of a box by its cells. -/
theorem g426_ok : boxOk run { e1 := 2, c1 := 6, e2 := 1, c2 := 2, e3 := 4, c3 := 31 } (1006) cells426 = true := by
  decide +kernel

end N14Cert.Case1

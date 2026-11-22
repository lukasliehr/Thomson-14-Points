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

/-- The cells of the group 443. -/
noncomputable def cells443 : List Cell :=
  [{ i := 24, j := 118, k := 55, use := 0, tree := 3 }]

/-- The group 443: the cover of a box by its cells. -/
theorem g443_ok : boxOk run { e1 := 3, c1 := 14, e2 := 4, c2 := 31, e3 := 4, c3 := 30 } (61) cells443 = true := by
  decide +kernel

/-- The cells of the group 444. -/
noncomputable def cells444 : List Cell :=
  [{ i := 24, j := 118, k := 118, use := 0, tree := 3 },
    { i := 24, j := 118, k := 245, use := 0, tree := 2769787520828 },
    { i := 24, j := 118, k := 246, use := 0, tree := 7518499907100 }]

/-- The group 444: the cover of a box by its cells. -/
theorem g444_ok : boxOk run { e1 := 3, c1 := 14, e2 := 5, c2 := 62, e3 := 4, c3 := 31 } (1006) cells444 = true := by
  decide +kernel

/-- The cells of the group 445. -/
noncomputable def cells445 : List Cell :=
  [{ i := 24, j := 245, k := 118, use := 0, tree := hex% "1eef2a2d0c80000000000000000000000000000000000000284e433873c" },
    { i := 24, j := 245, k := 245, use := 0, tree := 5 },
    { i := 24, j := 245, k := 246, use := 0, tree := 5 },
    { i := 24, j := 246, k := 245, use := 0, tree := 5 },
    { i := 24, j := 246, k := 246, use := 0, tree := 5 }]

/-- The group 445: the cover of a box by its cells. -/
theorem g445_ok : boxOk run { e1 := 3, c1 := 14, e2 := 5, c2 := 63, e3 := 4, c3 := 31 } (4127222) cells445 = true := by
  decide +kernel

/-- The cells of the group 446. -/
noncomputable def cells446 : List Cell :=
  [{ i := 55, j := 24, k := 24, use := 0, tree := 3 },
    { i := 55, j := 24, k := 55, use := 0, tree := 3 },
    { i := 55, j := 24, k := 118, use := 0, tree := 3 },
    { i := 55, j := 24, k := 245, use := 0, tree := 3 },
    { i := 55, j := 24, k := 246, use := 0, tree := hex% "39f83602480000000000000000000001ab1263b514" }]

/-- The group 446: the cover of a box by its cells. -/
theorem g446_ok : boxOk run { e1 := 3, c1 := 15, e2 := 3, c2 := 14, e3 := 2, c3 := 7 } (66828530) cells446 = true := by
  decide +kernel

/-- The cells of the group 447. -/
noncomputable def cells447 : List Cell :=
  [{ i := 55, j := 55, k := 24, use := 0, tree := 3 },
    { i := 118, j := 55, k := 24, use := 0, tree := 3 }]

/-- The group 447: the cover of a box by its cells. -/
theorem g447_ok : boxOk run { e1 := 3, c1 := 15, e2 := 3, c2 := 15, e3 := 3, c3 := 14 } (258548) cells447 = true := by
  decide +kernel

/-- The cells of the group 448. -/
noncomputable def cells448 : List Cell :=
  [{ i := 55, j := 55, k := 55, use := 0, tree := 3 },
    { i := 55, j := 55, k := 118, use := 0, tree := 3 },
    { i := 55, j := 55, k := 245, use := 0, tree := 3 },
    { i := 55, j := 55, k := 246, use := 0, tree := 3 }]

/-- The group 448: the cover of a box by its cells. -/
theorem g448_ok : boxOk run { e1 := 4, c1 := 30, e2 := 4, c2 := 30, e3 := 3, c3 := 15 } (16110) cells448 = true := by
  decide +kernel

/-- The cells of the group 449. -/
noncomputable def cells449 : List Cell :=
  [{ i := 55, j := 118, k := 55, use := 0, tree := 3 },
    { i := 55, j := 118, k := 118, use := 0, tree := 3 },
    { i := 55, j := 118, k := 245, use := 0, tree := 3 },
    { i := 55, j := 118, k := 246, use := 0, tree := 3 },
    { i := 55, j := 245, k := 118, use := 0, tree := 3 },
    { i := 55, j := 245, k := 245, use := 0, tree := 3 },
    { i := 55, j := 245, k := 246, use := 0, tree := 3 },
    { i := 55, j := 246, k := 245, use := 0, tree := 3 },
    { i := 55, j := 246, k := 246, use := 0, tree := 5 }]

/-- The group 449: the cover of a box by its cells. -/
theorem g449_ok : boxOk run { e1 := 4, c1 := 30, e2 := 4, c2 := 31, e3 := 3, c3 := 15 } (4327706966518) cells449 = true := by
  decide +kernel

/-- The cells of the group 450. -/
noncomputable def cells450 : List Cell :=
  [{ i := 118, j := 55, k := 55, use := 0, tree := 3 },
    { i := 118, j := 55, k := 118, use := 0, tree := 3 },
    { i := 118, j := 55, k := 245, use := 0, tree := 3 },
    { i := 118, j := 55, k := 246, use := 0, tree := 3 }]

/-- The group 450: the cover of a box by its cells. -/
theorem g450_ok : boxOk run { e1 := 4, c1 := 31, e2 := 4, c2 := 30, e3 := 3, c3 := 15 } (4176114) cells450 = true := by
  decide +kernel

end N14Cert.Case1

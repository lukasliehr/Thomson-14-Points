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

/-- The cells of the group 427. -/
noncomputable def cells427 : List Cell :=
  [{ i := 9, j := 9, k := 2, use := 0, tree := hex% "4e3fdd8000000000271fee80000000000000000000000000000012c" },
    { i := 24, j := 9, k := 2, use := 0, tree := hex% "63a4a92c0000000079398c720000000000000000000000005235b3c3c" }]

/-- The group 427: the cover of a box by its cells. -/
theorem g427_ok : boxOk run { e1 := 1, c1 := 3, e2 := 1, c2 := 3, e3 := 1, c3 := 2 } (258548) cells427 = true := by
  decide +kernel

/-- The cells of the group 428. -/
noncomputable def cells428 : List Cell :=
  [{ i := 9, j := 9, k := 9, use := 0, tree := hex% "39260c800000000073d5550000000000000000000000000000000040000000000e7aaaa0000000000000000000000000000000000000000000000008da6886996c8" },
    { i := 9, j := 9, k := 24, use := 0, tree := 3 },
    { i := 9, j := 9, k := 55, use := 0, tree := 3 },
    { i := 9, j := 9, k := 118, use := 0, tree := 3 },
    { i := 9, j := 9, k := 245, use := 0, tree := 3 },
    { i := 9, j := 9, k := 246, use := 0, tree := 3 }]

/-- The group 428: the cover of a box by its cells. -/
theorem g428_ok : boxOk run { e1 := 2, c1 := 6, e2 := 2, c2 := 6, e3 := 1, c3 := 3 } (4124398) cells428 = true := by
  decide +kernel

/-- The cells of the group 429. -/
noncomputable def cells429 : List Cell :=
  [{ i := 9, j := 24, k := 9, use := 0, tree := 3 }]

/-- The group 429: the cover of a box by its cells. -/
theorem g429_ok : boxOk run { e1 := 2, c1 := 6, e2 := 2, c2 := 7, e3 := 2, c3 := 6 } (61) cells429 = true := by
  decide +kernel

/-- The cells of the group 430. -/
noncomputable def cells430 : List Cell :=
  [{ i := 9, j := 24, k := 24, use := 0, tree := 3 },
    { i := 9, j := 24, k := 55, use := 0, tree := 76198954908 },
    { i := 9, j := 24, k := 118, use := 0, tree := hex% "d80000000000000000000000000000000000000000000000000000010f8f94971c2c1" },
    { i := 9, j := 24, k := 245, use := 0, tree := 789185 },
    { i := 9, j := 24, k := 246, use := 0, tree := 3543070542636 }]

/-- The group 430: the cover of a box by its cells. -/
theorem g430_ok : boxOk run { e1 := 2, c1 := 6, e2 := 3, c2 := 14, e3 := 2, c3 := 7 } (257774) cells430 = true := by
  decide +kernel

/-- The cells of the group 431. -/
noncomputable def cells431 : List Cell :=
  [{ i := 9, j := 55, k := 24, use := 0, tree := hex% "3380a2de580000000000000000000000000000000000000011bdcfc79c" }]

/-- The group 431: the cover of a box by its cells. -/
theorem g431_ok : boxOk run { e1 := 2, c1 := 6, e2 := 3, c2 := 15, e3 := 3, c3 := 14 } (61) cells431 = true := by
  decide +kernel

/-- The cells of the group 432. -/
noncomputable def cells432 : List Cell :=
  [{ i := 9, j := 55, k := 55, use := 0, tree := hex% "138000000000000000000000000000000000000000ad7fa6b7300000000000000000000000000000000000000000000000000000009471005c3e200000022a40d34f300000000000000000000000000000000000000251c40170f805458" },
    { i := 9, j := 55, k := 118, use := 0, tree := hex% "56000000000000000000000000000000000000000000000000000000a7c6977b9b08" },
    { i := 9, j := 55, k := 245, use := 0, tree := hex% "14000000000000000000000000000000000000000000000000000002b0019823ee0" },
    { i := 9, j := 55, k := 246, use := 0, tree := 5 }]

/-- The group 432: the cover of a box by its cells. -/
theorem g432_ok : boxOk run { e1 := 2, c1 := 6, e2 := 4, c2 := 30, e3 := 3, c3 := 15 } (16110) cells432 = true := by
  decide +kernel

end N14Cert.Case1

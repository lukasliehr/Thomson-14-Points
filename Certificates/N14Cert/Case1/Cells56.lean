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

/-- The cells of the group 451. -/
noncomputable def cells451 : List Cell :=
  [{ i := 118, j := 118, k := 55, use := 0, tree := 3 },
    { i := 244, j := 118, k := 55, use := 0, tree := 3 }]

/-- The group 451: the cover of a box by its cells. -/
theorem g451_ok : boxOk run { e1 := 4, c1 := 31, e2 := 4, c2 := 31, e3 := 4, c3 := 30 } (258548) cells451 = true := by
  decide +kernel

/-- The cells of the group 452. -/
noncomputable def cells452 : List Cell :=
  [{ i := 118, j := 118, k := 118, use := 0, tree := 3 },
    { i := 118, j := 118, k := 245, use := 0, tree := 3 },
    { i := 118, j := 118, k := 246, use := 0, tree := 3 },
    { i := 118, j := 245, k := 118, use := 0, tree := 3 },
    { i := 118, j := 245, k := 245, use := 0, tree := 3 },
    { i := 118, j := 245, k := 246, use := 0, tree := 3 },
    { i := 118, j := 246, k := 245, use := 0, tree := 3 },
    { i := 118, j := 246, k := 246, use := 0, tree := 3 }]

/-- The group 452: the cover of a box by its cells. -/
theorem g452_ok : boxOk run { e1 := 5, c1 := 62, e2 := 4, c2 := 31, e3 := 4, c3 := 31 } (16905105337) cells452 = true := by
  decide +kernel

/-- The cells of the group 453. -/
noncomputable def cells453 : List Cell :=
  [{ i := 244, j := 118, k := 118, use := 0, tree := 3 },
    { i := 244, j := 118, k := 245, use := 0, tree := 3 },
    { i := 244, j := 118, k := 246, use := 0, tree := 3 }]

/-- The group 453: the cover of a box by its cells. -/
theorem g453_ok : boxOk run { e1 := 5, c1 := 63, e2 := 5, c2 := 62, e3 := 4, c3 := 31 } (260338) cells453 = true := by
  decide +kernel

/-- The cells of the group 454. -/
noncomputable def cells454 : List Cell :=
  [{ i := 244, j := 245, k := 118, use := 0, tree := 3 },
    { i := 245, j := 245, k := 118, use := 0, tree := 3 },
    { i := 244, j := 245, k := 245, use := 0, tree := 3 },
    { i := 244, j := 245, k := 246, use := 0, tree := 3 },
    { i := 244, j := 246, k := 245, use := 0, tree := 3 },
    { i := 244, j := 246, k := 246, use := 0, tree := 3 },
    { i := 245, j := 245, k := 245, use := 0, tree := 3 },
    { i := 245, j := 245, k := 246, use := 0, tree := 3 },
    { i := 245, j := 246, k := 245, use := 0, tree := 3 },
    { i := 245, j := 246, k := 246, use := 0, tree := 3 }]

/-- The group 454: the cover of a box by its cells. -/
theorem g454_ok : boxOk run { e1 := 5, c1 := 63, e2 := 5, c2 := 63, e3 := 4, c3 := 31 } (69243393865682) cells454 = true := by
  decide +kernel

end N14Cert.Case1

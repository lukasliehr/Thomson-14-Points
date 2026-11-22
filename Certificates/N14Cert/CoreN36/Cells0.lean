module

public import N14Cert.CoreN36.Run
public import N14.Box.MasterKernel
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.CoreN36

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The cells of the group 0. -/
noncomputable def cells0 : List Cell :=
  [{ i := 9, j := 9, k := 8, use := 3, tree := hex% "350e8344a0000000001ffa97e0000000000000058000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000003fee4480000000000000060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000220682354150c8b5029a" }]

/-- The group 0: the cover of a box by its cells. -/
theorem g0_ok : boxOk run { e1 := 1, c1 := 1, e2 := 1, c2 := 2, e3 := 1, c3 := 3 } (hex% "3ffffff9cedc93b724edced2d372") cells0 = true := by
  decide +kernel

end N14Cert.CoreN36

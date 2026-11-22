module

public import N14Cert.CoreN56.Run
public import N14.Box.MasterKernel
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.CoreN56

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The cells of the group 0. -/
noncomputable def cells0 : List Cell :=
  [{ i := 10, j := 10, k := 8, use := 3, tree := hex% "c2a250000000003ffb642000000000000002b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000007fe219e000000000000000e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000110748340d5102d4cb09a" }]

/-- The group 0: the cover of a box by its cells. -/
theorem g0_ok : boxOk run { e1 := 1, c1 := 2, e2 := 1, c2 := 2, e3 := 1, c3 := 3 } (hex% "3ffffff724edc93b724edcedcb7372") cells0 = true := by
  decide +kernel

end N14Cert.CoreN56

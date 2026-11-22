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

/-- The cells of the group 262. -/
noncomputable def cells262 : List Cell :=
  [{ i := 55, j := 24, k := 24, use := 0, tree := hex% "a1590e39800000000000000580000000bb3b9ef180000000000000004" },
    { i := 55, j := 55, k := 24, use := 0, tree := hex% "217039f860000000151defa40000000000000000a0000000000000020c" },
    { i := 118, j := 55, k := 24, use := 0, tree := hex% "3fb9304e7800000029916881f80000000d1861042000000000000233d4" }]

/-- The group 262: the cover of a box by its cells. -/
theorem g262_ok : boxOk run { e1 := 3, c1 := 15, e2 := 2, c2 := 7, e3 := 2, c3 := 7 } (17120964553) cells262 = true := by
  decide +kernel

end N14Cert.CapRrr

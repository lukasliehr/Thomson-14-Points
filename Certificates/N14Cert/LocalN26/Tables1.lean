module

public import N14Cert.LocalN26.Run

@[expose] public section

namespace N14Cert.LocalN26

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

theorem table1_ok : tableOk tab1 entries1 = true := by decide +kernel

end N14Cert.LocalN26

module

public import N14Cert.AnnN48.Run

@[expose] public section

namespace N14Cert.AnnN48

open N14.Box

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

theorem table0_ok : tableOk tab0 entries0 = true := by decide +kernel

end N14Cert.AnnN48

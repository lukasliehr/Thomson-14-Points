module

public import N14.Box.Master

/-!
# T7, the slack on a domain: the axioms of the theorem of a run with a master tree

The test of the axioms of `run_sound_master` and of the theorems below it that are new in the second stage. A
theorem that depended on `sorryAx` or on another axiom would change the message, and the build would fail.
-/

namespace N14.Box

/-- info: 'N14.Box.run_sound_master' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_sound_master

/-- info: 'N14.Box.master_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms master_sound

/-- info: 'N14.Box.box_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms box_sound

end N14.Box

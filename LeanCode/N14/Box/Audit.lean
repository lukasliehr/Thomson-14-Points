module

public import N14.Box.Cover

/-!
# T7, the slack on a domain: the axioms of the theorems of soundness

The theorem of a run (`run_sound`) and the theorems that it uses depend on the three standard axioms only. A
failed test is an error of the build. The statement module of a certificate (`Slack.lean`, written by
`N14/py/boxgen.py`) repeats the test for its theorem `slack_nonneg`.
-/

namespace N14.Box

/-- info: 'N14.Box.run_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_sound

/-- info: 'N14.Box.cell_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cell_sound

/-- info: 'N14.Box.table_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms table_sound

/-- info: 'N14.Box.go_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms go_sound

end N14.Box

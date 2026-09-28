import AME52

/-!
Audit: the headline statement is the same term as Formal Conjectures' `ame_5_2_exists`, and the
proofs use only the three standard axioms. Any failure is an error, so `lake env lean` exits
nonzero. As a control, Formal Conjectures' own declaration must show `sorryAx`, which shows the
axiom check can fail.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some ours := env.find? `AME52.ame_5_2_exists | throwError "AME52.ame_5_2_exists missing"
  let some theirs := env.find? `OpenQuantumProblem35.ame_5_2_exists
    | throwError "OpenQuantumProblem35.ame_5_2_exists missing"
  unless ours.type == theirs.type do
    throwError m!"statements differ: {ours.type} vs {theirs.type}"
  let standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [`AME52.ame_5_2_exists, `AME52.ringSign_trace, `AME52.pathSign_trace_fails] do
    let axs ← collectAxioms n
    let extra := axs.filter fun a => !standard.contains a
    unless extra.isEmpty do throwError m!"{n} uses axioms outside the standard three: {extra}"
  let fc ← collectAxioms `OpenQuantumProblem35.ame_5_2_exists
  unless fc.contains ``sorryAx do
    throwError "control failed: Formal Conjectures' ame_5_2_exists no longer shows sorryAx"
  logInfo m!"audit passed: statement identical ({ours.type}); standard axioms only; control ok"

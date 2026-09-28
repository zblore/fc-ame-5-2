# AME(5,2) in Lean

A Lean 4 proof that an absolutely maximally entangled state of five qubits exists. It proves `ame_5_2_exists` from Open Quantum Problem 35 in Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) against their own definitions.

## The result

An AME(5,2) state is a state of five qubits where any two of them on their own look completely random. The witness here is the five qubit ring state. Its amplitudes are ±1/√32 with the sign (-1)^(x₀x₁ + x₁x₂ + x₂x₃ + x₃x₄ + x₄x₀).

This is a known result (A. J. Scott, Phys. Rev. A 69, 052330, 2004). The ring state is a graph state, the form of AME state studied in W. Helwig, Absolutely Maximally Entangled Qudit Graph States (arXiv:1306.2879, 2013). The Lean proof is new. The mathematics isn't.

## The proof

- `AME52/Sign.lean` holds the one finite fact. After any of the 120 permutations of the parties the traced sum of sign products is 8 on the diagonal and 0 off it. The Lean kernel checks every case with `decide +kernel`.
- `AME52/State.lean` defines the state and proves it's normalised.
- `AME52/Existence.lean` proves every two party reduction is I/4.
- `AME52/FormalTarget.lean` puts the two together as `AME52.ame_5_2_exists : ExistsAME 5 2`.
- `AME52/Control.lean` drops one edge of the ring and shows the same check fails. So the check isn't passing for a trivial reason.

The statement is the same term as Formal Conjectures' `OpenQuantumProblem35.ame_5_2_exists`. The proof uses only `propext`, `Classical.choice` and `Quot.sound`.

## Building

It needs Lean v4.33.1 and depends on Formal Conjectures at commit `40a8592c`.

```
lake exe cache get
lake build
```

A fresh build first compiles Formal Conjectures' support library, which took about ten minutes here. Then the kernel check in `Sign.lean` runs. It took between four and eleven minutes across three runs. On a machine with limited memory set `LEAN_NUM_THREADS` to a small number first.

To rerun the checks:

```
lake env lean audit/Audit.lean
lake env lean audit/Vacuity.lean
python audit/lexical.py
lake exe runLinter AME52
```

## How it was made

I used Claude Code to draft the Lean. I've checked every line myself and can explain all of it. I checked the witness numerically before writing any Lean.

## About

I'm Zayn Blore. My main project is [csd-lean4](https://github.com/zblore/csd-lean4), the Lean library behind my work on Constraint-Surface Dynamics.

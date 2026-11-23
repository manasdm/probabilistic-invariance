import PISLean.Basic
import PISLean.Proposition1
import PISLean.CredibleRegion
import PISLean.Proposition2

/-!
# Lean verification of Propositions 1 and 2

Paper: M. Mejari, S. K. Mulagaleti, M. Banitalebi Dehkordi, A. Bemporad, D. Piga,
*Joint Learning of Models and Probabilistic Invariant Sets for Linear Stochastic Systems*,
IFAC Journal of Systems and Control, 2026.

* `PISLean/Basic.lean`          : definitions (sets, `ρ`, `β`, `ᾱ`, RIS, PIS, Lemma 2).
* `PISLean/Proposition1.lean`   : Proposition 1 (`PIS.proposition1`).
* `PISLean/CredibleRegion.lean` : `Θ_δ`, `λ_min`, `ρ_Δ(N, δ)` and steps (31)–(36).
* `PISLean/Proposition2.lean`   : Proposition 2 (`PIS.proposition2`).

`lake build` prints the axioms used by the two main theorems below. The expected output is
`[propext, Classical.choice, Quot.sound]`, the standard axioms of Lean and Mathlib; in
particular no `sorryAx` (no unfinished proof) appears.
-/

#print axioms PIS.proposition1
#print axioms PIS.proposition2

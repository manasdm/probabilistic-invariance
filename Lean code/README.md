# Lean verification of Propositions 1 and 2

This folder holds a machine-checked proof of the two main results of the paper. It is written in
[Lean 4](https://lean-lang.org) with the [Mathlib](https://github.com/leanprover-community/mathlib4)
library. Lean checks every step of the proofs. There is no `sorry` (no unproved step), and only
the standard axioms of Lean are used.

## What is proved

| Paper | Lean name | File |
|---|---|---|
| Proposition 1 (condition (9) gives a p-PIS) | `PIS.proposition1` | `PISLean/Proposition1.lean` |
| Eqs. (11) and (12) in its proof | `PIS.eq11`, `PIS.eq12` | `PISLean/Proposition1.lean` |
| Eqs. (18)/(20): Θ_δ is the χ²_{n²} ellipsoid of Lemma 3 | `PIS.mem_credibleSet_iff` | `PISLean/CredibleRegion.lean` |
| Eqs. (31)–(36): ρ(A) ≤ ρ(Â) + ρ_Δ(N,δ) for all A ∈ Θ_δ | `PIS.rho_le_of_mem_credibleSet` | `PISLean/CredibleRegion.lean` |
| Eqs. (24)–(25) | `PIS.eq24_iff_eq25` | `PISLean/Proposition2.lean` |
| Proposition 2 (lower bound p̃ ≤ p\*, posterior probability ≥ δ) | `PIS.proposition2` | `PISLean/Proposition2.lean` |

`PISLean/Basic.lean` holds the definitions. The names follow the paper:

| Paper | Lean |
|---|---|
| xᵀPx, ‖M‖₂, ‖M‖_F | `x ⬝ᵥ (P *ᵥ x)`, `specNorm M`, `frobNorm M` |
| P^{1/2}, P^{-1/2}, Q^{1/2} | `Ph`, `Ph⁻¹`, `Qh` (with `IsSqrt Ph P`, `IsSqrt Qh Q`) |
| 𝒫_α (3), 𝒲_p (7) | `ellipsoid P α`, `confRegion Q c_p` |
| ρ(A), β (10), ᾱ(A,p) (13) | `rho Ph A`, `beta Ph Qh`, `alphaBar Ph Qh A c_p` |
| Definitions 1 and 3 (p-PIS, RIS) | `IsPIS`, `IsRIS` |
| Θ_δ (20), λ_min, ρ_Δ(N,δ) (27) | `credibleSet`, `lambdaMin`, `rhoDelta` |

## What is assumed

The paper cites two facts without proving them. They enter the Lean theorems as hypotheses:

* **Lemma 2** (Hewing et al., 2018): an RIS for w_k ∈ 𝒲_p is a p-PIS. This is the hypothesis
  `Lemma2`. Mathlib has no χ² distribution yet, so the χ²_n CDF is an abstract function `F`.
* **Definition 4**: Pr(A ∈ Θ_δ | D) ≥ δ under the posterior of Lemma 3. This is the hypothesis
  `hDef4` on the posterior measure `post`.

One small difference from the wording in the paper makes the Lean statements slightly more
general: P^{1/2} and Q^{1/2} can be any symmetric invertible square roots of P and Q (`IsSqrt`).

## How to check the proofs

**In the browser (no installation needed).** Click
[this link](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fmanasdm%2Fprobabilistic-invariance%2Fmaster%2FLean%2520code%2FPISLean_all.lean)
to open the online Lean editor with the proofs already loaded. To do it by hand instead, open
<https://live.lean-lang.org/>, replace the example code with the whole content of
`PISLean_all.lean` (all files of this folder in one file), and keep the default project
"Latest Mathlib". After about a minute, the panel on the right shows no errors, and under
*All Messages* it lists the axioms used by `PIS.proposition1` and `PIS.proposition2`:
`[propext, Classical.choice, Quot.sound]`.

**On your computer.**

1. Install Lean with elan: <https://lean-lang.org/install>.
2. In this folder, run:

   ```bash
   lake exe cache get   # downloads the compiled Mathlib library (about 5 GB, into .lake/)
   lake build           # checks all proofs
   ```

   The build prints the axioms used by `PIS.proposition1` and `PIS.proposition2`:
   `[propext, Classical.choice, Quot.sound]`. These are the standard axioms of Lean; `sorryAx`
   would appear here if any step were unproved. (To print them again later, run
   `lake env lean PISLean.lean`.)
   The `.lake/` folder takes about 5 GB, so avoid building inside a cloud-synced folder.
3. To read the statements and proofs, open this folder in VS Code with the *Lean 4* extension.

Checked locally with Lean 4.34.1 and Mathlib v4.34.1 (pinned in `lean-toolchain` and
`lake-manifest.json`), and in the online editor with Lean v4.36.0 and v4.37.0-rc1 and their
Mathlib versions.

# Joint Learning of Models and Probabilistic Invariant Sets

This repository contains the code accompanying the paper:

> **Joint Learning of Models and Probabilistic Invariant Sets for Linear Stochastic Systems**  
> Manas Mejari, Sampath Kumar Mulagaleti, Milad Banitalebi Dehkordi, Alberto Bemporad, Dario Piga  
> *21st IFAC Symposium on System Identification (SYSID2027) and IFAC-JSC, 2026* (accepted)



## Method

Given state-transition data from an unknown stochastic linear system `x_{k+1} = A* x_k + w_k`, with `w_k ~ N(0, Q)` and state constraints `x_k ∈ X`, the code learns a model together with an ellipsoidal set `P_α = {x : x^T P x ≤ α}` with a fixed shape matrix `P`. The set should be a p-PIS (probabilistic invariant set of level `p`): if `x_0 ∈ P_α`, then `Pr(x_k ∈ P_α) ≥ p` for all `k ≥ 0`. The code solves the two parts of Problem 1 in the paper:

- **P1:** compute a **model matrix** `A` and a set parameter `α` such that `P_α ⊆ X` is a **p-PIS of smallest possible size for the model** `A`, for a prescribed probability level `p`.
- **P2:** compute a **probability level `p̃`, as large as possible**, for which `P_α` is also a certified p̃-PIS for the **true system**.

For a given model `A`, the smallest p-PIS certified by Proposition 1 is `P_α` with `α = ᾱ(A, p)` (defined below). The set designed for the best-fit (least-squares) model is minimal for that model, but its certified level for the true system may fall below `p`. Among the models compatible with the data, the method therefore looks for the **largest of these minimal sets** (obtained with a less contractive model), traded off against the data fit. Such a set accounts for the model uncertainty and is certified for the true system at a higher probability level `p̃`.

The model is computed by solving problem (23) over the set `Θ_δ` of models compatible with the data:

```
min_{A ∈ Θ_δ}   (1/N) ||X+ - A X||_F^2  -  λ ᾱ(A, p)
subject to:      ρ(A) < 1,  ᾱ(A, p) ≤ α_max
```

where
- `ᾱ(A, p) = β² c_p / (1 - ρ(A))²` (13), with `c_p = F^{-1}_{χ²_n}(p)` and `β = ||P^{1/2} Q^{1/2}||_2`, is the smallest `α` for which `P_α` is certified as a p-PIS for model `A` by condition (9) of Proposition 1. It increases with the P-metric contraction rate `ρ(A) = ||P^{1/2} A P^{-1/2}||_2`, so less contractive models have larger minimal sets.
- `Θ_δ` is the credible ellipsoid (20): it is built from the data and contains the true system matrix with posterior probability δ. `α_max` (5) is the largest `α` such that `P_α ⊆ X` (for polytopic `X = {x : Hx ≤ h}`, `α_max = min_i h_i² / (H_i^T P^{-1} H_i)`), i.e., `P_{α_max}` is the largest ellipsoid of shape `P` inside `X`.
- The regularization parameter `λ` controls the trade-off between data fit and set size. `λ = 0` recovers the least-squares (LS) estimate `Â` (when ρ(Â) ≤ ρ_max, as in the example). Larger `λ` selects less contractive models, with larger sets and higher certified levels `p̃`, at the cost of reduced model accuracy, until the solution saturates at the least contractive model allowed by the constraints.
- For the learned model `A_reg` and its set `P_{α_reg}`, with `α_reg = ᾱ(A_reg, p)`, Proposition 2 gives `p̃` in closed form (29), provided `ρ(Â) + ρ_Δ(N, δ) < 1` (28): with posterior probability at least δ, `P_{α_reg}` is a p̃-PIS for the true system (problem P2).
- In the code (`solve_joint_maximal`), the term `λ ᾱ(A, p)` is replaced by the monotone proxy `λ ρ(A)` (ᾱ is strictly increasing in ρ for ρ < 1), and the two constraints are imposed together as `ρ(A) ≤ ρ_max = 1 - β sqrt(c_p/α_max)`. The values of `λ` in the notebook refer to `λ ρ(A)`. In the code, `delta` is the miscoverage: the paper's level δ corresponds to `1 - delta` (paper δ = 0.98, code `delta = 0.02`).

---

## Code overview

### Python code (numerical example)

| File | What it does |
|---|---|
| `main.ipynb` | Runs the numerical example of Section 5: generates the data, solves the joint learning problem (23), and reproduces all figures and Table 1. |
| `pis_model_functions.py` | Core functions: ρ(A), β, ᾱ(A,p), data generation, the estimate Â, the credible set Θ_δ (20), ρ_Δ(N,δ) (27), α_max (5), the solver of problem (23), and the probability levels p* (26) and p̃ (29). |
| `empirical_probability.py` | Monte Carlo check of the certified level (Section 5.1): simulates the true system from the boundary of the set and computes the empirical probability (41)–(42). |
| `figures/` | Figures of the paper (PDF). |

### Lean code (formal proofs, folder `Lean code/`)

| File | What it does / where it is in the paper |
|---|---|
| `PISLean/Basic.lean` | Definitions: system (1), set 𝒫_α (3), confidence region 𝒲_p (7), ρ(A) and β (10), ᾱ(A,p) (13), RIS (Definition 3), p-PIS (Definition 1). Lemma 2 is stated as a hypothesis. |
| `PISLean/Proposition1.lean` | Proposition 1, with its proof steps (11) and (12). |
| `PISLean/CredibleRegion.lean` | Credible set Θ_δ (Definition 4, eqs. (18) and (20)), λ_min, ρ_Δ(N,δ) (27), and the proof steps (31)–(36): ρ(A) ≤ ρ(Â) + ρ_Δ(N,δ) for every A ∈ Θ_δ. |
| `PISLean/Proposition2.lean` | Proposition 2, with its proof steps (24)–(26) and (37). |
| `PISLean.lean` | Imports all files and prints the axioms used by the two main theorems. |
| `PISLean_all.lean` | All of the above in a single file, for the online Lean editor (see below). |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | Lean project setup (Lean 4.34.1, Mathlib v4.34.1). |

---

## Running the Python code

Requirements: `numpy`, `scipy`, `matplotlib`, `pandas`. Install them with

```bash
pip install numpy scipy matplotlib pandas
```

Open and run `main.ipynb` sequentially. The notebook reproduces all figures and the comparison table in the paper.

---

## Checking the Lean proofs

The folder `Lean code/` contains machine-checked proofs of **Proposition 1** (sufficient condition for a p-PIS) and **Proposition 2** (data-driven lower bound `p̃` on the probability level for the true system), written in [Lean 4](https://lean-lang.org) with the Mathlib library. There are two ways to check them.

**1. In the browser (no installation needed)**

1. Open the online Lean editor with the proofs already loaded by clicking [this link](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fmanasdm%2Fprobabilistic-invariance%2Fmaster%2FLean%2520code%2FPISLean_all.lean).
   To do it by hand instead, open <https://live.lean-lang.org/>, delete the example code in the editor, and paste the whole content of [`Lean code/PISLean_all.lean`](Lean%20code/PISLean_all.lean). Keep the default project "Latest Mathlib" in the menu at the top.
2. Wait about a minute while Lean checks the file. It is done when the yellow bar at the right edge of the code disappears. (A notice about code from untrusted sources may pop up; you can close it.)
3. Look at the panel on the right. There are no errors, and **All Messages** shows exactly two lines:
   `'PIS.proposition1' depends on axioms: [propext, Classical.choice, Quot.sound]` and the same line for `PIS.proposition2`. These are Lean's standard axioms, so no step of the proofs is left unproved.

**2. On your computer**

Install Lean (<https://lean-lang.org/install>) and run, inside `Lean code/`:

```bash
lake exe cache get
lake build
```

The build prints the same two lines. `Lean code/README.md` lists the verified statements, the Lean names that correspond to the paper's notation, and the two results that the paper cites and that the proofs take as hypotheses (Lemma 2 and Definition 4).

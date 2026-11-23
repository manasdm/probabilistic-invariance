# Joint Learning of Models and Probabilistic Invariant Sets

This repository contains the code accompanying the paper:

> **Joint Learning of Models and Probabilistic Invariant Sets for Linear Stochastic Systems**  
> Manas Mejari, Sampath Kumar Mulagaleti, Milad Banitalebi Dehkordi, Alberto Bemporad, Dario Piga  
> *21st IFAC Symposium on System Identification (SYSID2027) and IFAC-JSC, 2026* (accepted)



## Method

Given state-transition data from an unknown stochastic linear system `x_{k+1} = A* x_k + w_k`, with `w_k ~ N(0, Q)`, subject to state constraints, the code jointly learns:
- a **model matrix** `A` and 
- the **largest ellipsoidal probabilistic invariant set (p-PIS)** `P_α = {x : x^T P x ≤ α}` certified at a prescribed probability level `p`.  
- It also computes a certified lower bound `p̃` on the probability level for the true unknown system, accounting for model mismatch due to finite data.

The joint learning problem is solved by minimizing a regularized objective over a data-compatible model set `Θ_δ`:

```
min_{A ∈ Θ_δ}   (1/N) ||X+ - A X||_F^2  -  λ ᾱ(A, p)
subject to:      ᾱ(A, p) ≤ α_max
```

where 
- `ᾱ(A, p) = β² c_p / (1 - ρ(A))²`, with `c_p = F^{-1}_{χ²_n}(p)` and `β = ||P^{1/2} Q^{1/2}||_2`, is the smallest `α` for which `P_α` is certified as a p-PIS for model `A` by the sufficient condition of the paper (requires `ρ(A) < 1`), and `ρ(A) = ||P^{1/2} A P^{-1/2}||_2` is the P-metric contraction rate. 
- The set `Θ_δ` is a confidence ellipsoid for the true system matrix constructed from data, and `α_max` is the largest `α` such that `P_α ⊆ X` (for polytopic `X = {x : Hx ≤ h}`, `α_max = min_i h_i² / (H_i^T P^{-1} H_i)`), i.e., `P_{α_max}` is the largest ellipsoid of shape `P` inside the state constraints `X`. 
- The regularization parameter `λ` controls the trade-off between data fit and invariant set size: `λ = 0` recovers the least-squares (LS) estimate `Â` (when ρ(Â) ≤ ρ_max, as in the example), 
while larger `λ` yields larger invariant sets at the cost of reduced model accuracy. 
- In the code (`solve_joint_maximal`), the term `λ ᾱ(A, p)` is replaced by the monotone proxy `λ ρ(A)` (ᾱ is strictly increasing in ρ for ρ < 1), and `ᾱ(A, p) ≤ α_max` is imposed equivalently as `ρ(A) ≤ ρ_max = 1 - β sqrt(c_p/α_max)`. The values of `λ` in the notebook refer to `λ ρ(A)`. In the code, `delta` is the miscoverage: the paper's level δ corresponds to `1 - delta` (paper δ = 0.98, code `delta = 0.02`).

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

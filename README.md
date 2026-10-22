# Joint Learning of Models and Probabilistic Invariant Sets

This repository contains the Python code to reproduce the numerical results of the paper:

> **Joint Learning of Models and Probabilistic Invariant Sets for Linear Stochastic Systems**  
> Manas Mejari, Sampath Kumar Mulagaleti, Milad Banitalebi Dehkordi, Alberto Bemporad, Dario Piga  
> *21st IFAC Symposium on System Identification (SYSID2027) and IFAC-JSC, 2026* (submitted)

---

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

where `ᾱ(A, p) = β² c_p / (1 - ρ(A))²`, with `c_p = F^{-1}_{χ²_n}(p)` and `β = ||P^{1/2} Q^{1/2}||_2`, is the smallest `α` for which `P_α` is certified as a p-PIS for model `A` by the sufficient condition of the paper (requires `ρ(A) < 1`), and `ρ(A) = ||P^{1/2} A P^{-1/2}||_2` is the P-metric contraction rate. 
The set `Θ_δ` is a confidence ellipsoid for the true system matrix constructed from data, and `α_max` is the largest `α` such that `P_α ⊆ X` (for polytopic `X = {x : Hx ≤ h}`, `α_max = min_i h_i² / (H_i^T P^{-1} H_i)`), i.e., `P_{α_max}` is the largest ellipsoid of shape `P` inside the state constraints `X`. 
The regularization parameter `λ` controls the trade-off between data fit and invariant set size: `λ = 0` recovers the least-squares (LS) estimate `Â` (when ρ(Â) ≤ ρ_max, as in the example), 
while larger `λ` yields larger invariant sets at the cost of reduced model accuracy. 
In the code (`solve_joint_maximal`), the term `λ ᾱ(A, p)` is replaced by the monotone proxy `λ ρ(A)` (ᾱ is strictly increasing in ρ for ρ < 1), and `ᾱ(A, p) ≤ α_max` is imposed equivalently as `ρ(A) ≤ ρ_max = 1 - β sqrt(c_p/α_max)`. The values of `λ` in the notebook refer to `λ ρ(A)`. In the code, `delta` is the miscoverage: the paper's level δ corresponds to `1 - delta` (paper δ = 0.98, code `delta = 0.02`).

---

## Requirements

```
numpy
scipy
matplotlib
pandas
```

Install with:

```bash
pip install numpy scipy matplotlib pandas
```

---

## How to run

Open and run `main.ipynb` sequentially. The notebook reproduces all figures and the comparison table in the paper.


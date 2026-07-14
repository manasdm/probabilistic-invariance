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

where `ᾱ(A, p) = β² c_p / (1 - ρ(A))²` is the minimal p-PIS size for model `A`, and `ρ(A) = ||P^{1/2} A P^{-1/2}||_2` is the P-metric contraction rate. 
The set `Θ_δ` is a confidence ellipsoid for the true system matrix constructed from data, and `α_max` is the largest ellipsoid fitting inside the state constraints `X`. 
The regularization parameter `λ` controls the trade-off between data fit and invariant set size: `λ = 0` recovers the least-squares (LS) solution, 
while larger `λ` yields larger invariant sets at the cost of reduced model accuracy. 

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


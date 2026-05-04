# -*- coding: utf-8 -*-
"""
Created on Thu Apr 30 14:00:01 2026

@author: manas.mejari
"""

import numpy as np
from scipy.linalg   import sqrtm



# --------- Monte Carlo empirical invariance ------------------------------
# ══════════════════════════════════════════════════════════════════════════
#  EMPIRICAL p-PIS VALIDATION
# ══════════════════════════════════════════════════════════════════════════
def empirical_pis(A, P, alpha, Q,
                  N_init,
                  Nw,
                  T,
                  plot_steps,
                  vis_init_idx,
                  boundary_frac,
                  p_target,
                  pt_lb,
                  seed=42,
                  xlabel='$x_1$',
                  ylabel='$x_2$'
                  ):
    """
    Empirical estimation of the p-PIS probability level.

    For N_init initial conditions x0 sampled uniformly on the boundary
    of P_alpha = {x : x^T P x <= alpha}, simulate T steps of:
        x_{k+1} = A x_k + w_k,   w_k ~ N(0, Q)
    using Nw independent noise realisations per step per initial condition.

    Empirical probability at step k for initial condition i:
        p_hat_k^{(i)} = (1/Nw) sum_{j=1}^{Nw} 1[x_k^{(i,j)} in P_alpha]

    Average over initial conditions:
        p_hat_k = (1/N_init) sum_i p_hat_k^{(i)}

    Certified probability level (worst case):
        p_hat_emp = min_{k=1,...,T}  p_hat_k

    Parameters
    ----------
    A           : (n,n) system matrix A_true
    P           : (n,n) shape matrix, P > 0
    alpha       : scalar, set scaling parameter
    Q           : (n,n) noise covariance
    N_init      : number of initial conditions on boundary
    Nw          : noise realisations per step per initial condition
    T           : number of time steps
    plot_steps  : tuple of steps to highlight in scatter plot
    p_target    : target probability level (for reference line)
    pt_lb       : theoretical lower bound p_tilde (for reference line)
    vis_init_idx: index of initial condition used for scatter plot
    boundary_frac : fraction of boundary (0.99 = slightly inside)
    seed        : random seed
    xlabel/ylabel : axis labels for state space plot
    save_path   : if given, save figure to this path

    Returns
    -------
    p_hat_k     : (T,) average empirical probability at each step
    p_hat_cert  : scalar, certified probability level = min_{k} p_hat_k
    """
    np.random.seed(seed)
    n   = A.shape[0]
    Phi = np.linalg.inv(sqrtm(P).real)   # P^{-1/2}

    # ── Sample initial conditions on boundary of P_alpha ─────────────────
    # Uniform on P-ellipsoid: transform uniform Euclidean sphere via P^{-1/2}
    V  = np.random.randn(n, N_init)
    V /= np.linalg.norm(V, axis=0)                    # unit sphere
    X0 = boundary_frac * Phi @ (np.sqrt(alpha) * V)   # (n, N_init) initial conditions

    # ── Simulate and estimate probability ─────────────────────────────────
    # Loop over initial conditions; vectorise over Nw (memory-safe)
    p_hat_ki = np.zeros((T, N_init))
    inside_sum = np.zeros(T)            # accumulate total inside count
    X_vis_t  = {}   # states at plot_steps for visualisation initial condition

    for i in range(N_init):
        # Xc: (n, Nw) — Nw trajectories from x0^{(i)}
        Xc = np.tile(X0[:, i:i+1], (1, Nw))
        for k in range(T):
            W  = np.random.multivariate_normal(np.zeros(n), Q, size=Nw).T
            Xc = A @ Xc + W
            # Quadratic form: x^T P x for each column
            quad = (Xc * (P @ Xc)).sum(axis=0)          # (Nw,)
            p_hat_ki[k, i] = (quad <= alpha).mean()
            inside_sum[k]   += (quad <= alpha).sum()               # NEW: accumulate count
            # Store states for the visualisation initial condition
            if i == vis_init_idx and (k + 1) in plot_steps:
                X_vis_t[k + 1] = Xc.copy()

    # ── Aggregate ─────────────────────────────────────────────────────────
    p_hat_k    = inside_sum/(N_init*Nw)   # (T,) average over init conditions
    p_hat_cert = p_hat_k.min()          # scalar, min over k and i


 


    return p_hat_k,  p_hat_cert, X_vis_t, X0
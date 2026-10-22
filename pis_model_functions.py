# -*- coding: utf-8 -*-
r"""
Created on Thu Apr 30 13:42:16 2026

@author: manas.mejari


Functions utilized to compute a probabilistic invariant set of level p, (p-PIS) and a model matrix A
for LTI system = x^{+} = Ax+ w with w~N(0,Q)

Ellisoidal set: \mathcal{P}:= {x:x^{\top}Px<= \alpha}, compute a maximal \alpha such that this set is p-PIS 
and satisfies the state constraints \mathcal{P} \subseteq \mathcal{X}
 
"""

import numpy as np
from scipy.stats    import chi2
from scipy.linalg   import sqrtm
from scipy.optimize import minimize

# ------------- P-metric spectral quantities ------------------------

def rho(A, P):
    Ph = sqrtm(P).real
    return np.linalg.norm(Ph @ A @ np.linalg.inv(Ph), ord=2)

def beta_val(P, Q):
    return np.linalg.norm(sqrtm(P).real @ sqrtm(Q).real, ord=2)

def alpha_star(A, P, Q, p):
    #  p-PIS size: (beta * cp / (1 - rho))^2
    r = rho(A, P)  
    b = beta_val(P, Q)
    cp = np.sqrt(chi2.ppf(p, df=P.shape[0]))  # chi2.ppf(p) returns inverse cdf for a given p: Percent point function (inverse of cdf — percentiles)
    return np.inf if r >= 1.0 else (b * cp / (1.0 - r))**2

# -------------- Data generation and MLE --------------------------

def generate_data(A_true, Q, N):
    n = A_true.shape[0]
    X = np.zeros((n, N));  Xp = np.zeros((n, N))  
    x = 40*np.random.rand(n)-20  # initial conditions uniformly distributed between [-20,20]
    for k in range(N):
        w = np.random.multivariate_normal(np.zeros(n), Q)
        X[:, k] = x;  Xp[:, k] = A_true @ x + w;  x = Xp[:, k]
    return X, Xp

def compute_mle(X, Xp):
    Sx = X @ X.T  # Sigma_X = X X^T
    return Xp @ X.T @ np.linalg.inv(Sx), Sx

# ---------- Confidence ellipsoid Theta_delta -----------------

def theta_stat(A, A_hat, Q, Sx):
    # T(A) = tr(Q^{-1} (A-Ahat) Sx (A-Ahat)^T) = vec(A-Ahat)^T (Sx kron Q^{-1}) vec(A-Ahat) ~ chi2_{n^2}
    D = A - A_hat
    return np.trace(np.linalg.solve(Q, D @ Sx @ D.T))

# ------------ Mismatch bound delta_rho (Cauchy-Schwarz in P-metric) --------

def compute_delta_rho(P, Q, Sx, delta, n2):
    c_delta = np.sqrt(chi2.ppf(1 - delta, df=n2))
    Ph  = sqrtm(P).real;  Phi = np.linalg.inv(Ph)
    lQ  = np.linalg.eigvalsh(Ph @ Q  @ Ph).max()                    # = 1/lambda_min(P^{-1/2} Q^{-1} P^{-1/2})
    lSi = np.linalg.eigvalsh(Phi @ np.linalg.inv(Sx) @ Phi).max()   # = 1/lambda_min(P^{1/2} Sx P^{1/2})
    return c_delta * np.sqrt(lQ) * np.sqrt(lSi)

def rho_star(A_hat, P, Q, Sx, delta, n2):
    # rho* = min(rho_hat + delta_rho, 1) — upper bound on max_{A in Theta_delta} rho(A) (triangle ineq. + ||E||_2 <= ||E||_F)
    dr = compute_delta_rho(P, Q, Sx, delta, n2)
    return min(rho(A_hat, P) + dr, 1.0), dr

# -------State constraint: compute alpha_max -----------------------------

def alpha_max_polytopic(P, H, h):
    # X_c = {x | Hx <= h}: P_alpha ⊆ X iff
    # alpha <= min_i  h_i^2 / ||P^{-1/2} H_i||^2 = min_i h_i^2 / (H_i^T P^{-1} H_i),  H_i = i-th row of H (h_i > 0)
    Phi = np.linalg.inv(sqrtm(P).real)
    return min((h[i]**2) / np.linalg.norm(Phi @ H[i])**2 for i in range(len(h)))

def alpha_max_ellipsoidal(P, C):
    # X_c = {x | x^T C x <= 1}: P_alpha ⊆ X_c iff
    # alpha <= 1 / lmax(P^{-1/2} C P^{-1/2})
    Phi = np.linalg.inv(sqrtm(P).real)
    return 1.0 / np.linalg.eigvalsh(Phi @ C @ Phi).max()

def rho_max_from_alpha(alpha_max, P, Q, p):
    # rho(A) <= 1 - beta*cp/sqrt(alpha_max)  guarantees alpha*(A) <= alpha_max
    b = beta_val(P, Q);  cp = np.sqrt(chi2.ppf(p, df=P.shape[0]))
    return 1.0 - b * cp / np.sqrt(alpha_max)

# ----- Joint maximal PIS solver --------------------------------------------

def solve_joint_maximal(A_hat, X, Xp, Sx, P, Q, p, delta, alpha_max, lam, A_init=None):
    # min   (1/N)*||X' - AX||_F^2 - \lam*alpha*(A)
    # s.t. T(A) <= chi2_{n^2,1-delta}   [data compatibility: A in Theta_delta]
    #      rho(A) <= rho_max             [p-PIS fits inside X_c]
    # Implemented: -\lam*rho(A) replaces -\lam*alpha*(A) (monotone proxy; not equivalent for a fixed lam)
    # avoids the pole in -alpha*(A) near rho=1
    n    = P.shape[0]
    c_d2 = chi2.ppf(1 - delta, df=n**2)
    rmax = rho_max_from_alpha(alpha_max, P, Q, p)
    if rmax <= 0:
        return None, False
    # Normalise fit so lambda is scale-independent
    def obj(av):
        A = av.reshape(n, n)
        fit = np.linalg.norm(Xp - A @ X, 'fro')**2 / X.shape[1]  # per-sample
        return fit - lam * rho(A, P)
    cons = [
        {'type':'ineq','fun': lambda av:
            c_d2 - theta_stat(av.reshape(n,n), A_hat, Q, Sx)},   # For SLSQP: ineq constraints: c(x)>=0
        {'type':'ineq','fun': lambda av:
            rmax - rho(av.reshape(n,n), P)},
    ]
    # Multi-start: try A_hat, A_init (e.g. A_true), and midpoint
    inits = [A_hat]
    if A_init is not None:
        inits += [A_init, 0.5*A_hat + 0.5*A_init]
    best_res = None; best_val = np.inf
    for A0 in inits:
        res = minimize(obj, A0.flatten(), method='SLSQP',
                       constraints=cons,
                       options={'ftol':1e-12,'maxiter':10000,'disp':False})
        A_cand = res.x.reshape(n, n)
        feas = (theta_stat(A_cand,A_hat,Q,Sx) <= c_d2+1e-4 and
                rho(A_cand,P) <= rmax+1e-4)
        if feas and res.fun < best_val:
            best_val = res.fun; best_res = res
    if best_res is None:
        return None, False
    return best_res.x.reshape(n, n), True

# --------- Probability levels ------------------------------
def compute_pstar(A_true, A_reg, P,  p):
    # p_star = F_{chi2_n}(cp^2 * ((1-rho(A_star))/(1-rho_reg))^2)
    # Largest level certified (via the PIS sufficient condition) for alpha*(A_reg) on the true A_true; deterministic (no delta)
    n = A_true.shape[0];  
    r_true = rho(A_true,P)
    r_reg  = rho(A_reg, P)
    if r_true >= 1.0 or r_reg >= 1.0: return 0.0
    cp = np.sqrt(chi2.ppf(p, df=n))
    ct = cp * (1.0 - r_true) / (1.0 - r_reg)
    return chi2.cdf(ct**2, df=n) if ct > 0 else 0.0


def compute_ptilde(A_hat, A_reg, P, Q, Sx, delta, p):
    # p_tilde = F_{chi2_n}(cp^2 * ((1-rho*)/(1-rho_reg))^2)
    # Valid for alpha*(A_reg) on true plant w.p. 1-delta
    n = P.shape[0];  n2 = n**2
    rs, _ = rho_star(A_hat, P, Q, Sx, delta, n2)
    r_reg = rho(A_reg, P)
    if rs >= 1.0 or r_reg >= 1.0: return 0.0
    cp = np.sqrt(chi2.ppf(p, df=n))
    ct = cp * (1.0 - rs) / (1.0 - r_reg)
    return chi2.cdf(ct**2, df=n) if ct > 0 else 0.0

# ------- Ellipse boundary ----------------------------------------------

def ellipse_pts(P, alpha, n_pts=5000):
    th  = np.linspace(0, 2*np.pi, n_pts)
    cir = np.stack([np.cos(th), np.sin(th)])
    L   = np.linalg.cholesky(alpha * np.linalg.inv(P))
    pts = L @ cir
    return pts[0], pts[1]




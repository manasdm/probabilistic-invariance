import PISLean.Proposition1
import PISLean.CredibleRegion

/-!
# Proposition 2

> **Proposition 2** (Data-driven lower bound on `p*`). For a given probability level
> `p ∈ (0,1)`, denote `A_reg` as the optimizer of Problem (23), along with
> `α_reg = ᾱ(A_reg, p)`. Further, for a given probability level `δ ∈ (0,1)`, define
>
>     ρ_Δ(N, δ) := √(c_δ / (λ_min(Q̃⁻¹) λ_min(Σ̃)))                                    (27)
>
> with `Q̃⁻¹ = P^{-1/2} Q⁻¹ P^{-1/2}` and `Σ̃ = P^{1/2} Σ_X P^{1/2}`. If the maximum likelihood
> estimate satisfies
>
>     ρ(Â) < 1 - ρ_Δ(N, δ),                                                           (28)
>
> then, with posterior probability at least `δ` given the dataset `D`, the set `𝒫_{α_reg}` is a
> `p̃`-PIS for the true system, where
>
>     p̃ = F_{χ²_n}( c_p ((1 - (ρ(Â) + ρ_Δ(N, δ))) / (1 - ρ(A_reg)))² ) ≤ p*.            (29)

Formalization:
* In the Bayesian setting of Section 3.2 the system matrix is a random variable `A` with
  posterior distribution `π(A | D)`. Here `post` is any measure on `ℝ^{n×n}` that gives
  `Θ_δ` mass at least `δ` (Definition 4, hypothesis `hDef4`).
* `proposition2_core`: for every `A ∈ Θ_δ`, `ρ(A) < 1`, `c_{p̃} ≤ c_{p*}` (eq. (37)), and
  `𝒫_{α_reg}` is an RIS of `x_{k+1} = A x_k + w_k` for `w_k ∈ 𝒲_{p̃}`.
* `proposition2_of_mem`: for every `A ∈ Θ_δ`, `𝒫_{α_reg}` is a `p̃`-PIS for `A` and `p̃ ≤ p*`.
* `proposition2`: the statement "with posterior probability at least `δ`".

Remarks. As in the paper, Assumption 1 is not a hypothesis: on `Θ_δ`, condition (28) already
gives `ρ(A) < 1`. The only property of `A_reg` that is used is `ρ(A_reg) < 1`, and the estimate
`Â` can be any matrix (in the paper it is the estimate (16)).
-/

open Matrix MeasureTheory

noncomputable section

namespace PIS

variable {n : ℕ}

/-- Eq. (37): `c_{p̃} = c_p ((1 - (ρ(Â) + ρ_Δ)) / (1 - ρ(A_reg)))²`; then `p̃ = F_{χ²_n}(c_{p̃})`,
eq. (29). -/
def cTilde (c_p ρhat ρΔ ρreg : ℝ) : ℝ := c_p * ((1 - (ρhat + ρΔ)) / (1 - ρreg)) ^ 2

/-- Eqs. (25)–(26): `c_{p*} = c_p ((1 - ρ(A*)) / (1 - ρ(A_reg)))²`; then `p* = F_{χ²_n}(c_{p*})`. -/
def cStar (c_p ρstar ρreg : ℝ) : ℝ := c_p * ((1 - ρstar) / (1 - ρreg)) ^ 2

/-- (24) ⇔ (25), written with condition (9): for `ρ(A*) < 1`, `ρ(A_reg) < 1` and `β > 0`,
`β² c / (1 - ρ(A*))² ≤ α_reg  ↔  c ≤ c_{p*}`, where `α_reg = β² c_p / (1 - ρ(A_reg))²`. -/
theorem alphaBar_le_iff_le_cStar {ρs ρr β c c_p : ℝ} (hs : ρs < 1) (hr : ρr < 1)
    (hβ : 0 < β) :
    β ^ 2 * c / (1 - ρs) ^ 2 ≤ β ^ 2 * c_p / (1 - ρr) ^ 2 ↔ c ≤ cStar c_p ρs ρr := by
  have h1 : 0 < (1 - ρs) ^ 2 := pow_pos (by linarith) 2
  have h2 : 0 < (1 - ρr) ^ 2 := pow_pos (by linarith) 2
  have hβ2 : 0 < β ^ 2 := pow_pos hβ 2
  rw [div_le_div_iff₀ h1 h2, cStar, div_pow, ← mul_div_assoc, le_div_iff₀ h2]
  constructor
  · intro h
    exact le_of_mul_le_mul_left (by simpa only [mul_assoc] using h) hβ2
  · intro h
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h hβ2.le

/-- (24) ⇔ (25): with `α_reg = β² c_p / (1 - ρ(A_reg))²`,
`ρ(A*) √α_reg + β √c ≤ √α_reg  ↔  c ≤ c_{p*}`. -/
theorem eq24_iff_eq25 {ρs ρr β c c_p : ℝ} (hs : ρs < 1) (hr : ρr < 1) (hβ : 0 < β)
    (hc : 0 ≤ c) (hcp : 0 ≤ c_p) :
    ρs * √(β ^ 2 * c_p / (1 - ρr) ^ 2) + β * √c ≤ √(β ^ 2 * c_p / (1 - ρr) ^ 2) ↔
      c ≤ cStar c_p ρs ρr := by
  rw [eq12 hs hβ.le hc (by positivity), alphaBar_le_iff_le_cStar hs hr hβ]

/-- **Proposition 2, deterministic core.** Assume `ρ(A_reg) < 1`, `α_reg = ᾱ(A_reg, p)` and (28).
Then every `A ∈ Θ_δ` satisfies:
1. `ρ(A) < 1` (Assumption 1 holds automatically on `Θ_δ`);
2. `c_{p̃} ≤ c_{p*}`, eq. (37) (hence `p̃ ≤ p*`);
3. `𝒫_{α_reg}` is an RIS of `x_{k+1} = A x_k + w_k` for `w_k ∈ 𝒲_{p̃} = {wᵀQ⁻¹w ≤ c_{p̃}}`. -/
theorem proposition2_core {P Q Ph Qh SigX Ahat Areg : Mat n}
    (hP : IsSqrt Ph P) (hQ : IsSqrt Qh Q) (hSig : SigX.PosDef) {c_p cδ : ℝ} (hcp : 0 ≤ c_p)
    (hreg : rho Ph Areg < 1) (h28 : rho Ph Ahat < 1 - rhoDelta Ph Q SigX cδ)
    {A : Mat n} (hA : A ∈ credibleSet Q SigX Ahat cδ) :
    rho Ph A < 1 ∧
      cTilde c_p (rho Ph Ahat) (rhoDelta Ph Q SigX cδ) (rho Ph Areg) ≤
        cStar c_p (rho Ph A) (rho Ph Areg) ∧
      IsRIS A (ellipsoid P (alphaBar Ph Qh Areg c_p))
        (confRegion Q (cTilde c_p (rho Ph Ahat) (rhoDelta Ph Q SigX cδ) (rho Ph Areg))) := by
  -- (31)–(36): `ρ(A) ≤ ρ(Â) + ρ_Δ(N, δ)`
  have hA' := rho_le_of_mem_credibleSet hP hQ hSig hA
  -- Assumption 1 holds on `Θ_δ`
  have hA1 : rho Ph A < 1 := by linarith
  -- (37): `c_{p̃} ≤ c_{p*}`
  have hle : cTilde c_p (rho Ph Ahat) (rhoDelta Ph Q SigX cδ) (rho Ph Areg) ≤
      cStar c_p (rho Ph A) (rho Ph Areg) := by
    unfold cTilde cStar
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ 2) hcp
    · exact div_nonneg (by linarith) (by linarith)
    · exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  refine ⟨hA1, hle, proposition1_RIS hP hQ A (mul_nonneg hcp (sq_nonneg _)) hA1 ?_⟩
  -- (25) ⇒ (24): condition (9) for `A`, the set `𝒫_{α_reg}` and the level `c_{p̃}`
  rcases (beta_nonneg Ph Qh).eq_or_lt with hβ | hβ
  · simp [alphaBar, ← hβ]
  · exact (alphaBar_le_iff_le_cStar hA1 hreg hβ).2 hle

/-- **Proposition 2 on the event `A ∈ Θ_δ`.** If the system matrix `A` lies in `Θ_δ`, then
`𝒫_{α_reg}` is a `p̃`-PIS for `x_{k+1} = A x_k + w_k`, with `p̃ = F(c_{p̃})` as in (29), and
`p̃ ≤ p* = F(c_{p*})` as in (26). -/
theorem proposition2_of_mem {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    (w : ℕ → Ω → Vec n) {P Q Ph Qh SigX Ahat Areg : Mat n} (hP : IsSqrt Ph P)
    (hQ : IsSqrt Qh Q) (hSig : SigX.PosDef) (F : ℝ → ℝ) (hF : Monotone F)
    (hLemma2 : Lemma2 Pr w Q F) {c_p cδ : ℝ} (hcp : 0 < c_p)
    (hreg : rho Ph Areg < 1) (h28 : rho Ph Ahat < 1 - rhoDelta Ph Q SigX cδ)
    {A : Mat n} (hA : A ∈ credibleSet Q SigX Ahat cδ) :
    IsPIS Pr w A (ellipsoid P (alphaBar Ph Qh Areg c_p))
        (F (cTilde c_p (rho Ph Ahat) (rhoDelta Ph Q SigX cδ) (rho Ph Areg))) ∧
      F (cTilde c_p (rho Ph Ahat) (rhoDelta Ph Q SigX cδ) (rho Ph Areg)) ≤
        F (cStar c_p (rho Ph A) (rho Ph Areg)) := by
  obtain ⟨-, hle, hRIS⟩ := proposition2_core hP hQ hSig hcp.le hreg h28 hA
  have h1 : 0 < 1 - (rho Ph Ahat + rhoDelta Ph Q SigX cδ) := by linarith
  have h2 : 0 < 1 - rho Ph Areg := by linarith
  have hct : 0 < cTilde c_p (rho Ph Ahat) (rhoDelta Ph Q SigX cδ) (rho Ph Areg) :=
    mul_pos hcp (pow_pos (div_pos h1 h2) 2)
  exact ⟨hLemma2 A _ _ hct hRIS, hF hle⟩

/-- **Proposition 2** (data-driven lower bound on `p*`).

Setting: `P = Pᵀ ≻ 0` and `Q = Qᵀ ≻ 0` with square roots `Ph = P^{1/2}`, `Qh = Q^{1/2}`;
`Σ_X ≻ 0` (`Σ_X = X Xᵀ`, persistent excitation); the noise `w` satisfies Lemma 2 with a monotone
`F` (`F = F_{χ²_n}`); `c_p > 0` (`c_p = F⁻¹_{χ²_n}(p)`); `A_reg` is the learned model, with
`ρ(A_reg) < 1` and `α_reg = ᾱ(A_reg, p)`; `post` is the posterior distribution `π(A | D)` of the
system matrix, with `Pr(A ∈ Θ_δ | D) ≥ δ` (Definition 4).

If (28) holds, then with posterior probability at least `δ` the set `𝒫_{α_reg}` is a `p̃`-PIS for
the system `x_{k+1} = A x_k + w_k`, where `p̃` is given by (29), and `p̃ ≤ p*` with `p*` as in
(26). -/
theorem proposition2 {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) (w : ℕ → Ω → Vec n)
    {P Q Ph Qh SigX Ahat : Mat n} (hP : IsSqrt Ph P) (hQ : IsSqrt Qh Q) (hSig : SigX.PosDef)
    (F : ℝ → ℝ) (hF : Monotone F) (hLemma2 : Lemma2 Pr w Q F) {c_p : ℝ} (hcp : 0 < c_p)
    (Areg : Mat n) (hreg : rho Ph Areg < 1)
    (αreg : ℝ) (hαreg : αreg = alphaBar Ph Qh Areg c_p)
    (cδ ρΔ : ℝ) (h27 : ρΔ = rhoDelta Ph Q SigX cδ)
    (h28 : rho Ph Ahat < 1 - ρΔ)
    (pTilde : ℝ) (h29 : pTilde = F (c_p * ((1 - (rho Ph Ahat + ρΔ)) / (1 - rho Ph Areg)) ^ 2))
    (post : Measure (Mat n)) {δ : ℝ}
    (hDef4 : ENNReal.ofReal δ ≤ post (credibleSet Q SigX Ahat cδ)) :
    ENNReal.ofReal δ ≤ post {A | IsPIS Pr w A (ellipsoid P αreg) pTilde ∧
      pTilde ≤ F (c_p * ((1 - rho Ph A) / (1 - rho Ph Areg)) ^ 2)} := by
  subst hαreg h27 h29
  refine hDef4.trans (measure_mono fun A hA => ?_)
  exact proposition2_of_mem Pr w hP hQ hSig F hF hLemma2 hcp hreg h28 hA

end PIS

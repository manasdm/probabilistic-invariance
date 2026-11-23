import PISLean.Basic

/-!
# Proposition 1

> **Proposition 1.** For a given model matrix `A` and probability level `p ∈ (0,1)`, the set
> `𝒫_α` in (3) is a `p`-PIS for the dynamics `x_{k+1} = A x_k + w_k`, with `w_k ∼ 𝒩(0, Q)`, if
>
>     ρ(A) < 1,     β² c_p / (1 - ρ(A))² ≤ α,                                    (9)
>
> where `ρ(A) = ‖P^{1/2} A P^{-1/2}‖₂`, `β = ‖P^{1/2} Q^{1/2}‖₂` (10) and `c_p = F⁻¹_{χ²_n}(p)`.

The formal proof follows the proof in the paper:
* `eq12`             : the scalar equivalence (12);
* `eq11`             : the one-step invariance condition (11), via the change of variables
                        `z = P^{1/2} x`, `y = Q^{-1/2} w` and the triangle inequality;
* `proposition1_RIS` : `𝒫_α` is an RIS for `w_k ∈ 𝒲_p` (Definition 3);
* `proposition1`     : with Lemma 2, `𝒫_α` is a `p`-PIS (Definition 1).
-/

open Matrix MeasureTheory

noncomputable section

namespace PIS

variable {n : ℕ}

/-- Eq. (12): for `ρ < 1` and `β, c, α ≥ 0`,
`ρ √α + β √c ≤ √α  ↔  β² c / (1 - ρ)² ≤ α`. -/
theorem eq12 {ρ β c α : ℝ} (hρ : ρ < 1) (hβ : 0 ≤ β) (hc : 0 ≤ c) (hα : 0 ≤ α) :
    ρ * √α + β * √c ≤ √α ↔ β ^ 2 * c / (1 - ρ) ^ 2 ≤ α := by
  have h1 : 0 < 1 - ρ := by linarith
  -- both sides of `β √c ≤ (1 - ρ) √α` are nonnegative, so this inequality may be squared
  have key : (β * √c) ^ 2 ≤ ((1 - ρ) * √α) ^ 2 ↔ β * √c ≤ (1 - ρ) * √α :=
    sq_le_sq₀ (by positivity) (by positivity)
  rw [mul_pow, mul_pow, Real.sq_sqrt hc, Real.sq_sqrt hα] at key
  have e : (1 - ρ) * √α = √α - ρ * √α := by ring
  rw [div_le_iff₀ (by positivity), mul_comm α, key]
  constructor <;> intro h <;> linarith [e]

/-- Eq. (11): under (9), one step of `x⁺ = A x + w` maps `𝒫_α × 𝒲` into `𝒫_α`, where
`𝒲 = {wᵀQ⁻¹w ≤ c}`. -/
theorem eq11 {P Q Ph Qh A : Mat n} (hP : IsSqrt Ph P) (hQ : IsSqrt Qh Q) {α c : ℝ}
    (hc : 0 ≤ c) (hρ : rho Ph A < 1)
    (hα : beta Ph Qh ^ 2 * c / (1 - rho Ph A) ^ 2 ≤ α) :
    ∀ x ∈ ellipsoid P α, ∀ w ∈ confRegion Q c, A *ᵥ x + w ∈ ellipsoid P α := by
  intro x hx w hw
  have hα0 : 0 ≤ α := le_trans (by positivity) hα
  -- the scalar condition (12)
  have h12 : rho Ph A * √α + beta Ph Qh * √c ≤ √α :=
    (eq12 hρ (beta_nonneg Ph Qh) hc hα0).2 hα
  -- change of variables `z = P^{1/2} x`, `y = Q^{-1/2} w`: then `‖z‖₂ ≤ √α`, `‖y‖₂ ≤ √c`
  have hz : vnorm (Ph *ᵥ x) ≤ √α := by
    refine (Real.le_sqrt (vnorm_nonneg _) hα0).2 ?_
    rw [← hP.quad_eq]
    exact hx
  have hy : vnorm (Qh⁻¹ *ᵥ w) ≤ √c := by
    refine (Real.le_sqrt (vnorm_nonneg _) hc).2 ?_
    rw [← hQ.quad_inv_eq]
    exact hw
  -- `P^{1/2} (A x + w) = (P^{1/2} A P^{-1/2}) z + (P^{1/2} Q^{1/2}) y`
  have hdec : Ph *ᵥ (A *ᵥ x + w) =
      (Ph * A * Ph⁻¹) *ᵥ (Ph *ᵥ x) + (Ph * Qh) *ᵥ (Qh⁻¹ *ᵥ w) := by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc (Ph * A), hP.inv_mul, Matrix.mul_one,
      Matrix.mul_assoc Ph Qh, hQ.mul_inv, Matrix.mul_one, mulVec_add, mulVec_mulVec]
  -- triangle inequality and (12)
  have hb : vnorm (Ph *ᵥ (A *ᵥ x + w)) ≤ √α := by
    rw [hdec]
    calc _ ≤ vnorm ((Ph * A * Ph⁻¹) *ᵥ (Ph *ᵥ x)) + vnorm ((Ph * Qh) *ᵥ (Qh⁻¹ *ᵥ w)) :=
          vnorm_add_le _ _
      _ ≤ rho Ph A * vnorm (Ph *ᵥ x) + beta Ph Qh * vnorm (Qh⁻¹ *ᵥ w) :=
          add_le_add (vnorm_mulVec_le _ _) (vnorm_mulVec_le _ _)
      _ ≤ rho Ph A * √α + beta Ph Qh * √c :=
          add_le_add (mul_le_mul_of_nonneg_left hz (rho_nonneg _ _))
            (mul_le_mul_of_nonneg_left hy (beta_nonneg _ _))
      _ ≤ √α := h12
  -- hence `(A x + w)ᵀ P (A x + w) = ‖P^{1/2} (A x + w)‖₂² ≤ α`
  show (A *ᵥ x + w) ⬝ᵥ (P *ᵥ (A *ᵥ x + w)) ≤ α
  rw [hP.quad_eq]
  calc vnorm (Ph *ᵥ (A *ᵥ x + w)) ^ 2 ≤ (√α) ^ 2 := pow_le_pow_left₀ (vnorm_nonneg _) hb 2
    _ = α := Real.sq_sqrt hα0

/-- **Proposition 1, robust part.** Under (9), `𝒫_α` is a robust invariant set
(Definition 3) of `x_{k+1} = A x_k + w_k` for all disturbances `w_k ∈ 𝒲_p = {wᵀQ⁻¹w ≤ c_p}`. -/
theorem proposition1_RIS {P Q Ph Qh : Mat n} (hP : IsSqrt Ph P) (hQ : IsSqrt Qh Q)
    (A : Mat n) {c_p α : ℝ} (hcp : 0 ≤ c_p) (hρ : rho Ph A < 1)
    (hα : beta Ph Qh ^ 2 * c_p / (1 - rho Ph A) ^ 2 ≤ α) :
    IsRIS A (ellipsoid P α) (confRegion Q c_p) :=
  isRIS_of_step (eq11 hP hQ hcp hρ hα)

/-- **Proposition 1.** Let `P = Pᵀ ≻ 0` and `Q = Qᵀ ≻ 0` with square roots `Ph = P^{1/2}`,
`Qh = Q^{1/2}`, let the noise `w` satisfy Lemma 2 (`hLemma2`, with `F = F_{χ²_n}` for
`w_k ∼ 𝒩(0, Q)` i.i.d.), and let `c_p` be the level-`p` constant, `F(c_p) = p`
(i.e. `c_p = F⁻¹_{χ²_n}(p)`). If (9) holds, i.e. `ρ(A) < 1` and `β² c_p / (1 - ρ(A))² ≤ α`,
then `𝒫_α` is a `p`-PIS for `x_{k+1} = A x_k + w_k`. -/
theorem proposition1 {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) (w : ℕ → Ω → Vec n)
    {P Q Ph Qh : Mat n} (hP : IsSqrt Ph P) (hQ : IsSqrt Qh Q)
    (F : ℝ → ℝ) (hLemma2 : Lemma2 Pr w Q F)
    (A : Mat n) {p c_p α : ℝ} (hcp : 0 < c_p) (hFcp : F c_p = p)
    (hρ : rho Ph A < 1) (hα : beta Ph Qh ^ 2 * c_p / (1 - rho Ph A) ^ 2 ≤ α) :
    IsPIS Pr w A (ellipsoid P α) p := by
  have h := hLemma2 A (ellipsoid P α) c_p hcp (proposition1_RIS hP hQ A hcp.le hρ hα)
  rwa [hFcp] at h

/-- Remark after (13): `𝒫_{ᾱ(A,p)}` is a `p`-PIS. By definition of `ᾱ`, condition (9) holds
exactly for `α ≥ ᾱ(A,p)`, so this is the smallest set of shape `P` certified by (9). -/
theorem proposition1_alphaBar {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    (w : ℕ → Ω → Vec n) {P Q Ph Qh : Mat n} (hP : IsSqrt Ph P) (hQ : IsSqrt Qh Q)
    (F : ℝ → ℝ) (hLemma2 : Lemma2 Pr w Q F)
    (A : Mat n) {p c_p : ℝ} (hcp : 0 < c_p) (hFcp : F c_p = p) (hρ : rho Ph A < 1) :
    IsPIS Pr w A (ellipsoid P (alphaBar Ph Qh A c_p)) p :=
  proposition1 Pr w hP hQ F hLemma2 A hcp hFcp hρ le_rfl

end PIS

import Mathlib

/-!
# Basic definitions

Lean formalization accompanying the paper

  M. Mejari, S. K. Mulagaleti, M. Banitalebi Dehkordi, A. Bemporad, D. Piga,
  *Joint Learning of Models and Probabilistic Invariant Sets for Linear Stochastic Systems*,
  IFAC Journal of Systems and Control, 2026.

This file contains the objects of Sections 2 and 3 of the paper.

| paper                                     | Lean                                         |
|-------------------------------------------|----------------------------------------------|
| `ℝⁿ`, `ℝ^{n×n}`                           | `Vec n` (`= Fin n → ℝ`), `Mat n`             |
| `xᵀ P x`                                  | `x ⬝ᵥ (P *ᵥ x)`                              |
| `‖x‖₂`, `‖M‖₂`, `‖M‖_F`                   | `vnorm x`, `specNorm M`, `frobNorm M`        |
| `P^{1/2}`, `P^{-1/2}`                     | `Ph` with `IsSqrt Ph P`, and `Ph⁻¹`          |
| `Q^{1/2}`, `Q^{-1/2}`                     | `Qh` with `IsSqrt Qh Q`, and `Qh⁻¹`          |
| `𝒫_α`, eq. (3)                            | `ellipsoid P α`                              |
| `𝒲_p`, eq. (7) (zero mean)                | `confRegion Q c_p`                           |
| `ρ(A)`, `β`, eq. (10)                     | `rho Ph A`, `beta Ph Qh`                     |
| `ᾱ(A, p)`, eq. (13)                       | `alphaBar Ph Qh A c_p`                       |
| system (1), Definitions 1 and 3           | `traj`, `IsPIS`, `IsRIS`                     |
| Lemma 2 (cited from Hewing et al., 2018)  | hypothesis `Lemma2`                          |
-/

open Matrix MeasureTheory

noncomputable section

namespace PIS

/-- Vectors of `ℝⁿ`. -/
abbrev Vec (n : ℕ) := Fin n → ℝ

/-- Real `n × n` matrices. -/
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

variable {n : ℕ}

/-! ## Norms -/

/-- Euclidean norm `‖x‖₂ = √(xᵀx)`. -/
def vnorm (x : Vec n) : ℝ := ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖

/-- Spectral norm `‖M‖₂`: the operator norm of `M` acting on `(ℝⁿ, ‖·‖₂)`. -/
def specNorm (M : Mat n) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖

/-- Squared Frobenius norm `‖M‖_F² = ∑ᵢⱼ Mᵢⱼ²`. -/
def frobSq (M : Mat n) : ℝ := ∑ i, ∑ j, M i j ^ 2

/-- Frobenius norm `‖M‖_F`. -/
def frobNorm (M : Mat n) : ℝ := √(frobSq M)

lemma vnorm_nonneg (x : Vec n) : 0 ≤ vnorm x := norm_nonneg _

lemma vnorm_sq (x : Vec n) : vnorm x ^ 2 = x ⬝ᵥ x := by
  rw [vnorm, EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

lemma vnorm_ne_zero {x : Vec n} (hx : x ≠ 0) : vnorm x ≠ 0 := by
  simpa [vnorm] using hx

lemma vnorm_add_le (x y : Vec n) : vnorm (x + y) ≤ vnorm x + vnorm y := by
  simpa only [vnorm, WithLp.toLp_add] using norm_add_le _ _

/-- `‖M x‖₂ ≤ ‖M‖₂ ‖x‖₂`. -/
lemma vnorm_mulVec_le (M : Mat n) (x : Vec n) : vnorm (M *ᵥ x) ≤ specNorm M * vnorm x := by
  simpa [vnorm, specNorm] using (Matrix.toEuclideanCLM (𝕜 := ℝ) M).le_opNorm (WithLp.toLp 2 x)

lemma specNorm_nonneg (M : Mat n) : 0 ≤ specNorm M := norm_nonneg _

lemma specNorm_add_le (A B : Mat n) : specNorm (A + B) ≤ specNorm A + specNorm B := by
  simpa only [specNorm, map_add] using norm_add_le _ _

lemma specNorm_zero : specNorm (0 : Mat n) = 0 := by
  simp [specNorm]

lemma frobSq_nonneg (M : Mat n) : 0 ≤ frobSq M := by
  unfold frobSq
  positivity

/-- `‖M‖₂ ≤ ‖M‖_F` (used in eq. (36)). -/
lemma specNorm_le_frobNorm (M : Mat n) : specNorm M ≤ frobNorm M := by
  unfold specNorm frobNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, Real.sq_sqrt (frobSq_nonneg M),
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, frobSq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : (Matrix.toEuclideanCLM (𝕜 := ℝ) M x) i = ∑ j, M i j * x j := by
    simp [Matrix.mulVec, dotProduct]
  rw [h]
  -- Cauchy–Schwarz inequality
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-! ## Square roots of positive definite matrices -/

/-- `S` is a symmetric invertible square root of `M`, i.e. `Sᵀ = S`, `S S = M`, `det S ≠ 0`.
The principal square root `M^{1/2}` of a positive definite matrix `M` has these properties, and
conversely they imply that `M` is positive definite (`IsSqrt.posDef`).
The matrices `P^{1/2}` and `Q^{1/2}` of the paper enter the statements as such matrices. -/
structure IsSqrt (S M : Mat n) : Prop where
  symm : Sᵀ = S
  mul_self : S * S = M
  isUnit_det : IsUnit S.det

namespace IsSqrt

variable {S M : Mat n}

lemma inv_mul (h : IsSqrt S M) : S⁻¹ * S = 1 := nonsing_inv_mul S h.isUnit_det

lemma mul_inv (h : IsSqrt S M) : S * S⁻¹ = 1 := mul_nonsing_inv S h.isUnit_det

lemma inv_symm (h : IsSqrt S M) : (S⁻¹)ᵀ = S⁻¹ := by
  rw [transpose_nonsing_inv, h.symm]

lemma isUnit_inv_det (h : IsSqrt S M) : IsUnit (S⁻¹).det :=
  isUnit_nonsing_inv_det S h.isUnit_det

/-- `xᵀ M x = ‖S x‖₂²`. -/
lemma quad_eq (h : IsSqrt S M) (x : Vec n) : x ⬝ᵥ (M *ᵥ x) = vnorm (S *ᵥ x) ^ 2 := by
  rw [vnorm_sq, ← h.mul_self, ← mulVec_mulVec, dotProduct_mulVec x S (S *ᵥ x),
    ← mulVec_transpose, h.symm]

/-- `xᵀ M⁻¹ x = ‖S⁻¹ x‖₂²`. -/
lemma quad_inv_eq (h : IsSqrt S M) (x : Vec n) : x ⬝ᵥ (M⁻¹ *ᵥ x) = vnorm (S⁻¹ *ᵥ x) ^ 2 := by
  rw [vnorm_sq, ← h.mul_self, Matrix.mul_inv_rev, ← mulVec_mulVec,
    dotProduct_mulVec x S⁻¹ (S⁻¹ *ᵥ x), ← mulVec_transpose, h.inv_symm]

lemma mulVec_ne_zero (h : IsSqrt S M) {x : Vec n} (hx : x ≠ 0) : S *ᵥ x ≠ 0 := by
  intro h0
  apply hx
  rw [← one_mulVec x, ← h.inv_mul, ← mulVec_mulVec, h0, mulVec_zero]

/-- The hypotheses `IsSqrt S M` imply that `M` is positive definite. -/
lemma posDef (h : IsSqrt S M) : M.PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · show Mᴴ = M
    rw [conjTranspose_eq_transpose_of_trivial, ← h.mul_self, transpose_mul, h.symm]
  · rw [star_trivial, h.quad_eq]
    exact pow_pos ((vnorm_nonneg _).lt_of_ne (vnorm_ne_zero (h.mulVec_ne_zero hx)).symm) 2

end IsSqrt

/-! ## The objects of the paper -/

/-- Eq. (3): the ellipsoid `𝒫_α = {x ∈ ℝⁿ | xᵀ P x ≤ α}`. -/
def ellipsoid (P : Mat n) (α : ℝ) : Set (Vec n) := {x | x ⬝ᵥ (P *ᵥ x) ≤ α}

/-- Eq. (7) for zero-mean noise: the confidence region `{w | wᵀ Q⁻¹ w ≤ c}`;
for `c = c_p = F⁻¹_{χ²_n}(p)` this is `𝒲_p`. -/
def confRegion (Q : Mat n) (c : ℝ) : Set (Vec n) := {w | w ⬝ᵥ (Q⁻¹ *ᵥ w) ≤ c}

/-- Eq. (10): the contraction rate `ρ(A) = ‖P^{1/2} A P^{-1/2}‖₂` (here `Ph = P^{1/2}`). -/
def rho (Ph A : Mat n) : ℝ := specNorm (Ph * A * Ph⁻¹)

/-- Eq. (10): `β = ‖P^{1/2} Q^{1/2}‖₂` (here `Ph = P^{1/2}`, `Qh = Q^{1/2}`). -/
def beta (Ph Qh : Mat n) : ℝ := specNorm (Ph * Qh)

/-- Eq. (13): `ᾱ(A, p) = β² c_p / (1 - ρ(A))²`, where `c_p = F⁻¹_{χ²_n}(p)`. -/
def alphaBar (Ph Qh A : Mat n) (c_p : ℝ) : ℝ := beta Ph Qh ^ 2 * c_p / (1 - rho Ph A) ^ 2

lemma rho_nonneg (Ph A : Mat n) : 0 ≤ rho Ph A := specNorm_nonneg _

lemma beta_nonneg (Ph Qh : Mat n) : 0 ≤ beta Ph Qh := specNorm_nonneg _

/-! ## Robust and probabilistic invariance -/

/-- The state sequence of `x_{k+1} = A x_k + w_k` (system (1)) started at `x₀`, for the
disturbance sequence `w`. -/
def traj (A : Mat n) (x₀ : Vec n) (w : ℕ → Vec n) : ℕ → Vec n
  | 0 => x₀
  | k + 1 => A *ᵥ traj A x₀ w k + w k

/-- Definition 3 (RIS): `x₀ ∈ 𝒫 ⇒ x_k ∈ 𝒫` for all `w_k ∈ 𝒲` and all `k ≥ 0`. -/
def IsRIS (A : Mat n) (Pset Wset : Set (Vec n)) : Prop :=
  ∀ x₀ ∈ Pset, ∀ w : ℕ → Vec n, (∀ k, w k ∈ Wset) → ∀ k, traj A x₀ w k ∈ Pset

/-- Definition 1 (`p`-PIS): `x₀ ∈ 𝒫 ⇒ Pr(x_k ∈ 𝒫) ≥ p` for all `k ≥ 0`. The disturbance is a
random process `w : ℕ → Ω → ℝⁿ` on a probability space `(Ω, Pr)`. -/
def IsPIS {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) (w : ℕ → Ω → Vec n)
    (A : Mat n) (Pset : Set (Vec n)) (p : ℝ) : Prop :=
  ∀ x₀ ∈ Pset, ∀ k, ENNReal.ofReal p ≤ Pr {ω | traj A x₀ (fun j => w j ω) k ∈ Pset}

/-- **Lemma 2** of the paper (Hewing et al., 2018, Corollary 4), cited there without proof.
For every system matrix `A` and every set `𝒫`: if `𝒫` is an RIS with respect to the confidence
region `{wᵀQ⁻¹w ≤ c}`, then `𝒫` is an `F(c)`-PIS for the system driven by the noise `w`.
For `w_k` i.i.d. `𝒩(0, Q)` one takes `F = F_{χ²_n}` (the `χ²_n` CDF), so that for
`c = c_p = F⁻¹_{χ²_n}(p)` this reads "RIS for `w_k ∈ 𝒲_p` ⇒ `p`-PIS".
Mathlib has no `χ²` distribution, so `F` is kept abstract and this cited result is an explicit
hypothesis of Propositions 1 and 2. -/
def Lemma2 {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) (w : ℕ → Ω → Vec n)
    (Q : Mat n) (F : ℝ → ℝ) : Prop :=
  ∀ (A : Mat n) (Pset : Set (Vec n)) (c : ℝ), 0 < c →
    IsRIS A Pset (confRegion Q c) → IsPIS Pr w A Pset (F c)

/-- Sanity check: the hypothesis `Lemma2` is not contradictory (it holds, e.g., for zero noise
and `F ≡ 1`), so the theorems that assume it are not vacuous. For i.i.d. `𝒩(0, Q)` noise and
`F = F_{χ²_n}` it is the result of Hewing et al. (2018). -/
theorem lemma2_zero_noise {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (Q : Mat n) : Lemma2 Pr (fun _ _ => 0) Q (fun _ => 1) := by
  intro A Pset c hc hRIS x₀ hx₀ k
  have h0 : ∀ _ : ℕ, (0 : Vec n) ∈ confRegion Q c := fun _ => by
    simp [confRegion, hc.le]
  have hk : traj A x₀ (fun _ => 0) k ∈ Pset := hRIS x₀ hx₀ (fun _ => 0) h0 k
  simp [hk]

/-- One-step invariance (`x ∈ 𝒫`, `w ∈ 𝒲` ⇒ `A x + w ∈ 𝒫`) implies robust invariance. -/
lemma isRIS_of_step {A : Mat n} {Pset Wset : Set (Vec n)}
    (h : ∀ x ∈ Pset, ∀ w ∈ Wset, A *ᵥ x + w ∈ Pset) : IsRIS A Pset Wset := by
  intro x₀ hx₀ w hw k
  induction k with
  | zero => exact hx₀
  | succ k ih => exact h _ ih _ (hw k)

end PIS

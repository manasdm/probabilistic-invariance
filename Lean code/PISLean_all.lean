import Mathlib

/-!
# Lean verification of Propositions 1 and 2 (single-file version)

All Lean code of this project in one file, for the online editor https://live.lean-lang.org/
(paste this file there, keep the default "Latest Mathlib" project, and wait until Lean has
checked it). It is the concatenation of `PISLean/Basic.lean`, `PISLean/Proposition1.lean`,
`PISLean/CredibleRegion.lean`, `PISLean/Proposition2.lean` and `PISLean.lean`.
The last two lines print the axioms used by the two main theorems; the expected output is
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
-/

-- ════════════ PISLean/Basic.lean ════════════

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

end

-- ════════════ PISLean/Proposition1.lean ════════════

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

end

-- ════════════ PISLean/CredibleRegion.lean ════════════

/-!
# The credible set `Θ_δ` and the bound `ρ_Δ(N, δ)`

Definition 4 (eq. (20)), eq. (27), and the matrix steps (31)–(36) of the proof of
Proposition 2. Main result:

* `rho_le_of_mem_credibleSet` : every `A ∈ Θ_δ` satisfies `ρ(A) ≤ ρ(Â) + ρ_Δ(N, δ)`.

`λ_min` is defined through the Rayleigh quotient (Rayleigh–Ritz) and is shown to be the smallest
eigenvalue (`lambdaMin_le_of_eigen`, `exists_eigen_lambdaMin`).
-/

open Matrix
open scoped Kronecker

noncomputable section

namespace PIS

variable {n : ℕ}

/-! ## The credible set (Definition 4) -/

/-- Definition 4, eq. (20): `Θ_δ = {A | tr(Q⁻¹ (A - Â) Σ_X (A - Â)ᵀ) ≤ c_δ}`, with
`c_δ = F⁻¹_{χ²_{n²}}(δ)`. -/
def credibleSet (Q SigX Ahat : Mat n) (cδ : ℝ) : Set (Mat n) :=
  {A | (Q⁻¹ * (A - Ahat) * SigX * (A - Ahat)ᵀ).trace ≤ cδ}

/-- Trace form = Kronecker form: `tr(M E N Eᵀ) = vec(E)ᵀ (N ⊗ M) vec(E)` for symmetric `N`
(`vec` is the column-wise vectorization). This identity is used in (18) and (34). -/
theorem trace_eq_vec_kron (M E N : Mat n) (hN : Nᵀ = N) :
    (M * E * N * Eᵀ).trace = vec E ⬝ᵥ ((N ⊗ₖ M) *ᵥ vec E) := by
  rw [kronecker_mulVec_vec, vec_dotProduct_vec, hN, Matrix.trace_mul_comm]

/-- Eq. (18): `Θ_δ = {A | vec(A - Â)ᵀ (Σ_X ⊗ Q⁻¹) vec(A - Â) ≤ c_δ}`, i.e. `Θ_δ` is the
`χ²_{n²}` credible ellipsoid of the posterior `𝒩(vec Â, Σ_X⁻¹ ⊗ Q)` of Lemma 3. -/
theorem mem_credibleSet_iff {Q SigX Ahat : Mat n} (hSig : SigXᵀ = SigX) {cδ : ℝ} {A : Mat n} :
    A ∈ credibleSet Q SigX Ahat cδ ↔
      vec (A - Ahat) ⬝ᵥ ((SigX ⊗ₖ Q⁻¹) *ᵥ vec (A - Ahat)) ≤ cδ := by
  show (Q⁻¹ * (A - Ahat) * SigX * (A - Ahat)ᵀ).trace ≤ cδ ↔ _
  rw [trace_eq_vec_kron _ _ _ hSig]

/-! ## Minimum eigenvalue -/

/-- The Rayleigh quotient `vᵀ M v / vᵀ v`. -/
def rayleigh (M : Mat n) (v : Vec n) : ℝ := (v ⬝ᵥ (M *ᵥ v)) / (v ⬝ᵥ v)

/-- `λ_min(M)`: the minimum of the Rayleigh quotient `vᵀ M v / vᵀ v` over `v ≠ 0`
(Rayleigh–Ritz). For a symmetric `M` this is the smallest eigenvalue of `M`, see
`lambdaMin_le_of_eigen` and `exists_eigen_lambdaMin`. -/
def lambdaMin (M : Mat n) : ℝ := ⨅ v : {v : Vec n // v ≠ 0}, rayleigh M v

lemma dot_self_pos {v : Vec n} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  rw [← vnorm_sq]
  exact pow_pos ((vnorm_nonneg v).lt_of_ne (vnorm_ne_zero hv).symm) 2

lemma rayleigh_smul (M : Mat n) (v : Vec n) {c : ℝ} (hc : c ≠ 0) :
    rayleigh M (c • v) = rayleigh M v := by
  simp only [rayleigh, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    mul_div_mul_left _ _ hc]

lemma bddBelow_rayleigh {M : Mat n} (hM : ∀ v : Vec n, v ≠ 0 → 0 < v ⬝ᵥ (M *ᵥ v)) :
    BddBelow (Set.range fun v : {v : Vec n // v ≠ 0} => rayleigh M v) :=
  ⟨0, by rintro _ ⟨v, rfl⟩; exact (div_pos (hM v.1 v.2) (dot_self_pos v.2)).le⟩

/-- Rayleigh bound for a positive definite `M`: `λ_min(M) vᵀv ≤ vᵀ M v`. -/
lemma lambdaMin_mul_le {M : Mat n} (hM : ∀ v : Vec n, v ≠ 0 → 0 < v ⬝ᵥ (M *ᵥ v)) (v : Vec n) :
    lambdaMin M * (v ⬝ᵥ v) ≤ v ⬝ᵥ (M *ᵥ v) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvv := dot_self_pos hv
  calc lambdaMin M * (v ⬝ᵥ v) ≤ rayleigh M v * (v ⬝ᵥ v) :=
        mul_le_mul_of_nonneg_right (ciInf_le (bddBelow_rayleigh hM) ⟨v, hv⟩) hvv.le
    _ = v ⬝ᵥ (M *ᵥ v) := div_mul_cancel₀ _ hvv.ne'

/-- `λ_min(M) > 0` for a positive definite `M` (and `n ≥ 1`): the Rayleigh quotient attains a
positive minimum on the compact unit sphere, and it is invariant under scaling. -/
lemma lambdaMin_pos {M : Mat n} (hn : 0 < n) (hM : ∀ v : Vec n, v ≠ 0 → 0 < v ⬝ᵥ (M *ᵥ v)) :
    0 < lambdaMin M := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hne : (Metric.sphere (0 : Vec n) 1).Nonempty := NormedSpace.sphere_nonempty.2 zero_le_one
  have hcont : ContinuousOn (rayleigh M) (Metric.sphere (0 : Vec n) 1) := by
    have h1 : Continuous fun v : Vec n => v ⬝ᵥ (M *ᵥ v) :=
      continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
    have h2 : Continuous fun v : Vec n => v ⬝ᵥ v := continuous_id.dotProduct continuous_id
    exact h1.continuousOn.div h2.continuousOn fun v hv =>
      (dot_self_pos (ne_zero_of_mem_sphere one_ne_zero ⟨v, hv⟩)).ne'
  obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_sphere (0 : Vec n) 1).exists_isMinOn hne hcont
  have hv₀ne : v₀ ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨v₀, hv₀⟩
  have hpos : 0 < rayleigh M v₀ := div_pos (hM v₀ hv₀ne) (dot_self_pos hv₀ne)
  have : Nonempty {v : Vec n // v ≠ 0} := ⟨⟨v₀, hv₀ne⟩⟩
  refine hpos.trans_le (le_ciInf fun u => ?_)
  -- rescale `u` to the unit sphere
  have hu : ‖u.1‖ ≠ 0 := norm_ne_zero_iff.2 u.2
  have hmem : ‖u.1‖⁻¹ • u.1 ∈ Metric.sphere (0 : Vec n) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu]
  calc rayleigh M v₀ ≤ rayleigh M (‖u.1‖⁻¹ • u.1) := isMinOn_iff.1 hmin _ hmem
    _ = rayleigh M u.1 := rayleigh_smul M u.1 (inv_ne_zero hu)

/-- Every eigenvalue of a positive definite `M` is `≥ λ_min(M)`. -/
lemma lambdaMin_le_of_eigen {M : Mat n} (hM : ∀ v : Vec n, v ≠ 0 → 0 < v ⬝ᵥ (M *ᵥ v))
    {μ : ℝ} {v : Vec n} (hv : v ≠ 0) (hMv : M *ᵥ v = μ • v) : lambdaMin M ≤ μ := by
  have h : rayleigh M v = μ := by
    rw [rayleigh, hMv, dotProduct_smul, smul_eq_mul, mul_div_assoc,
      div_self (dot_self_pos hv).ne', mul_one]
  calc lambdaMin M ≤ rayleigh M v := ciInf_le (bddBelow_rayleigh hM) ⟨v, hv⟩
    _ = μ := h

open scoped RealInnerProductSpace in
/-- For a symmetric `M` (and `n ≥ 1`), `λ_min(M)` is an eigenvalue of `M`. Together with
`lambdaMin_le_of_eigen`, `λ_min(M)` is the smallest eigenvalue of `M`. -/
theorem exists_eigen_lambdaMin {M : Mat n} (hn : 0 < n) (hMs : Mᵀ = M) :
    ∃ v : Vec n, v ≠ 0 ∧ M *ᵥ v = lambdaMin M • v := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hT : (Matrix.toEuclideanLin M).IsSymmetric := by
    rw [isSymmetric_toEuclideanLin_iff]
    show Mᴴ = M
    rwa [conjTranspose_eq_transpose_of_trivial]
  have h := hT.hasEigenvalue_iInf_of_finiteDimensional
  -- the infimum in Mathlib's statement is `lambdaMin M` (reindex by `v ↦ toLp 2 v`)
  have heq : (⨅ x : {x : EuclideanSpace ℝ (Fin n) // x ≠ 0},
      RCLike.re ⟪Matrix.toEuclideanLin M x, x⟫ / ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2) =
      lambdaMin M := by
    let e : {v : Vec n // v ≠ 0} ≃ {x : EuclideanSpace ℝ (Fin n) // x ≠ 0} :=
      Equiv.subtypeEquiv (WithLp.equiv 2 (Fin n → ℝ)).symm (fun v => by simp)
    rw [← e.surjective.iInf_comp]
    refine iInf_congr fun v => ?_
    have h1 : RCLike.re ⟪Matrix.toEuclideanLin M (WithLp.toLp 2 v.1), WithLp.toLp 2 v.1⟫ =
        v.1 ⬝ᵥ (M *ᵥ v.1) := by
      rw [RCLike.re_to_real, real_inner_comm, ← coe_toEuclideanCLM_eq_toEuclideanLin]
      simpa using inner_toEuclideanCLM M (WithLp.toLp 2 v.1) (WithLp.toLp 2 v.1)
    have h2 : ‖(WithLp.toLp 2 v.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2 = v.1 ⬝ᵥ v.1 := vnorm_sq v.1
    show RCLike.re ⟪Matrix.toEuclideanLin M (WithLp.toLp 2 v.1), WithLp.toLp 2 v.1⟫ /
        ‖(WithLp.toLp 2 v.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2 = rayleigh M v.1
    rw [h1, h2, rayleigh]
  rw [heq] at h
  obtain ⟨x, hx⟩ := h.exists_hasEigenvector
  refine ⟨WithLp.ofLp x, ?_, ?_⟩
  · simpa using hx.2
  · simpa using congrArg WithLp.ofLp hx.apply_eq_smul

/-! ## The bound `ρ_Δ(N, δ)`, eqs. (27) and (31)–(36) -/

/-- `Q̃⁻¹ = P^{-1/2} Q⁻¹ P^{-1/2}` (Proposition 2). -/
def Qtinv (Ph Q : Mat n) : Mat n := Ph⁻¹ * Q⁻¹ * Ph⁻¹

/-- `Σ̃ = P^{1/2} Σ_X P^{1/2}` (Proposition 2). -/
def SigT (Ph SigX : Mat n) : Mat n := Ph * SigX * Ph

/-- Eq. (27): `ρ_Δ(N, δ) = √(c_δ / (λ_min(Q̃⁻¹) λ_min(Σ̃)))`. -/
def rhoDelta (Ph Q SigX : Mat n) (cδ : ℝ) : ℝ :=
  √(cδ / (lambdaMin (Qtinv Ph Q) * lambdaMin (SigT Ph SigX)))

lemma rhoDelta_nonneg (Ph Q SigX : Mat n) (cδ : ℝ) : 0 ≤ rhoDelta Ph Q SigX cδ :=
  Real.sqrt_nonneg _

/-- `vᵀ (Kᵀ K) v = ‖K v‖₂² > 0` for `v ≠ 0` and invertible `K`. -/
lemma quad_transpose_mul_self_pos {K : Mat n} (hK : IsUnit K.det) {v : Vec n} (hv : v ≠ 0) :
    0 < v ⬝ᵥ ((Kᵀ * K) *ᵥ v) := by
  rw [← mulVec_mulVec, dotProduct_mulVec v Kᵀ (K *ᵥ v), vecMul_transpose]
  refine dot_self_pos fun h => hv ?_
  rw [← one_mulVec v, ← nonsing_inv_mul K hK, ← mulVec_mulVec, h, mulVec_zero]

/-- `Q̃⁻¹ = Kᵀ K` with `K = Q^{-1/2} P^{-1/2}`. -/
lemma Qtinv_eq {P Q Ph Qh : Mat n} (hP : IsSqrt Ph P) (hQ : IsSqrt Qh Q) :
    Qtinv Ph Q = (Qh⁻¹ * Ph⁻¹)ᵀ * (Qh⁻¹ * Ph⁻¹) := by
  rw [Qtinv, Matrix.transpose_mul, hP.inv_symm, hQ.inv_symm, ← hQ.mul_self, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

/-- `Q̃⁻¹` is positive definite. -/
lemma Qtinv_pos {P Q Ph Qh : Mat n} (hP : IsSqrt Ph P) (hQ : IsSqrt Qh Q) :
    ∀ v : Vec n, v ≠ 0 → 0 < v ⬝ᵥ (Qtinv Ph Q *ᵥ v) := fun v hv => by
  rw [Qtinv_eq hP hQ]
  refine quad_transpose_mul_self_pos ?_ hv
  rw [det_mul]
  exact hQ.isUnit_inv_det.mul hP.isUnit_inv_det

lemma transpose_eq_of_posDef {M : Mat n} (hM : M.PosDef) : Mᵀ = M := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact hM.isHermitian

/-- `Σ̃` is symmetric. -/
lemma SigT_symm {P Ph SigX : Mat n} (hP : IsSqrt Ph P) (hSig : SigX.PosDef) :
    (SigT Ph SigX)ᵀ = SigT Ph SigX := by
  rw [SigT, Matrix.transpose_mul, Matrix.transpose_mul, hP.symm, transpose_eq_of_posDef hSig,
    Matrix.mul_assoc]

/-- `Σ̃` is positive definite. -/
lemma SigT_pos {P Ph SigX : Mat n} (hP : IsSqrt Ph P) (hSig : SigX.PosDef) :
    ∀ v : Vec n, v ≠ 0 → 0 < v ⬝ᵥ (SigT Ph SigX *ᵥ v) := fun v hv => by
  have h := hSig.dotProduct_mulVec_pos (hP.mulVec_ne_zero hv)
  rw [star_trivial] at h
  rwa [SigT, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec v Ph, ← mulVec_transpose,
    hP.symm]

/-- (32) ⇔ (33): with `E = P^{1/2} Δ P^{-1/2}`,
`tr(Q⁻¹ Δ Σ_X Δᵀ) = tr(Q̃⁻¹ E Σ̃ Eᵀ)`. -/
theorem trace_change_of_variables {P Ph : Mat n} (hP : IsSqrt Ph P) (Q SigX Δ : Mat n) :
    (Q⁻¹ * Δ * SigX * Δᵀ).trace =
      (Qtinv Ph Q * (Ph * Δ * Ph⁻¹) * SigT Ph SigX * (Ph * Δ * Ph⁻¹)ᵀ).trace := by
  have hL : ∀ X : Mat n, Ph⁻¹ * (Ph * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hP.inv_mul, Matrix.one_mul]
  have hR : ∀ X : Mat n, Ph * (Ph⁻¹ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hP.mul_inv, Matrix.one_mul]
  simp only [Qtinv, SigT, Matrix.transpose_mul, hP.symm, hP.inv_symm, Matrix.mul_assoc, hL, hR]
  rw [Matrix.trace_mul_comm Ph⁻¹]
  simp only [Matrix.mul_assoc, hP.mul_inv, Matrix.mul_one]

/-- `tr(X M Xᵀ) = ∑ₖ xₖᵀ M xₖ`, where `xₖ` are the rows of `X`. -/
lemma trace_mul_mul_transpose (X M : Mat n) :
    (X * M * Xᵀ).trace = ∑ k, X k ⬝ᵥ (M *ᵥ X k) := by
  unfold Matrix.trace
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `‖X‖_F² = ‖vec X‖₂²`. -/
lemma frobSq_eq_vec (X : Mat n) : frobSq X = vec X ⬝ᵥ vec X := by
  simp only [frobSq, dotProduct, vec, Fintype.sum_prod_type, sq]
  exact Finset.sum_comm

lemma frobSq_eq_trace (X : Mat n) : frobSq X = (Xᵀ * X).trace := by
  rw [frobSq_eq_vec, vec_dotProduct_vec]

lemma frobSq_transpose (X : Mat n) : frobSq Xᵀ = frobSq X := by
  unfold frobSq
  rw [Finset.sum_comm]
  rfl

/-- If `a vᵀv ≤ vᵀ M v` for all `v`, then `a ‖X‖_F² ≤ tr(X M Xᵀ)`. -/
lemma le_trace_of_le_quad (X M : Mat n) {a : ℝ}
    (hM : ∀ v : Vec n, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (M *ᵥ v)) :
    a * frobSq X ≤ (X * M * Xᵀ).trace := by
  rw [trace_mul_mul_transpose, frobSq, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  simpa [dotProduct, sq] using hM (X k)

/-- If `M = Kᵀ K`, `a vᵀv ≤ vᵀ M v` and `b vᵀv ≤ vᵀ N v` for all `v` (with `b ≥ 0`), then
`a b ‖E‖_F² ≤ tr(M E N Eᵀ)`. -/
lemma mul_frobSq_le_trace {M N : Mat n} (K : Mat n) (hMK : M = Kᵀ * K) (E : Mat n) {a b : ℝ}
    (hb : 0 ≤ b) (hM : ∀ v : Vec n, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (M *ᵥ v))
    (hN : ∀ v : Vec n, b * (v ⬝ᵥ v) ≤ v ⬝ᵥ (N *ᵥ v)) :
    a * b * frobSq E ≤ (M * E * N * Eᵀ).trace := by
  subst hMK
  -- with `H = K E`: `tr(Kᵀ K E N Eᵀ) = tr(H N Hᵀ) ≥ b ‖H‖_F²` and `‖H‖_F² ≥ a ‖E‖_F²`
  have h1 : (Kᵀ * K * E * N * Eᵀ).trace = (K * E * N * (K * E)ᵀ).trace := by
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm Kᵀ]
    simp only [Matrix.mul_assoc]
  have h2 : a * frobSq E ≤ frobSq (K * E) := by
    have e : frobSq (K * E) = (Eᵀ * (Kᵀ * K) * Eᵀᵀ).trace := by
      rw [frobSq_eq_trace, Matrix.transpose_mul, Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
    rw [e, ← frobSq_transpose E]
    exact le_trace_of_le_quad Eᵀ (Kᵀ * K) hM
  have h3 : b * frobSq (K * E) ≤ (K * E * N * (K * E)ᵀ).trace := le_trace_of_le_quad _ N hN
  calc a * b * frobSq E = b * (a * frobSq E) := by ring
    _ ≤ b * frobSq (K * E) := mul_le_mul_of_nonneg_left h2 hb
    _ ≤ (K * E * N * (K * E)ᵀ).trace := h3
    _ = (Kᵀ * K * E * N * Eᵀ).trace := h1.symm

/-- The bound on the matrix of (34), `Σ̃ ⊗ Q̃⁻¹ ⪰ λ_min(Q̃⁻¹) λ_min(Σ̃) I`, in general form: if
`M = Kᵀ K`, `a vᵀv ≤ vᵀ M v`, `b vᵀv ≤ vᵀ N v` (`b ≥ 0`) and `Nᵀ = N`, then
`a b ‖e‖₂² ≤ eᵀ (N ⊗ M) e` for every `e ∈ ℝ^{n²}`. -/
lemma kron_quad_ge {M N : Mat n} (K : Mat n) (hMK : M = Kᵀ * K) (hNs : Nᵀ = N) {a b : ℝ}
    (hb : 0 ≤ b) (hM : ∀ v : Vec n, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (M *ᵥ v))
    (hN : ∀ v : Vec n, b * (v ⬝ᵥ v) ≤ v ⬝ᵥ (N *ᵥ v)) (e : Fin n × Fin n → ℝ) :
    a * b * (e ⬝ᵥ e) ≤ e ⬝ᵥ ((N ⊗ₖ M) *ᵥ e) := by
  -- every `e` is `vec E` for some matrix `E`
  obtain ⟨E, rfl⟩ : ∃ E : Mat n, vec E = e := ⟨Matrix.of fun i j => e (j, i), rfl⟩
  rw [← trace_eq_vec_kron M E N hNs, ← frobSq_eq_vec]
  exact mul_frobSq_le_trace K hMK E hb hM hN

/-- Eqs. (33)–(36): if `E` satisfies `tr(Q̃⁻¹ E Σ̃ Eᵀ) ≤ c_δ`, then
`‖E‖₂ ≤ ‖E‖_F ≤ ρ_Δ(N, δ)`. -/
theorem specNorm_le_rhoDelta_of_trace {P Q Ph Qh SigX : Mat n} (hP : IsSqrt Ph P)
    (hQ : IsSqrt Qh Q) (hSig : SigX.PosDef) {cδ : ℝ} (E : Mat n)
    (h33 : (Qtinv Ph Q * E * SigT Ph SigX * Eᵀ).trace ≤ cδ) :
    specNorm E ≤ rhoDelta Ph Q SigX cδ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Subsingleton.elim E 0, specNorm_zero]
    exact rhoDelta_nonneg _ _ _ _
  have hQpos := Qtinv_pos hP hQ
  have hSpos := SigT_pos hP hSig
  have ha : 0 < lambdaMin (Qtinv Ph Q) := lambdaMin_pos hn hQpos
  have hb : 0 < lambdaMin (SigT Ph SigX) := lambdaMin_pos hn hSpos
  -- (34): `e = vec E` satisfies `eᵀ (Σ̃ ⊗ Q̃⁻¹) e ≤ c_δ`
  rw [trace_eq_vec_kron _ _ _ (SigT_symm hP hSig)] at h33
  -- `Σ̃ ⊗ Q̃⁻¹ ⪰ λ_min(Q̃⁻¹) λ_min(Σ̃) I`, hence `λ_min(Q̃⁻¹) λ_min(Σ̃) ‖e‖₂² ≤ c_δ`
  have hlam := (kron_quad_ge _ (Qtinv_eq hP hQ) (SigT_symm hP hSig) hb.le
    (lambdaMin_mul_le hQpos) (lambdaMin_mul_le hSpos) (vec E)).trans h33
  -- `‖e‖₂ = ‖E‖_F`, and (36): `‖E‖₂ ≤ ‖E‖_F ≤ ρ_Δ(N, δ)`
  rw [← frobSq_eq_vec] at hlam
  refine (specNorm_le_frobNorm E).trans (Real.sqrt_le_sqrt ?_)
  rw [le_div_iff₀ (mul_pos ha hb), mul_comm]
  exact hlam

/-- **Eqs. (32)–(36).** Every `A ∈ Θ_δ` satisfies `‖P^{1/2} (A - Â) P^{-1/2}‖₂ ≤ ρ_Δ(N, δ)`.
Here `P^{1/2} = Ph`, `Q^{1/2} = Qh`, and `Σ_X ≻ 0` (persistent excitation). -/
theorem specNorm_le_rhoDelta {P Q Ph Qh SigX Ahat A : Mat n} (hP : IsSqrt Ph P)
    (hQ : IsSqrt Qh Q) (hSig : SigX.PosDef) {cδ : ℝ} (hA : A ∈ credibleSet Q SigX Ahat cδ) :
    specNorm (Ph * (A - Ahat) * Ph⁻¹) ≤ rhoDelta Ph Q SigX cδ := by
  -- (32) ⇒ (33): change of variables `E = P^{1/2} Δ P^{-1/2}` with `Δ = A - Â`
  have hA' : (Q⁻¹ * (A - Ahat) * SigX * (A - Ahat)ᵀ).trace ≤ cδ := hA
  rw [trace_change_of_variables hP] at hA'
  exact specNorm_le_rhoDelta_of_trace hP hQ hSig _ hA'

/-- Triangle inequality used in (31)–(32): `ρ(A) ≤ ρ(Â) + ‖P^{1/2} (A - Â) P^{-1/2}‖₂`. -/
lemma rho_le_rho_add (Ph A Ahat : Mat n) :
    rho Ph A ≤ rho Ph Ahat + specNorm (Ph * (A - Ahat) * Ph⁻¹) := by
  have h : Ph * A * Ph⁻¹ = Ph * Ahat * Ph⁻¹ + Ph * (A - Ahat) * Ph⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    abel
  unfold rho
  rw [h]
  exact specNorm_add_le _ _

/-- **Eqs. (31)–(36).** Every `A ∈ Θ_δ` satisfies `ρ(A) ≤ ρ(Â) + ρ_Δ(N, δ)`. -/
theorem rho_le_of_mem_credibleSet {P Q Ph Qh SigX Ahat A : Mat n} (hP : IsSqrt Ph P)
    (hQ : IsSqrt Qh Q) (hSig : SigX.PosDef) {cδ : ℝ} (hA : A ∈ credibleSet Q SigX Ahat cδ) :
    rho Ph A ≤ rho Ph Ahat + rhoDelta Ph Q SigX cδ := by
  have h1 := rho_le_rho_add Ph A Ahat
  have h2 := specNorm_le_rhoDelta hP hQ hSig hA
  linarith

end PIS

end

-- ════════════ PISLean/Proposition2.lean ════════════

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

end

-- ════════════ Axiom check (PISLean.lean) ════════════

#print axioms PIS.proposition1
#print axioms PIS.proposition2

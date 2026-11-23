import PISLean.Basic

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

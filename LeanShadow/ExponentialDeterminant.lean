import LeanShadow.ProjectiveJacobian
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Trace

/-! # Determinant of the actual exponential flow

The proof evaluates the Banach-algebra exponential on eigenvectors using its
convergent series. An orthonormal eigenbasis then reduces determinant and trace
to finite products and sums. No determinant-of-exponential identity is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace ShadowVerification.Projective

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem power_apply_eigenvector (H : E →L[ℝ] E) (x : E) (lam : ℝ)
    (hx : H x = lam • x) (k : ℕ) : (H ^ k) x = lam ^ k • x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hx, smul_smul]
    rw [pow_succ]

variable [CompleteSpace E]

theorem exponential_apply_eigenvector (H : E →L[ℝ] E) (x : E) (lam : ℝ)
    (hx : H x = lam • x) : (NormedSpace.exp H) x = Real.exp lam • x := by
  have h1 := (ContinuousLinearMap.apply ℝ E x).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) H)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) lam).smul_const x
  simp only [ContinuousLinearMap.apply_apply, smul_apply,
    power_apply_eigenvector H x lam hx, smul_smul] at h1
  simp only [smul_eq_mul] at h2
  simpa only [← Real.exp_eq_exp_ℝ] using h1.unique h2

theorem flow_apply_eigenvector (H : E →L[ℝ] E) (x : E) (lam t : ℝ)
    (hx : H x = lam • x) : flow H x t = Real.exp (t * lam) • x := by
  apply exponential_apply_eigenvector (t • H) x (t * lam)
  simp only [smul_apply, hx, smul_smul]

variable [FiniteDimensional ℝ E]

theorem flow_matrix_in_eigenbasis (H : E →L[ℝ] E)
    (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (t : ℝ) :
    let b := (hH.eigenvectorBasis rfl).toBasis
    LinearMap.toMatrix b b (flowEquiv H t : E →ₗ[ℝ] E) =
      Matrix.diagonal (fun i => Real.exp (t * hH.eigenvalues rfl i)) := by
  classical
  dsimp only
  ext i j
  rw [LinearMap.toMatrix_apply]
  change ((hH.eigenvectorBasis rfl).toBasis.repr (flowEquiv H t (hH.eigenvectorBasis rfl j))) i = _
  rw [flowEquiv_apply,
    flow_apply_eigenvector H _ _ t (hH.apply_eigenvectorBasis rfl j)]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

omit [CompleteSpace E] in
theorem trace_eq_sum_eigenvalues (H : E →L[ℝ] E)
    (hH : (H : E →ₗ[ℝ] E).IsSymmetric) :
    LinearMap.trace ℝ E (H : E →ₗ[ℝ] E) = ∑ i, hH.eigenvalues rfl i := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (hH.eigenvectorBasis rfl).toBasis,
    hH.toMatrix_eigenvectorBasis rfl]
  simp

/-- Determinant of the actual flow, for every symmetric generator. -/
theorem flow_determinant (H : E →L[ℝ] E)
    (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (t : ℝ) :
    LinearMap.det (flowEquiv H t : E →ₗ[ℝ] E) =
      Real.exp (t * LinearMap.trace ℝ E (H : E →ₗ[ℝ] E)) := by
  rw [← LinearMap.det_toMatrix (hH.eigenvectorBasis rfl).toBasis,
    flow_matrix_in_eigenbasis H hH t, Matrix.det_diagonal,
    ← Real.exp_sum, ← Finset.mul_sum, ← trace_eq_sum_eigenvalues H hH]

theorem flow_determinant_trace_free (H : E →L[ℝ] E)
    (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (htr : LinearMap.trace ℝ E (H : E →ₗ[ℝ] E) = 0) (t : ℝ) :
    LinearMap.det (flowEquiv H t : E →ₗ[ℝ] E) = 1 := by
  rw [flow_determinant H hH t, htr, mul_zero, Real.exp_zero]

end ShadowVerification.Projective
#print axioms ShadowVerification.Projective.power_apply_eigenvector
#print axioms ShadowVerification.Projective.exponential_apply_eigenvector
#print axioms ShadowVerification.Projective.flow_apply_eigenvector
#print axioms ShadowVerification.Projective.flow_matrix_in_eigenbasis
#print axioms ShadowVerification.Projective.trace_eq_sum_eigenvalues
#print axioms ShadowVerification.Projective.flow_determinant
#print axioms ShadowVerification.Projective.flow_determinant_trace_free

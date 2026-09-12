import LeanShadow.ShadowVerification
import Mathlib.Analysis.Matrix.PosDef

/-! # Spectral step, conditional on the geometric variational data

This module proves the existence of the negative eigendirection from symmetry,
zero trace, and nonvanishing. Nonisotropy and the geometric moment bound remain
hypotheses. This is not a proof of the shadow theorem.
-/

set_option autoImplicit false
open scoped BigOperators Matrix

namespace ShadowVerification

variable {ι n : Type*} [Fintype ι] [Fintype n]

theorem exists_unit_negative_eigenvector
    (G : Matrix n n ℝ) (hG : G.IsSymm) (htrace : G.trace = 0) (hne : G ≠ 0) :
    ∃ (d : ℝ) (z : n → ℝ), 0 < d ∧ z ⬝ᵥ z = 1 ∧ G *ᵥ z = (-d) • z := by
  classical
  have hHerm : G.IsHermitian := by simpa using hG
  have hneg : ∃ i, hHerm.eigenvalues i < 0 := by
    by_contra h
    push Not at h
    have hpsd : G.PosSemidef := hHerm.posSemidef_iff_eigenvalues_nonneg.mpr h
    exact hne (hpsd.trace_eq_zero_iff.mp htrace)
  obtain ⟨i, hi⟩ := hneg
  refine ⟨-hHerm.eigenvalues i, ⇑(hHerm.eigenvectorBasis i), neg_pos.mpr hi, ?_, ?_⟩
  · have hvnorm : ‖hHerm.eigenvectorBasis i‖ = 1 := hHerm.eigenvectorBasis.orthonormal.1 i
    have hin : inner ℝ (hHerm.eigenvectorBasis i) (hHerm.eigenvectorBasis i) = 1 := by
      simp [inner_self_eq_norm_sq_to_K, hvnorm]
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hin
  · simpa using hHerm.mulVec_eigenvectorBasis i

theorem rayleigh_bound_for_negative_eigenvalue
    (G : Matrix n n ℝ) (z : n → ℝ) (d D : ℝ)
    (hz : z ⬝ᵥ z = 1) (heigen : G *ᵥ z = (-d) • z)
    (hRayleigh : ∀ w : n → ℝ, w ⬝ᵥ w = 1 → -D ≤ w ⬝ᵥ (G *ᵥ w)) :
    d ≤ D := by
  have h := hRayleigh z hz
  rw [heigen, dotProduct_smul, hz] at h
  simpa using h

/-- All finite-dimensional steps from the displayed hypotheses to C / D ≤ ρ.
The geometric content of hvariation, hidentity, hne and hRayleigh is not
established by this module. -/
theorem algebraic_curvature_bound
    (H : ι → Matrix n n ℝ) (Q : Matrix ι ι ℝ)
    (v : ι → ℝ) (G : Matrix n n ℝ) (ρ C D : ℝ)
    (hH : ∀ i, (H i).IsSymm)
    (hG : (∑ i : ι, v i • H i) = G)
    (hvariation : (ρ • rankOne v - Q).PosSemidef)
    (hidentity : manuscriptContraction H Q = (-C) • G)
    (hsymm : G.IsSymm) (htrace : G.trace = 0) (hne : G ≠ 0)
    (hC : 0 ≤ C)
    (hRayleigh : ∀ z : n → ℝ, z ⬝ᵥ z = 1 → -D ≤ z ⬝ᵥ (G *ᵥ z)) :
    C / D ≤ ρ := by
  obtain ⟨d, z, hd, hz, heigen⟩ := exists_unit_negative_eigenvector G hsymm htrace hne
  have hdD := rayleigh_bound_for_negative_eigenvalue G z d D hz heigen hRayleigh
  exact variation_to_scalar_bound H Q v G z ρ C d D hH hG hvariation hidentity
    hC hd hdD hz heigen

end ShadowVerification

#print axioms ShadowVerification.exists_unit_negative_eigenvector
#print axioms ShadowVerification.rayleigh_bound_for_negative_eigenvalue
#print axioms ShadowVerification.algebraic_curvature_bound

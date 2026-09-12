import LeanShadow.RadialChange
import LeanShadow.ProjectiveJacobian

/-! # The area integral for an actual exponential projective deformation

This connects the sphere-image definition of area to precisely the density
whose pointwise derivatives are proved in `ProjectiveJacobian`. The determinant
factor is retained; its reduction for trace-free generators is not assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace ShadowVerification.Projective
open Spherical Radial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem exponential_area_integral (mu : Measure E) [mu.IsAddHaarMeasure]
    (H : E →L[ℝ] E) (A : Set (Sphere E)) (hA : MeasurableSet A) (t : ℝ) :
    transformedArea mu A (flowEquiv H t) =
      |LinearMap.det (flowEquiv H t : E →ₗ[ℝ] E)| *
        ∫ x in A, flowDensity (Module.finrank ℝ E : ℝ) H (x : E) t ∂probability mu := by
  rw [transformedArea_integral mu (flowEquiv H t) A hA]
  simp_rw [flowEquiv_apply, flowDensity_eq_inverse_norm_power]

end ShadowVerification.Projective
#print axioms ShadowVerification.Projective.exponential_area_integral

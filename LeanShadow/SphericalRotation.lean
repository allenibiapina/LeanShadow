import LeanShadow.OrthogonalHaar
import Mathlib.MeasureTheory.Measure.Prod

/-! # Rotational invariance and Haar orbit measure on the sphere

The spherical probability here is the previously defined normalization of
`Measure.toSphere`; we identify it with the Haar orbit law rather than
introducing a different meaning of spherical area.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.SphericalRotation
open Spherical OrthogonalHaar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem rotate_eq_action (R : OrthogonalHaar.Group E) :
    rotate R = action (Unitary.linearIsometryEquiv R).toContinuousLinearEquiv := by
  funext x
  apply Subtype.ext
  rw [action_coe]
  change (R : E →L[ℝ] E) x = ‖(R : E →L[ℝ] E) x‖⁻¹ • (R : E →L[ℝ] E) x
  rw [Unitary.norm_map, mem_sphere_zero_iff_norm.mp x.property]
  simp

/-- Orthogonal transformations preserve the existing normalized spherical measure. -/
theorem measurePreserving_rotate (R : OrthogonalHaar.Group E) :
    MeasurePreserving (rotate R) (probability mu) (probability mu) := by
  rw [rotate_eq_action]
  let T := (Unitary.linearIsometryEquiv R).toContinuousLinearEquiv
  have hm := (action_continuous T).measurable
  refine ⟨hm, ?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hm hA]
  have hv := Invariance.area_of_constant_unit_norm mu (action T ⁻¹' A)
    (hA.preimage hm) T 1 (by norm_num) (fun x => by
      change ‖(R : E →L[ℝ] E) x‖ = 1
      rw [Unitary.norm_map]
      exact mem_sphere_zero_iff_norm.mp x.property)
  unfold transformedArea at hv
  have hs : Function.Surjective (action T) := (actionHomeomorph T).surjective
  rw [hs.image_preimage] at hv
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hv.symm

/-- The distribution of a Haar-rotated point does not depend on the initial point. -/
theorem orbit_map_eq (x y : Sphere E) :
    (haar E).map (fun R => rotate R x) = (haar E).map (fun R => rotate R y) := by
  obtain ⟨S, hS, _⟩ := exists_exchange x y
  have hm : Measurable (fun R : OrthogonalHaar.Group E => rotate R x) :=
    (rotate_continuous.comp (continuous_id.prodMk continuous_const)).measurable
  have hmul : Measurable (fun R : OrthogonalHaar.Group E => R * S) :=
    (continuous_mul_const S).measurable
  calc
    (haar E).map (fun R => rotate R x) =
        ((haar E).map (· * S)).map (fun R => rotate R x) := by rw [haar_map_right]
    _ = (haar E).map (fun R => rotate R y) := by
      rw [Measure.map_map hm hmul]
      congr 1
      funext R
      exact (rotate_mul R S x).trans (congrArg (rotate R) hS)

/-- Averaging first over the group and then over the sphere identifies the orbit law. -/
theorem orbit_map_probability (x : Sphere E) :
    (haar E).map (fun R => rotate R x) = probability mu := by
  apply Measure.ext
  intro A hA
  let F : Sphere E → ℝ≥0∞ := A.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hA
  have hm (y : Sphere E) : Measurable (fun R : OrthogonalHaar.Group E => rotate R y) :=
    (rotate_continuous.comp (continuous_id.prodMk continuous_const)).measurable
  have hc (y : Sphere E) :
      (∫⁻ R, F (rotate R x) ∂haar E) = ∫⁻ R, F (rotate R y) ∂haar E := by
    rw [← lintegral_map hF (hm x), ← lintegral_map hF (hm y), orbit_map_eq x y]
  calc
    ((haar E).map (fun R => rotate R x)) A = ∫⁻ R, F (rotate R x) ∂haar E := by
      rw [← lintegral_map hF (hm x)]
      simp [F, lintegral_indicator hA]
    _ = ∫⁻ y, ∫⁻ R, F (rotate R y) ∂haar E ∂probability mu := by
      simp_rw [← hc]
      simp
    _ = ∫⁻ R, ∫⁻ y, F (rotate R y) ∂probability mu ∂haar E := by
      apply lintegral_lintegral_swap
      exact (hF.comp (rotate_continuous.comp continuous_swap).measurable).aemeasurable
    _ = probability mu A := by
      simp_rw [(measurePreserving_rotate mu _).lintegral_comp hF]
      simp [F, lintegral_indicator hA]

end ShadowVerification.SphericalRotation
#print axioms ShadowVerification.SphericalRotation.rotate_eq_action
#print axioms ShadowVerification.SphericalRotation.measurePreserving_rotate
#print axioms ShadowVerification.SphericalRotation.orbit_map_eq
#print axioms ShadowVerification.SphericalRotation.orbit_map_probability

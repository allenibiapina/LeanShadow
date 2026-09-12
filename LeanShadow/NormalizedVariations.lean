import LeanShadow.AreaVariations
import LeanShadow.ExponentialDeterminant

/-! # Exact normalization and trace-free area variations

The whole-sphere density integral is computed from the proved determinant
formula. This evaluates both whole-sphere correction terms and completes the
passage from pointwise density derivatives to the manuscript's exact area
derivatives for an arbitrary Borel spherical set.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace ShadowVerification.Projective
open Spherical

theorem exp_mul_hasDeriv (c t : ℝ) :
    HasDerivAt (fun s => Real.exp (s * c)) (c * Real.exp (t * c)) t := by
  convert ((hasDerivAt_id t).mul_const c).exp using 1 <;> simp [mul_comm]

theorem exp_mul_second_deriv_zero (c : ℝ) :
    deriv (deriv (fun t => Real.exp (t * c))) 0 = c ^ 2 := by
  have heq : deriv (fun t => Real.exp (t * c)) = fun t => c * Real.exp (t * c) :=
    funext (fun t => (exp_mul_hasDeriv c t).deriv)
  rw [heq]
  have h := (exp_mul_hasDeriv c 0).const_mul c
  rw [h.deriv]
  simp [pow_two]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- Exact normalization for the density of the actual exponential flow. -/
theorem whole_densityIntegral (mu : Measure E) [mu.IsAddHaarMeasure]
    (H : E →L[ℝ] E) (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (t : ℝ) :
    densityIntegral (probability mu) univ (Module.finrank ℝ E : ℝ) H t =
      Real.exp (t * (-LinearMap.trace ℝ E (H : E →ₗ[ℝ] E))) := by
  have h := exponential_area_integral mu H univ MeasurableSet.univ t
  rw [transformedArea_univ, flow_determinant H hH t,
    abs_of_pos (Real.exp_pos _)] at h
  change 1 = Real.exp (t * LinearMap.trace ℝ E (H : E →ₗ[ℝ] E)) *
    densityIntegral (probability mu) univ (Module.finrank ℝ E : ℝ) H t at h
  have hi : densityIntegral (probability mu) univ (Module.finrank ℝ E : ℝ) H t =
      1 / Real.exp (t * LinearMap.trace ℝ E (H : E →ₗ[ℝ] E)) := by
    apply (eq_div_iff (Real.exp_ne_zero _)).mpr
    simpa only [mul_comm] using h.symm
  rw [hi, one_div, ← Real.exp_neg]
  congr 1
  ring

theorem whole_densityIntegral_trace_free (mu : Measure E) [mu.IsAddHaarMeasure]
    (H : E →L[ℝ] E) (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (htr : LinearMap.trace ℝ E (H : E →ₗ[ℝ] E) = 0) (t : ℝ) :
    densityIntegral (probability mu) univ (Module.finrank ℝ E : ℝ) H t = 1 := by
  rw [whole_densityIntegral mu H hH t, htr, neg_zero, mul_zero, Real.exp_zero]

/-- The first whole-sphere correction term is minus the operator trace. -/
theorem firstMomentVariation_univ (mu : Measure E) [mu.IsAddHaarMeasure]
    (H : E →L[ℝ] E) (hH : (H : E →ₗ[ℝ] E).IsSymmetric) :
    firstMomentVariation (probability mu) univ (Module.finrank ℝ E : ℝ) H =
      -LinearMap.trace ℝ E (H : E →ₗ[ℝ] E) := by
  have heq : densityIntegral (probability mu) univ (Module.finrank ℝ E : ℝ) H =
      fun t => Real.exp (t * (-LinearMap.trace ℝ E (H : E →ₗ[ℝ] E))) :=
    funext (whole_densityIntegral mu H hH)
  have h := densityIntegral_hasDeriv_zero (probability mu) univ (Module.finrank ℝ E : ℝ) H
  rw [heq] at h
  have h' := exp_mul_hasDeriv (-LinearMap.trace ℝ E (H : E →ₗ[ℝ] E)) 0
  simpa only [zero_mul, Real.exp_zero, mul_one, firstMomentVariation] using h.unique h'

/-- The second whole-sphere correction term is the square of the trace. -/
theorem secondMomentVariation_univ (mu : Measure E) [mu.IsAddHaarMeasure]
    (H : E →L[ℝ] E) (hH : (H : E →ₗ[ℝ] E).IsSymmetric) :
    secondMomentVariation (probability mu) univ (Module.finrank ℝ E : ℝ) H =
      (LinearMap.trace ℝ E (H : E →ₗ[ℝ] E)) ^ 2 := by
  have heq : densityIntegral (probability mu) univ (Module.finrank ℝ E : ℝ) H =
      fun t => Real.exp (t * (-LinearMap.trace ℝ E (H : E →ₗ[ℝ] E))) :=
    funext (whole_densityIntegral mu H hH)
  have h := densityIntegral_second_deriv_zero (probability mu) univ
    (Module.finrank ℝ E : ℝ) H hH
  rw [heq, exp_mul_second_deriv_zero, neg_sq] at h
  exact h.symm

/-- The determinant-one image-area identity, with the determinant condition
proved from symmetry and vanishing trace rather than assumed separately. -/
theorem exponential_area_integral_trace_free (mu : Measure E) [mu.IsAddHaarMeasure]
    (H : E →L[ℝ] E) (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (htr : LinearMap.trace ℝ E (H : E →ₗ[ℝ] E) = 0)
    (A : Set (Sphere E)) (hA : MeasurableSet A) (t : ℝ) :
    transformedArea mu A (flowEquiv H t) =
      densityIntegral (probability mu) A (Module.finrank ℝ E : ℝ) H t := by
  rw [exponential_area_ratio mu H A hA t, whole_densityIntegral_trace_free mu H hH htr t,
    div_one]

/-- Exact first variation for every Borel set and symmetric trace-free generator. -/
theorem area_hasDeriv_trace_free (mu : Measure E) [mu.IsAddHaarMeasure]
    (H : E →L[ℝ] E) (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (htr : LinearMap.trace ℝ E (H : E →ₗ[ℝ] E) = 0)
    (A : Set (Sphere E)) (hA : MeasurableSet A) :
    HasDerivAt (fun t => transformedArea mu A (flowEquiv H t))
      (∫ x in A, -(Module.finrank ℝ E : ℝ) * inner ℝ (x : E) (H x) ∂probability mu) 0 := by
  simp_rw [exponential_area_integral_trace_free mu H hH htr A hA]
  exact densityIntegral_hasDeriv_zero (probability mu) A (Module.finrank ℝ E : ℝ) H

/-- Exact second variation of actual image area. No boundary regularity of
the Borel set is required. All normalization terms have been discharged. -/
theorem area_second_deriv_trace_free (mu : Measure E) [mu.IsAddHaarMeasure]
    (H : E →L[ℝ] E) (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (htr : LinearMap.trace ℝ E (H : E →ₗ[ℝ] E) = 0)
    (A : Set (Sphere E)) (hA : MeasurableSet A) :
    deriv (deriv (fun t => transformedArea mu A (flowEquiv H t))) 0 =
      ∫ x in A, (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) + 2) *
        (inner ℝ (x : E) (H x)) ^ 2 -
        2 * (Module.finrank ℝ E : ℝ) * inner ℝ (x : E) (H (H x)) ∂probability mu := by
  simp_rw [exponential_area_integral_trace_free mu H hH htr A hA]
  exact densityIntegral_second_deriv_zero (probability mu) A (Module.finrank ℝ E : ℝ) H hH

end ShadowVerification.Projective
#print axioms ShadowVerification.Projective.exp_mul_hasDeriv
#print axioms ShadowVerification.Projective.exp_mul_second_deriv_zero
#print axioms ShadowVerification.Projective.whole_densityIntegral
#print axioms ShadowVerification.Projective.whole_densityIntegral_trace_free
#print axioms ShadowVerification.Projective.firstMomentVariation_univ
#print axioms ShadowVerification.Projective.secondMomentVariation_univ
#print axioms ShadowVerification.Projective.exponential_area_integral_trace_free
#print axioms ShadowVerification.Projective.area_hasDeriv_trace_free
#print axioms ShadowVerification.Projective.area_second_deriv_trace_free

import LeanShadow.DualFlow

/-! # Vanishing area variations in skew and scalar directions

Area invariance is derived for actual Borel-set images. It is not an
assumption about an abstract scalar function. The statements hold along the
entire flow and through every invertible base transformation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace ShadowVerification.Invariance
open Spherical Projective Regularity DualFlow
open _root_.ShadowVerification.Dual _root_.ShadowVerification.Composition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Scalar generators act by a positive scalar along their entire flow. -/
theorem scalar_flow_apply (s t : ℝ) (x : E) :
    flowEquiv (s • (1 : E →L[ℝ] E)) t x = Real.exp (t * s) • x := by
  rw [flowEquiv_apply]
  apply flow_apply_eigenvector
  simp

variable [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

/-- A constant norm factor on unit vectors cancels exactly in the area ratio. -/
theorem area_of_constant_unit_norm (A : Set (Sphere E)) (hA : MeasurableSet A)
    (T : E ≃L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x : Sphere E, ‖T x‖ = c) : transformedArea mu A T = area mu A := by
  rw [transformedArea_eq_extension mu A hA]
  have hI (D : Set (Sphere E)) :
      operatorDensityIntegral ((probability mu).restrict D) (Module.finrank ℝ E)
        (T : E →L[ℝ] E) = (probability mu).real D * c⁻¹ ^ Module.finrank ℝ E := by
    unfold operatorDensityIntegral operatorDensity
    simp_rw [ContinuousLinearEquiv.coe_coe, hT]
    simp [measureReal_def]
  unfold areaExtension
  rw [hI A]
  have hwhole : operatorDensityIntegral (probability mu) (Module.finrank ℝ E)
      (T : E →L[ℝ] E) = c⁻¹ ^ Module.finrank ℝ E := by
    simpa using hI univ
  rw [hwhole, mul_div_cancel_right₀ _ (pow_ne_zero _ (inv_ne_zero hc.ne'))]
  rfl

/-- Every skew-adjoint flow preserves spherical area. -/
theorem skew_area (A : Set (Sphere E)) (hA : MeasurableSet A)
    (H : E →L[ℝ] E) (hH : star H = -H) (t : ℝ) :
    transformedArea mu A (flowEquiv H t) = area mu A := by
  apply area_of_constant_unit_norm mu A hA _ 1 (by norm_num)
  intro x
  rw [skew_flow_norm H hH]
  exact mem_sphere_zero_iff_norm.mp x.property

/-- Every scalar flow preserves spherical area. -/
theorem scalar_area (A : Set (Sphere E)) (hA : MeasurableSet A) (s t : ℝ) :
    transformedArea mu A (flowEquiv (s • (1 : E →L[ℝ] E)) t) = area mu A := by
  apply area_of_constant_unit_norm mu A hA _ (Real.exp (t * s)) (Real.exp_pos _)
  intro x
  rw [scalar_flow_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    mem_sphere_zero_iff_norm.mp x.property, mul_one]

/-- The primal invariant-direction identity is valid at every base. -/
theorem skew_area_at_transformation (A : Set (Sphere E)) (hA : MeasurableSet A)
    (T : E ≃L[ℝ] E) (H : E →L[ℝ] E) (hH : star H = -H) (t : ℝ) :
    transformedArea mu A (T.trans (flowEquiv H t)) = transformedArea mu A T := by
  rw [transformedArea_trans, skew_area mu _ (measurable_action_image T A hA) H hH]
  rfl

theorem scalar_area_at_transformation (A : Set (Sphere E)) (hA : MeasurableSet A)
    (T : E ≃L[ℝ] E) (s t : ℝ) :
    transformedArea mu A (T.trans (flowEquiv (s • (1 : E →L[ℝ] E)) t)) =
      transformedArea mu A T := by
  rw [transformedArea_trans, scalar_area mu _ (measurable_action_image T A hA)]
  rfl

/-- Both sides of the actual avoiding pair are constant in skew directions. -/
theorem dual_skew_area_at_transformation (B : Set (Sphere E)) (hB : MeasurableSet B)
    (T : E ≃L[ℝ] E) (H : E →L[ℝ] E) (hH : star H = -H) (t : ℝ) :
    transformedArea mu B (dualEquiv (T.trans (flowEquiv H t))) =
      transformedArea mu B (dualEquiv T) := by
  rw [dual_trans_flow, hH, neg_neg]
  exact skew_area_at_transformation mu B hB (dualEquiv T) H hH t

theorem dual_scalar_area_at_transformation (B : Set (Sphere E)) (hB : MeasurableSet B)
    (T : E ≃L[ℝ] E) (s t : ℝ) :
    transformedArea mu B (dualEquiv (T.trans (flowEquiv (s • (1 : E →L[ℝ] E)) t))) =
      transformedArea mu B (dualEquiv T) := by
  rw [dual_trans_flow, star_smul, star_trivial, star_one, ← neg_smul]
  exact scalar_area_at_transformation mu B hB (dualEquiv T) (-s) t

end ShadowVerification.Invariance
#print axioms ShadowVerification.Invariance.scalar_flow_apply
#print axioms ShadowVerification.Invariance.area_of_constant_unit_norm
#print axioms ShadowVerification.Invariance.skew_area
#print axioms ShadowVerification.Invariance.scalar_area
#print axioms ShadowVerification.Invariance.skew_area_at_transformation
#print axioms ShadowVerification.Invariance.scalar_area_at_transformation
#print axioms ShadowVerification.Invariance.dual_skew_area_at_transformation
#print axioms ShadowVerification.Invariance.dual_scalar_area_at_transformation

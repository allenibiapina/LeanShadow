import LeanShadow.IntegratedDensity

/-! # Actual first and second variations of measurable image area

Normalization by the whole-sphere density integral cancels the determinant.
This allows a direct proof for every self-adjoint generator, without first
proving the separate determinant-of-exponential identity. The correction
terms are explicitly the whole-sphere moments; they have not been assumed
to vanish for trace-free generators. Their evaluation, and the resulting
exact trace-free formulas, are proved subsequently in `NormalizedVariations`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace ShadowVerification.Projective
open Spherical

theorem quotient_second_deriv_at_unit (f df g dg : ℝ → ℝ) (eF eG : ℝ)
    (hf : ∀ t, HasDerivAt f (df t) t) (hg : ∀ t, HasDerivAt g (dg t) t)
    (hdf : HasDerivAt df eF 0) (hdg : HasDerivAt dg eG 0)
    (hg0 : g 0 = 1) (hgne : ∀ t, g t ≠ 0) :
    deriv (deriv (fun t => f t / g t)) 0 =
      eF - 2 * df 0 * dg 0 + 2 * f 0 * (dg 0) ^ 2 - f 0 * eG := by
  have heq : deriv (fun t => f t / g t) =
      fun t => (df t * g t - f t * dg t) / (g t) ^ 2 :=
    funext (fun t => ((hf t).div (hg t) (hgne t)).deriv)
  rw [heq]
  have h := ((hdf.mul (hg 0)).sub ((hf 0).mul hdg)).div
    ((hg 0).pow 2) (pow_ne_zero 2 (hgne 0))
  change deriv ((df * g - f * dg) / g ^ 2) 0 = _
  rw [h.deriv]
  simp only [Pi.pow_apply, Pi.sub_apply, Pi.mul_apply, hg0, one_pow, mul_one, div_one, Nat.cast_ofNat]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem transformedArea_univ (mu : Measure E) [mu.IsAddHaarMeasure] (T : E ≃L[ℝ] E) :
    transformedArea mu univ T = 1 := by
  have heq : action T '' univ = univ :=
    Set.image_univ_of_surjective (actionHomeomorph T).surjective
  simp [transformedArea, heq, area]

omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
theorem densityIntegral_zero (mu : Measure (Sphere E)) [IsFiniteMeasure mu]
    (A : Set (Sphere E)) (N : ℝ) (H : E →L[ℝ] E) :
    densityIntegral mu A N H 0 = mu.real A := by
  unfold densityIntegral
  have hx (x : Sphere E) : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  simp_rw [flowDensity_zero N H _ (hx _)]
  simp

theorem whole_densityIntegral_ne_zero (mu : Measure E) [mu.IsAddHaarMeasure]
    (H : E →L[ℝ] E) (t : ℝ) :
    densityIntegral (probability mu) univ (Module.finrank ℝ E : ℝ) H t ≠ 0 := by
  have h := exponential_area_integral mu H univ MeasurableSet.univ t
  rw [transformedArea_univ] at h
  intro hz
  change (∫ x in univ, flowDensity (Module.finrank ℝ E : ℝ) H (x : E) t ∂probability mu) = 0 at hz
  rw [hz, mul_zero] at h
  exact one_ne_zero h

/-- Image area is exactly a ratio of density integrals. The denominator is
never zero, as proved from the whole-sphere change-of-measure formula. -/
theorem exponential_area_ratio (mu : Measure E) [mu.IsAddHaarMeasure]
    (H : E →L[ℝ] E) (A : Set (Sphere E)) (hA : MeasurableSet A) (t : ℝ) :
    transformedArea mu A (flowEquiv H t) =
      densityIntegral (probability mu) A (Module.finrank ℝ E : ℝ) H t /
        densityIntegral (probability mu) univ (Module.finrank ℝ E : ℝ) H t := by
  have h := exponential_area_integral mu H univ MeasurableSet.univ t
  rw [transformedArea_univ] at h
  rw [exponential_area_integral mu H A hA t]
  apply (eq_div_iff (whole_densityIntegral_ne_zero mu H t)).mpr
  unfold densityIntegral
  rw [mul_right_comm, ← h, one_mul]

noncomputable def firstMomentVariation (mu : Measure (Sphere E))
    (A : Set (Sphere E)) (N : ℝ) (H : E →L[ℝ] E) : ℝ :=
  ∫ x in A, -N * inner ℝ (x : E) (H x) ∂mu

noncomputable def secondMomentVariation (mu : Measure (Sphere E))
    (A : Set (Sphere E)) (N : ℝ) (H : E →L[ℝ] E) : ℝ :=
  ∫ x in A, N * (N + 2) * (inner ℝ (x : E) (H x)) ^ 2 -
    2 * N * inner ℝ (x : E) (H (H x)) ∂mu

/-- The first variation of the actual spherical image of any Borel set. -/
theorem exponential_area_hasDeriv_zero (mu : Measure E) [mu.IsAddHaarMeasure]
    (H : E →L[ℝ] E) (A : Set (Sphere E)) (hA : MeasurableSet A) :
    HasDerivAt (fun t => transformedArea mu A (flowEquiv H t))
      (firstMomentVariation (probability mu) A (Module.finrank ℝ E : ℝ) H -
        area mu A * firstMomentVariation (probability mu) univ (Module.finrank ℝ E : ℝ) H) 0 := by
  have h := (densityIntegral_hasDeriv_zero (probability mu) A (Module.finrank ℝ E : ℝ) H).div
    (densityIntegral_hasDeriv_zero (probability mu) univ (Module.finrank ℝ E : ℝ) H)
    (whole_densityIntegral_ne_zero mu H 0)
  have h1 : (probability mu).real univ = 1 := by simp
  simp only [densityIntegral_zero, h1, mul_one, one_pow, div_one] at h
  simpa only [exponential_area_ratio mu H A hA, firstMomentVariation, area] using! h

/-- The second variation of actual image area, including all normalization
terms. The set is merely Borel; no boundary regularity is imposed. -/
theorem exponential_area_second_deriv_zero (mu : Measure E) [mu.IsAddHaarMeasure]
    (H : E →L[ℝ] E) (A : Set (Sphere E)) (hA : MeasurableSet A)
    (hH : ∀ u v : E, inner ℝ (H u) v = inner ℝ u (H v)) :
    deriv (deriv (fun t => transformedArea mu A (flowEquiv H t))) 0 =
      secondMomentVariation (probability mu) A (Module.finrank ℝ E : ℝ) H -
      2 * firstMomentVariation (probability mu) A (Module.finrank ℝ E : ℝ) H *
        firstMomentVariation (probability mu) univ (Module.finrank ℝ E : ℝ) H +
      2 * area mu A * (firstMomentVariation (probability mu) univ (Module.finrank ℝ E : ℝ) H) ^ 2 -
      area mu A * secondMomentVariation (probability mu) univ (Module.finrank ℝ E : ℝ) H := by
  simp_rw [exponential_area_ratio mu H A hA]
  have h := quotient_second_deriv_at_unit
    (densityIntegral (probability mu) A (Module.finrank ℝ E : ℝ) H)
    (fun t => ∫ x in A, densityD (Module.finrank ℝ E : ℝ) H (x : E) t ∂probability mu)
    (densityIntegral (probability mu) univ (Module.finrank ℝ E : ℝ) H)
    (fun t => ∫ x in univ, densityD (Module.finrank ℝ E : ℝ) H (x : E) t ∂probability mu)
    _ _
    (densityIntegral_hasDeriv (probability mu) A (Module.finrank ℝ E : ℝ) H)
    (densityIntegral_hasDeriv (probability mu) univ (Module.finrank ℝ E : ℝ) H)
    (densityIntegralD_hasDeriv (probability mu) A (Module.finrank ℝ E : ℝ) H 0)
    (densityIntegralD_hasDeriv (probability mu) univ (Module.finrank ℝ E : ℝ) H 0)
    (by simp [densityIntegral_zero]) (whole_densityIntegral_ne_zero mu H)
  simpa only [densityD_zero, densityDD_zero _ H _ hH, densityIntegral_zero,
    firstMomentVariation, secondMomentVariation, area] using h

end ShadowVerification.Projective
#print axioms ShadowVerification.Projective.quotient_second_deriv_at_unit
#print axioms ShadowVerification.Projective.transformedArea_univ
#print axioms ShadowVerification.Projective.densityIntegral_zero
#print axioms ShadowVerification.Projective.whole_densityIntegral_ne_zero
#print axioms ShadowVerification.Projective.exponential_area_ratio
#print axioms ShadowVerification.Projective.exponential_area_hasDeriv_zero
#print axioms ShadowVerification.Projective.exponential_area_second_deriv_zero

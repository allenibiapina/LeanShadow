import LeanShadow.OrthogonalIncidence

/-! # The concrete spherical incidence operator

All incidence data in this file are the Haar construction, not hypotheses.
Only compactness and the density-point recovery property remain inputs in
the final attainment corollaries.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.SphericalIncidenceOperator
open Spherical Profile OrthogonalIncidence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure] (hd : 1 < Module.finrank ℝ E)

def operator : Lp ℝ 2 (probability mu) →L[ℝ] Lp ℝ 2 (probability mu) :=
  Attainment.operator mu (realization mu hd)

theorem pairing (u v : Lp ℝ 2 (probability mu)) :
    inner ℝ u (operator mu hd v) =
      ∫ z, u z.1 * v z.2 ∂(realization mu hd).measure :=
  Attainment.pairing mu _ u v

/-- The pairing is an explicit Haar average of rotated orthogonal vectors. -/
theorem pairing_haar (u v : Lp ℝ 2 (probability mu)) :
    inner ℝ u (operator mu hd v) = ∫ R,
      u (OrthogonalHaar.rotate R (firstPoint hd)) *
      v (OrthogonalHaar.rotate R (secondPoint hd)) ∂OrthogonalHaar.haar E := by
  rw [pairing]
  exact integral_map_of_stronglyMeasurable (frame_continuous _ _).measurable
    (((Lp.stronglyMeasurable u).comp_measurable measurable_fst).mul
      ((Lp.stronglyMeasurable v).comp_measurable measurable_snd))

theorem norm_apply_le (u : Lp ℝ 2 (probability mu)) :
    ‖operator mu hd u‖ ≤ ‖u‖ :=
  CouplingOperator.norm_apply_le _ _ (realization mu hd).firstMarginal
    (realization mu hd).secondMarginal u

theorem symmetric : (operator mu hd).toLinearMap.IsSymmetric :=
  CouplingOperator.symmetric _ _ (realization mu hd).firstMarginal
    (realization mu hd).secondMarginal (realization_swap mu hd)

/-- Positivity follows from the positive incidence integral, using every indicator as a test. -/
theorem nonneg_ae (v : Lp ℝ 2 (probability mu))
    (hv : ∀ᵐ x ∂probability mu, 0 ≤ v x) :
    ∀ᵐ x ∂probability mu, 0 ≤ operator mu hd v x := by
  apply ae_nonneg_of_forall_setIntegral_nonneg (WeakIndicators.integrable _ _)
  intro A hA _
  rw [WeakIndicators.integral_eq_inner _ _ A hA, real_inner_comm, pairing]
  apply integral_nonneg_of_ae
  apply IncidenceRounding.product_nonneg _ _ (realization mu hd).firstMarginal
    (realization mu hd).secondMarginal _ v _ hv
  filter_upwards [WeakIndicators.indicator_ae (probability mu) A hA] with x hx
  rw [hx]
  exact indicator_nonneg (fun _ _ => zero_le_one) x

/-- Averaging over orthogonal directions preserves the spherical integral. -/
theorem integral_operator (v : Lp ℝ 2 (probability mu)) :
    (∫ x, operator mu hd v x ∂probability mu) = ∫ x, v x ∂probability mu := by
  have hi := WeakIndicators.integral_eq_inner (probability mu) (operator mu hd v)
    univ MeasurableSet.univ
  rw [setIntegral_univ, real_inner_comm, pairing] at hi
  rw [hi]
  calc
    (∫ z, WeakIndicators.indicator (probability mu) univ MeasurableSet.univ z.1 * v z.2
        ∂(realization mu hd).measure) = ∫ z, v z.2 ∂(realization mu hd).measure := by
      apply integral_congr_ae
      filter_upwards [(realization mu hd).firstMarginal.quasiMeasurePreserving.ae
        (WeakIndicators.indicator_ae (probability mu) univ MeasurableSet.univ)] with z hz
      simp [hz]
    _ = ∫ x, v x ∂probability mu := by
      have h := integral_map_of_stronglyMeasurable
        (μ := (realization mu hd).measure) measurable_snd (Lp.stronglyMeasurable v)
      rw [(realization mu hd).secondMarginal.map_eq] at h
      exact h.symm

/-- The constant one function is fixed by the concrete operator. -/
theorem operator_one :
    operator mu hd (WeakIndicators.indicator (probability mu) univ MeasurableSet.univ) =
      WeakIndicators.indicator (probability mu) univ MeasurableSet.univ := by
  apply ext_inner_right ℝ
  intro v
  have hi (w : Lp ℝ 2 (probability mu)) :
      inner ℝ (WeakIndicators.indicator (probability mu) univ MeasurableSet.univ) w =
        ∫ x, w x ∂probability mu := by
    rw [real_inner_comm]
    simpa only [setIntegral_univ] using
      (WeakIndicators.integral_eq_inner (probability mu) w univ MeasurableSet.univ).symm
  change inner ℝ ((operator mu hd).toLinearMap _) v = _
  rw [symmetric mu hd, hi, hi]
  exact integral_operator mu hd v

theorem indicator_pairing (A B : Set (Sphere E)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    inner ℝ (WeakIndicators.indicator (probability mu) A hA)
      (operator mu hd (WeakIndicators.indicator (probability mu) B hB)) =
      (realization mu hd).measure.real (A ×ˢ B) := by
  rw [pairing]
  exact IncidenceRounding.indicator_product_integral _ _ (realization mu hd).firstMarginal
    (realization mu hd).secondMarginal A B hA hB

theorem avoiding_pairing_zero (A B : Set (Sphere E))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Avoids A B) :
    inner ℝ (WeakIndicators.indicator (probability mu) A hA)
      (operator mu hd (WeakIndicators.indicator (probability mu) B hB)) = 0 :=
  Attainment.pairing_zero_of_avoids mu (realization mu hd) A B hA hB hAB

/-- Attainment for the actual profile now needs only compactness and pointwise recovery. -/
theorem exists_optimizer_of_compact
    (hc : IsCompactOperator (operator mu hd))
    (hr : Attainment.PointwiseRecovery mu (realization mu hd).measure)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ A B : Set (Sphere E), IsOptimalPair mu p A B ∧ IsOptimizer mu p A :=
  Attainment.exists_optimalPair_of_compact_incidence mu (realization mu hd) hc hr hd p hp hp1

/-- Exchange symmetry is proved; compactness of the concrete square suffices. -/
theorem exists_optimizer_of_compact_square
    (hc : IsCompactOperator ((operator mu hd).comp (operator mu hd)))
    (hr : Attainment.PointwiseRecovery mu (realization mu hd).measure)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ A B : Set (Sphere E), IsOptimalPair mu p A B ∧ IsOptimizer mu p A :=
  Attainment.exists_optimalPair_of_compact_square mu (realization mu hd)
    (realization_swap mu hd) hc hr hd p hp hp1

end ShadowVerification.SphericalIncidenceOperator
#print axioms ShadowVerification.SphericalIncidenceOperator.pairing
#print axioms ShadowVerification.SphericalIncidenceOperator.pairing_haar
#print axioms ShadowVerification.SphericalIncidenceOperator.norm_apply_le
#print axioms ShadowVerification.SphericalIncidenceOperator.symmetric
#print axioms ShadowVerification.SphericalIncidenceOperator.nonneg_ae
#print axioms ShadowVerification.SphericalIncidenceOperator.integral_operator
#print axioms ShadowVerification.SphericalIncidenceOperator.indicator_pairing
#print axioms ShadowVerification.SphericalIncidenceOperator.avoiding_pairing_zero
#print axioms ShadowVerification.SphericalIncidenceOperator.exists_optimizer_of_compact
#print axioms ShadowVerification.SphericalIncidenceOperator.exists_optimizer_of_compact_square

#print axioms ShadowVerification.SphericalIncidenceOperator.operator_one

import LeanShadow.OrthogonalPairLaw

/-! # The actual two-step orthogonality law

Choose a Haar rotation R and independently a Haar element U fixing b.
The pair (R a, R U a) is the endpoint law of two orthogonality steps
when a and b are orthogonal. Its marginals and its relation to F² are
derived from the constructed Haar measures.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.TwoStep
open Spherical OrthogonalHaar OrthogonalIncidence ConditionalAverage PairLaw

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

def sample (a b : Sphere E) (z : OrthogonalHaar.Group E × AxisStabilizer.subgroup b) :
    Sphere E × Sphere E := (rotate z.1 a, rotate (z.1 * z.2.1) a)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem sample_continuous (a b : Sphere E) : Continuous (sample a b) := by
  apply Continuous.prodMk
  · exact rotate_continuous.comp (continuous_fst.prodMk continuous_const)
  · exact rotate_continuous.comp
      ((continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).prodMk continuous_const)

def measure (a b : Sphere E) : Measure (Sphere E × Sphere E) :=
  ((haar E).prod (AxisStabilizer.haar b)).map (sample a b)

instance probability (a b : Sphere E) : IsProbabilityMeasure (measure a b) :=
  Measure.isProbabilityMeasure_map (sample_continuous a b).measurable.aemeasurable

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem gram_sample (a b : Sphere E) (z : OrthogonalHaar.Group E × AxisStabilizer.subgroup b) :
    inner ℝ (sample a b z).1.val (sample a b z).2.val =
      inner ℝ (a : E) (rotate z.2.1 a : E) := by
  change inner ℝ (rotate z.1 a : E) (rotate (z.1 * z.2.1) a : E) = _
  rw [rotate_mul, rotate_inner]

variable (mu : Measure E) [mu.IsAddHaarMeasure]

theorem firstMarginal (a b : Sphere E) :
    MeasurePreserving Prod.fst (measure a b) (Spherical.probability mu) := by
  refine ⟨measurable_fst, ?_⟩
  rw [measure, Measure.map_map measurable_fst (sample_continuous a b).measurable]
  change ((haar E).prod (AxisStabilizer.haar b)).map ((orbit a) ∘ Prod.fst) = _
  rw [← Measure.map_map (orbit a).continuous.measurable measurable_fst, Measure.map_fst_prod]
  simp only [measure_univ, one_smul]
  exact SphericalRotation.orbit_map_probability mu a

theorem secondMarginal (a b : Sphere E) :
    MeasurePreserving Prod.snd (measure a b) (Spherical.probability mu) := by
  refine ⟨measurable_snd, ?_⟩
  apply Measure.ext
  intro A hA
  let F : Sphere E → ℝ≥0∞ := A.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hA
  have hm : Measurable (fun z : OrthogonalHaar.Group E × AxisStabilizer.subgroup b =>
      rotate (z.1 * z.2.1) a) := (sample_continuous a b).snd.measurable
  have hi (U : AxisStabilizer.subgroup b) :
      (∫⁻ R, F (rotate (R * U.1) a) ∂haar E) = Spherical.probability mu A := by
    simp_rw [rotate_mul]
    have hr : Measurable (fun R : OrthogonalHaar.Group E => rotate R (rotate U.1 a)) :=
      (rotate_continuous.comp (continuous_id.prodMk continuous_const)).measurable
    rw [← lintegral_map hF hr, SphericalRotation.orbit_map_probability mu]
    simp [F, lintegral_indicator hA]
  calc
    ((measure a b).map Prod.snd) A =
        ∫⁻ z, F (rotate (z.1 * z.2.1) a) ∂(haar E).prod (AxisStabilizer.haar b) := by
      calc
        _ = ∫⁻ y, F y ∂(measure a b).map Prod.snd := by simp [F, lintegral_indicator hA]
        _ = ∫⁻ z, F z.2 ∂measure a b := lintegral_map hF measurable_snd
        _ = _ := lintegral_map (hF.comp measurable_snd) (sample_continuous a b).measurable
    _ = ∫⁻ U : AxisStabilizer.subgroup b, ∫⁻ R, F (rotate (R * U.1) a)
        ∂haar E ∂AxisStabilizer.haar b := by
      exact (lintegral_prod _ (hF.comp hm).aemeasurable).trans
        (lintegral_lintegral_swap (hF.comp hm).aemeasurable)
    _ = Spherical.probability mu A := by simp_rw [hi]; simp

/-- The square of the actual incidence operator has the constructed two-step pairing. -/
theorem continuous_pairing (hd : 1 < Module.finrank ℝ E)
    (a b : Sphere E) (hab : inner ℝ (a : E) (b : E) = 0)
    (u v : C(Sphere E, ℝ)) :
    inner ℝ (ContinuousMap.toLp 2 (Spherical.probability mu) ℝ u)
      (SphericalIncidenceOperator.operator mu hd (SphericalIncidenceOperator.operator mu hd
        (ContinuousMap.toLp 2 (Spherical.probability mu) ℝ v))) =
      ∫ z : Sphere E × Sphere E, u z.1 * v z.2 ∂measure a b := by
  have hba : inner ℝ (b : E) (a : E) = 0 := by rw [real_inner_comm, hab]
  rw [PairLaw.continuous_image mu hd b a hba v,
    PairLaw.continuous_pairing mu hd a b hab]
  simp_rw [spherical_orbit b a v, ← integral_const_mul]
  let k : C(OrthogonalHaar.Group E × AxisStabilizer.subgroup b, ℝ) :=
    ⟨fun z => u (sample a b z).1 * v (sample a b z).2,
      (u.continuous.comp (sample_continuous a b).fst).mul
        (v.continuous.comp (sample_continuous a b).snd)⟩
  have hi := memLp_one_iff_integrable.mp
    (k.memLp ℝ (p := 1) (μ := (haar E).prod (AxisStabilizer.haar b)))
  change (∫ R, ∫ U, k (R,U) ∂AxisStabilizer.haar b ∂haar E) = _
  rw [← integral_prod _ hi]
  exact (integral_map_of_stronglyMeasurable (sample_continuous a b).measurable
    (show StronglyMeasurable (fun z : Sphere E × Sphere E => u z.1 * v z.2) by
      exact (show Continuous _ by fun_prop).stronglyMeasurable)).symm

end ShadowVerification.TwoStep
#print axioms ShadowVerification.TwoStep.sample_continuous
#print axioms ShadowVerification.TwoStep.gram_sample
#print axioms ShadowVerification.TwoStep.firstMarginal
#print axioms ShadowVerification.TwoStep.secondMarginal
#print axioms ShadowVerification.TwoStep.continuous_pairing

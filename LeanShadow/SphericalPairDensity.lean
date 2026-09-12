import LeanShadow.TwoStepGramClass

/-! # Recovering an invariant pair density from its scalar Gram density -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.PairDensity
open Spherical OrthogonalHaar InvariantPair

theorem map_weighted {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (eta : Measure X) (p : X → Y) (hp : Measurable p)
    (f : Y → ℝ≥0∞) (hf : Measurable f) :
    (eta.withDensity (fun x => f (p x))).map p = (eta.map p).withDensity f := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply hp hS, withDensity_apply _ (hp hS), withDensity_apply _ hS,
    ← lintegral_indicator hS, lintegral_map (hf.indicator hS) hp,
    ← lintegral_indicator (hp hS)]
  congr 1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [Nontrivial E] in
theorem invariant_weight (eta : Measure (Sphere E × Sphere E)) (he : Invariant eta)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    Invariant (eta.withDensity (fun z => f (gram z))) := by
  intro R
  refine ⟨(he R).measurable, ?_⟩
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (he R).measurable hS,
    withDensity_apply _ ((he R).measurable hS), withDensity_apply _ hS,
    ← lintegral_indicator ((he R).measurable hS), ← lintegral_indicator hS]
  have hp := (he R).lintegral_comp ((hf.comp gram_continuous.measurable).indicator hS)
  calc
    _ = ∫⁻ z, S.indicator (fun z => f (gram z)) (diagonal R z) ∂eta := by
      congr 1
      funext z
      classical
      by_cases hz : InvariantPair.diagonal R z ∈ S
      · rw [Set.indicator_of_mem (show z ∈ InvariantPair.diagonal R ⁻¹' S from hz),
          Set.indicator_of_mem hz]
        simp only [gram, InvariantPair.diagonal, rotate_inner]
      · rw [Set.indicator_of_notMem (show z ∉ InvariantPair.diagonal R ⁻¹' S from hz),
          Set.indicator_of_notMem hz]
    _ = _ := hp

theorem invariant_product (mu : Measure E) [mu.IsAddHaarMeasure] :
    Invariant ((probability mu).prod (probability mu)) := by
  intro R
  exact (SphericalRotation.measurePreserving_rotate mu R).prod
    (SphericalRotation.measurePreserving_rotate mu R)

theorem invariant_twoStep (a b : Sphere E) : Invariant (TwoStep.measure a b) := by
  intro S
  have hm : Measurable (diagonal S) :=
    (diagonal_continuous.comp (continuous_const.prodMk continuous_id)).measurable
  refine ⟨hm, ?_⟩
  rw [TwoStep.measure, Measure.map_map hm (TwoStep.sample_continuous a b).measurable]
  let L : OrthogonalHaar.Group E × AxisStabilizer.subgroup b →
      OrthogonalHaar.Group E × AxisStabilizer.subgroup b := fun z => (S * z.1, z.2)
  have hp : MeasurePreserving L ((haar E).prod (AxisStabilizer.haar b))
      ((haar E).prod (AxisStabilizer.haar b)) :=
    (measurePreserving_mul_left (haar E) S).prod (MeasurePreserving.id _)
  have hh : diagonal S ∘ TwoStep.sample a b = TwoStep.sample a b ∘ L := by
    funext z
    simp only [Function.comp_apply, InvariantPair.diagonal, TwoStep.sample, L, rotate_mul, mul_assoc]
  rw [hh, ← Measure.map_map (TwoStep.sample_continuous a b).measurable hp.measurable, hp.map_eq]

/-- Any scalar Gram density lifts to the corresponding invariant pair density. -/
theorem density_eq (nu eta : Measure (Sphere E × Sphere E))
    [IsFiniteMeasure nu] [IsFiniteMeasure eta] (hn : Invariant nu) (he : Invariant eta)
    (hac : nu.map gram ≪ eta.map gram) :
    nu = eta.withDensity (fun z => (nu.map gram).rnDeriv (eta.map gram) (gram z)) := by
  let f := (nu.map gram).rnDeriv (eta.map gram)
  have hf : Measurable f := Measure.measurable_rnDeriv _ _
  have hw : (eta.withDensity (fun z => f (gram z))).map gram = nu.map gram := by
    rw [map_weighted eta gram gram_continuous.measurable f hf]
    exact Measure.withDensity_rnDeriv_eq _ _ hac
  have hi : (∫⁻ z, f (gram z) ∂eta) ≠ ∞ := by
    rw [← lintegral_map hf gram_continuous.measurable]
    have hfinite := measure_ne_top (nu.map gram) Set.univ
    rw [← Measure.withDensity_rnDeriv_eq _ _ hac, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] at hfinite
    exact hfinite
  let : IsFiniteMeasure (eta.withDensity (fun z => f (gram z))) := isFiniteMeasure_withDensity hi
  exact ext_of_gram nu _ hn (invariant_weight eta he f hf) hw.symm

/-- The actual two-step measure is absolutely continuous, without an assumed kernel identity. -/
theorem twoStep_absolutelyContinuous (mu : Measure E) [mu.IsAddHaarMeasure]
    (hd : 2 < Module.finrank ℝ E) (a b : Sphere E)
    (hba : inner ℝ (b : E) (a : E) = 0) :
    TwoStep.measure a b ≪ (probability mu).prod (probability mu) := by
  rw [density_eq _ _ (invariant_twoStep a b) (invariant_product mu)
    (TwoStepGram.absolutelyContinuous mu hd a b hba)]
  exact withDensity_absolutelyContinuous _ _

end ShadowVerification.PairDensity
#print axioms ShadowVerification.PairDensity.map_weighted
#print axioms ShadowVerification.PairDensity.invariant_weight
#print axioms ShadowVerification.PairDensity.invariant_product
#print axioms ShadowVerification.PairDensity.invariant_twoStep
#print axioms ShadowVerification.PairDensity.density_eq
#print axioms ShadowVerification.PairDensity.twoStep_absolutelyContinuous

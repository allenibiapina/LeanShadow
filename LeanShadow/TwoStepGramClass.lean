import LeanShadow.InvariantPairMeasure

/-! # Absolute continuity of the actual two-step Gram law -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.TwoStepGram
open Spherical OrthogonalHaar AxisCoordinates InvariantPair
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

theorem product_null_iff (hd : 1 < Module.finrank ℝ E)
    (N : Set ℝ) (hN : MeasurableSet N) :
    ((probability mu).prod (probability mu)).map gram N = 0 ↔
      volume (N ∩ Ioo (-1) 1) = 0 := by
  rw [Measure.map_apply gram_continuous.measurable hN,
    Measure.prod_apply (hN.preimage gram_continuous.measurable),
    lintegral_eq_zero_iff (measurable_measure_prodMk_left
      (hN.preimage gram_continuous.measurable))]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.exists
    exact (LatitudeClass.coordinate_null_iff mu hd x N hN).mp hx
  · intro h
    exact Eventually.of_forall fun x => (LatitudeClass.coordinate_null_iff mu hd x N hN).mpr h

omit mu in
theorem twoStep_null_iff (hd : 2 < Module.finrank ℝ E) (a b : Sphere E)
    (hba : inner ℝ (b : E) (a : E) = 0) (N : Set ℝ) (hN : MeasurableSet N) :
    (TwoStep.measure a b).map gram N = 0 ↔ volume (N ∩ Ioo (-1) 1) = 0 := by
  have hd' : 1 < Module.finrank ℝ E := by omega
  let : Nontrivial (perpendicular b) := perpendicular_nontrivial b hd'
  have hdP : 1 < Module.finrank ℝ (perpendicular b) := by
    have he := perpendicular_finrank b
    omega
  let aP : Sphere (perpendicular b) :=
    ⟨⟨a, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hba⟩, a.property⟩
  have hg : (TwoStep.measure a b).map gram =
      (AxisStabilizer.haar b).map (fun U => inner ℝ (a : E) (rotate U.1 a : E)) := by
    rw [TwoStep.measure, Measure.map_map gram_continuous.measurable
      (TwoStep.sample_continuous a b).measurable]
    have hf : gram ∘ TwoStep.sample a b =
        (fun U : AxisStabilizer.subgroup b => inner ℝ (a : E) (rotate U.1 a : E)) ∘ Prod.snd :=
      funext (TwoStep.gram_sample a b)
    rw [hf, ← Measure.map_map (by fun_prop) measurable_snd, Measure.map_snd_prod]
    simp
  rw [hg]
  have horbit := Equatorial.orbit_map_spherical hd' b a hba
  have he : (AxisStabilizer.haar b).map
      (fun U => inner ℝ (a : E) (rotate U.1 a : E)) =
      (probability (Measure.addHaar : Measure (perpendicular b))).map
        (fun y : Sphere (perpendicular b) => inner ℝ (aP : perpendicular b) (y : perpendicular b)) := by
    calc
      _ = ((AxisStabilizer.haar b).map (fun U => rotate U.1 a)).map
          (fun y : Sphere E => inner ℝ (a : E) (y : E)) := by
        rw [Measure.map_map (by fun_prop) (by
          exact (rotate_continuous.comp (continuous_subtype_val.prodMk continuous_const)).measurable)]
        rfl
      _ = _ := by
        rw [horbit, Measure.map_map (by fun_prop) (Equatorial.embed_continuous b).measurable]
        rfl
  rw [he, Measure.map_apply (by fun_prop) hN]
  exact LatitudeClass.coordinate_null_iff (Measure.addHaar : Measure (perpendicular b)) hdP aP N hN

/-- Only the dimension bound n≥3 is needed for the scalar absolute-continuity step. -/
theorem absolutelyContinuous (hd : 2 < Module.finrank ℝ E) (a b : Sphere E)
    (hba : inner ℝ (b : E) (a : E) = 0) :
    (TwoStep.measure a b).map gram ≪ ((probability mu).prod (probability mu)).map gram := by
  intro N hz
  let eta := ((probability mu).prod (probability mu)).map gram
  apply measure_mono_null (subset_toMeasurable eta N)
  apply (twoStep_null_iff hd a b hba (toMeasurable eta N) (measurableSet_toMeasurable _ _)).mpr
  apply (product_null_iff mu (by omega) (toMeasurable eta N) (measurableSet_toMeasurable _ _)).mp
  exact (measure_toMeasurable N).trans hz

end ShadowVerification.TwoStepGram
#print axioms ShadowVerification.TwoStepGram.product_null_iff
#print axioms ShadowVerification.TwoStepGram.twoStep_null_iff
#print axioms ShadowVerification.TwoStepGram.absolutelyContinuous

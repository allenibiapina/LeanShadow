import LeanShadow.LatitudeCoordinate
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-! # Polar integration transfers null directional events to ambient Haar measure -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.DirectionNull
open Spherical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

def rays (A : Set (Sphere E)) : Set E :=
  Subtype.val '' ((homeomorphUnitSphereProd E) ⁻¹' (A ×ˢ (univ : Set (Ioi (0 : ℝ)))))

theorem radial_mass_ne_zero (d : ℕ) : Measure.volumeIoiPow d univ ≠ 0 := by
  have hp : 0 < Measure.volumeIoiPow d (Iio (⟨1, by norm_num⟩ : Ioi (0 : ℝ))) := by
    rw [Measure.volumeIoiPow_apply_Iio]
    positivity
  exact ne_of_gt (hp.trans_le (measure_mono (subset_univ _)))

variable (mu : Measure E) [mu.IsAddHaarMeasure]

omit [Nontrivial E] in
/-- The full positive ray set is null exactly when its spherical section is null. -/
theorem null_iff_rays (A : Set (Sphere E)) (hA : MeasurableSet A) :
    probability mu A = 0 ↔ mu (rays A) = 0 := by
  have hp := mu.measurePreserving_homeomorphUnitSphereProd.measure_preimage
    (hA.prod MeasurableSet.univ).nullMeasurableSet
  rw [comap_subtype_coe_apply (measurableSet_singleton (0 : E)).compl] at hp
  change mu (rays A) = (mu.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1)))
    (A ×ˢ univ) at hp
  rw [Measure.prod_prod] at hp
  rw [hp]
  simp only [probability, Measure.smul_apply, smul_eq_mul, mul_eq_zero,
    ENNReal.inv_eq_zero, measure_ne_top, false_or, radial_mass_ne_zero, or_false]

def ratio (a : Sphere E) (z : E) : ℝ := inner ℝ (a : E) z / ‖z‖

omit [Nontrivial E] [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
theorem ratio_measurable (a : Sphere E) : Measurable (ratio a) := by
  exact (continuous_const.inner continuous_id).measurable.div continuous_norm.measurable

omit mu [mu.IsAddHaarMeasure] [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E] in
theorem rays_latitude (a : Sphere E) (N : Set ℝ) :
    rays {x : Sphere E | inner ℝ (a : E) (x : E) ∈ N} = (ratio a ⁻¹' N) \ {0} := by
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hn : (v : E) ≠ 0 := v.property
    refine ⟨?_, by simpa using hn⟩
    change inner ℝ (a : E) ((homeomorphUnitSphereProd E v).1 : E) ∈ N ∧ True at hv
    have hv' := hv.1
    simpa only [ratio, mem_preimage, homeomorphUnitSphereProd_apply_fst_coe,
      inner_smul_right, smul_eq_mul, div_eq_inv_mul] using hv'
  · intro hz
    let v : ({0}ᶜ : Set E) := ⟨z, hz.2⟩
    refine ⟨v, ?_, rfl⟩
    change inner ℝ (a : E) ((homeomorphUnitSphereProd E v).1 : E) ∈ N ∧ True
    refine ⟨?_, trivial⟩
    simpa only [ratio, mem_preimage, homeomorphUnitSphereProd_apply_fst_coe,
      inner_smul_right, smul_eq_mul, div_eq_inv_mul] using hz.1

/-- The normalized ambient coordinate and the spherical coordinate have the same null events. -/
theorem latitude_null_iff (a : Sphere E) (N : Set ℝ) (hN : MeasurableSet N) :
    probability mu {x : Sphere E | inner ℝ (a : E) (x : E) ∈ N} = 0 ↔
      mu (ratio a ⁻¹' N) = 0 := by
  have hA : MeasurableSet {x : Sphere E | inner ℝ (a : E) (x : E) ∈ N} :=
    hN.preimage (continuous_const.inner continuous_subtype_val).measurable
  exact (null_iff_rays mu _ hA).trans (by
    rw [rays_latitude, measure_sdiff_null (measure_singleton (0 : E))])

end ShadowVerification.DirectionNull
#print axioms ShadowVerification.DirectionNull.radial_mass_ne_zero
#print axioms ShadowVerification.DirectionNull.null_iff_rays
#print axioms ShadowVerification.DirectionNull.ratio_measurable
#print axioms ShadowVerification.DirectionNull.rays_latitude
#print axioms ShadowVerification.DirectionNull.latitude_null_iff

import LeanShadow.AxisCoordinates
import LeanShadow.SphericalRotation
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! # Nonnegative polar integration for the existing spherical measure -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.SphericalPolarIntegration
open Spherical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

theorem lintegral_norm (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f ‖x‖ ∂mu) = mu.toSphere univ *
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * f r := by
  calc
    _ = ∫⁻ x : ({0}ᶜ : Set E), f ‖x.1‖ ∂mu.comap (↑) := by
      rw [lintegral_subtype_comap (measurableSet_singleton (0 : E)).compl (fun x : E => f ‖x‖),
        restrict_compl_singleton]
    _ = ∫⁻ x : Sphere E × Ioi (0 : ℝ), f x.2.1
        ∂mu.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
      simpa only [Function.comp_def, homeomorphUnitSphereProd_apply_snd_coe] using
        mu.measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
          (Homeomorph.measurableEmbedding _) (fun x => f x.2.1)
    _ = _ := by
      rw [lintegral_prod _ (by fun_prop)]
      dsimp only
      rw [lintegral_const, mul_comm]
      unfold Measure.volumeIoiPow
      congr 1
      rw [lintegral_withDensity_eq_lintegral_mul _
        (f := fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1 ^ (Module.finrank ℝ E - 1)))
        (g := fun r : Ioi (0 : ℝ) => f r.1) (by fun_prop) (by fun_prop)]
      exact lintegral_subtype_comap measurableSet_Ioi
        (fun r : ℝ => ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * f r)

theorem probability_haar_independent (nu : Measure E) [nu.IsAddHaarMeasure]
    (a : Sphere E) : probability mu = probability nu := by
  rw [← SphericalRotation.orbit_map_probability mu a,
    ← SphericalRotation.orbit_map_probability nu a]

theorem lintegral_ratio_ball (a : Sphere E) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in ball (0 : E) 1, f (DirectionNull.ratio a x) ∂mu) =
      (mu (ball (0 : E) 1)) *
        ∫⁻ x : Sphere E, f (inner ℝ (a : E) (x : E)) ∂probability mu := by
  let F : E → ℝ≥0∞ := (ball (0 : E) 1).indicator (fun x => f (DirectionNull.ratio a x))
  let J : Set (Ioi (0 : ℝ)) := Iio ⟨1, by norm_num⟩
  have hpolar := mu.measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
    (Homeomorph.measurableEmbedding _)
    (fun x : Sphere E × Ioi (0 : ℝ) =>
      f (inner ℝ (a : E) (x.1 : E)) * J.indicator (fun _ => 1) x.2)
  have heq : (fun x : ({0}ᶜ : Set E) =>
      f (inner ℝ (a : E) ((homeomorphUnitSphereProd E x).1 : E)) *
        J.indicator (fun _ => 1) (homeomorphUnitSphereProd E x).2) = fun x => F x.1 := by
    funext x
    have hJ : (homeomorphUnitSphereProd E x).2 ∈ J ↔ ‖x.1‖ < 1 := by
      change ((homeomorphUnitSphereProd E x).2 : ℝ) < 1 ↔ _
      rw [homeomorphUnitSphereProd_apply_snd_coe]
    simp only [homeomorphUnitSphereProd_apply_fst_coe, inner_smul_right,
      F, DirectionNull.ratio, div_eq_inv_mul]
    by_cases hx : ‖x.1‖ < 1
    · rw [indicator_of_mem (hJ.mpr hx)]
      simp [hx]
    · rw [indicator_of_notMem (mt hJ.mp hx)]
      simp [hx]
  rw [heq, lintegral_subtype_comap (measurableSet_singleton (0 : E)).compl F,
    restrict_compl_singleton, lintegral_indicator measurableSet_ball] at hpolar
  rw [hpolar, lintegral_prod_mul (f := fun x : Sphere E => f (inner ℝ (a : E) (x : E)))
    (g := J.indicator (fun _ => 1)) (by fun_prop)
    (by exact (measurable_const.indicator measurableSet_Iio).aemeasurable),
    lintegral_indicator measurableSet_Iio, lintegral_one]
  have hrad : (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) J =
      (Module.finrank ℝ E : ℝ≥0∞)⁻¹ := by
    rw [Measure.volumeIoiPow_apply_Iio]
    have hd := Module.finrank_pos (R := ℝ) (M := E)
    have he : ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + 1 = (Module.finrank ℝ E : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hd
    simp [he, ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr hd)]
  rw [Measure.restrict_apply_univ, hrad]
  unfold probability
  rw [lintegral_smul_measure, Measure.toSphere_apply_univ, ENNReal.mul_inv, smul_eq_mul] <;>
    try { simp [Module.finrank_pos.ne'] }
  have hb : mu (ball (0 : E) 1) ≠ 0 := (measure_ball_pos mu 0 zero_lt_one).ne'
  have hbt : mu (ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
  calc
    _ = (Module.finrank ℝ E : ℝ≥0∞)⁻¹ *
        ∫⁻ x : Sphere E, f (inner ℝ (a : E) (x : E)) ∂mu.toSphere := mul_comm _ _
    _ = _ := by
      rw [← mul_assoc, mul_left_comm (mu (ball (0 : E) 1)),
        ENNReal.mul_inv_cancel hb hbt, mul_one]

end ShadowVerification.SphericalPolarIntegration
#print axioms ShadowVerification.SphericalPolarIntegration.lintegral_norm
#print axioms ShadowVerification.SphericalPolarIntegration.probability_haar_independent
#print axioms ShadowVerification.SphericalPolarIntegration.lintegral_ratio_ball

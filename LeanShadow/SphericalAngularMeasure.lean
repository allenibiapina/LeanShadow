import LeanShadow.SphericalPolarIntegration
import LeanShadow.PlanarLatitude
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Exact angular distribution of normalized Haar spherical measure

Axial Haar coordinates, polar integration in the perpendicular space, and
the planar polar formula give the sin-power density. Normalizing by the
whole sphere cancels all auxiliary Haar constants.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.SphericalAngularMeasure
open Spherical AxisCoordinates SphericalPolarIntegration

def angularIntegral (m : ℕ) (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ theta in Ioo (0 : ℝ) Real.pi, ENNReal.ofReal (Real.sin theta ^ m) * f (Real.cos theta)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

def axialHaar (a : Sphere E) : Measure E :=
  (volume.prod (Measure.addHaar : Measure (perpendicular a))).map (equivalence a)

instance axialHaar_isAddHaarMeasure (a : Sphere E) : (axialHaar a).IsAddHaarMeasure := by
  unfold axialHaar
  infer_instance

omit [Nontrivial E] in
theorem ball_integral (a : Sphere E) [Nontrivial (perpendicular a)]
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in ball (0 : E) 1, f (DirectionNull.ratio a x) ∂axialHaar a) =
      (Measure.addHaar : Measure (perpendicular a)).toSphere univ *
        ENNReal.ofReal ((1 : ℝ) / (Module.finrank ℝ (perpendicular a) + 1)) *
          angularIntegral (Module.finrank ℝ (perpendicular a) - 1) f := by
  let nu : Measure (perpendicular a) := Measure.addHaar
  let F : E → ℝ≥0∞ := (ball (0 : E) 1).indicator (fun x => f (DirectionNull.ratio a x))
  have hF : Measurable F := (hf.comp (DirectionNull.ratio_measurable a)).indicator measurableSet_ball
  have heq (t : ℝ) (v : perpendicular a) : F (equivalence a (t,v)) =
      if t ^ 2 + ‖v‖ ^ 2 < 1 then f (t / Real.sqrt (t ^ 2 + ‖v‖ ^ 2)) else 0 := by
    have hb : equivalence a (t,v) ∈ ball (0 : E) 1 ↔ t ^ 2 + ‖v‖ ^ 2 < 1 := by
      rw [mem_ball_zero_iff]
      have hn := norm_equivalence_sq a t v
      have hnorm := norm_nonneg (equivalence a (t,v))
      constructor <;> intro h <;> nlinarith
    simp only [F, indicator, hb, ratio_equivalence]
  rw [← lintegral_indicator measurableSet_ball]
  change (∫⁻ x, F x ∂(volume.prod nu).map (equivalence a)) = _
  have he : Measurable (equivalence a) := (equivalence a).toContinuousLinearEquiv.continuous.measurable
  rw [lintegral_map hF he,
    lintegral_prod (μ := volume) (ν := nu) (fun z : ℝ × perpendicular a => F (equivalence a z))
      (by fun_prop)]
  simp_rw [heq]
  have hn (t : ℝ) := lintegral_norm nu
    (fun r : ℝ => if t ^ 2 + r ^ 2 < 1 then f (t / Real.sqrt (t ^ 2 + r ^ 2)) else 0)
    (Measurable.ite (by measurability) (by fun_prop) measurable_const)
  simp_rw [hn]
  rw [lintegral_const_mul' _ _ (measure_ne_top _ _), ← PlanarLatitude.kernel_iterated _ f hf,
    PlanarLatitude.kernel_integral _ f hf, ← mul_assoc]
  have hd : 0 < Module.finrank ℝ (perpendicular a) := Module.finrank_pos
  have hc : ((Module.finrank ℝ (perpendicular a) - 1 : ℕ) : ℝ) + 2 =
      (Module.finrank ℝ (perpendicular a) : ℝ) + 1 := by
    rw [Nat.cast_sub hd, Nat.cast_one]
    ring
  rw [hc]
  rfl

theorem lintegral_coordinate (mu : Measure E) [mu.IsAddHaarMeasure]
    (hd : 1 < Module.finrank ℝ E) (a : Sphere E)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : Sphere E, f (inner ℝ (a : E) (x : E)) ∂probability mu) =
      (angularIntegral (Module.finrank ℝ E - 2) (fun _ => 1))⁻¹ *
        angularIntegral (Module.finrank ℝ E - 2) f := by
  let : Nontrivial (perpendicular a) := perpendicular_nontrivial a hd
  let N := Module.finrank ℝ (perpendicular a)
  let C : ℝ≥0∞ := (Measure.addHaar : Measure (perpendicular a)).toSphere univ *
    ENNReal.ofReal ((1 : ℝ) / (N+1))
  have hn : N - 1 = Module.finrank ℝ E - 2 := by
    have h := perpendicular_finrank a
    dsimp [N]
    omega
  have hC0 : C ≠ 0 := by
    apply mul_ne_zero
    · intro h
      exact (Measure.addHaar : Measure (perpendicular a)).toSphere_ne_zero
        (Measure.measure_univ_eq_zero.mp h)
    · apply ne_of_gt
      positivity
  have hCt : C ≠ ∞ := ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hb0 : axialHaar a (ball (0 : E) 1) ≠ 0 := (measure_ball_pos _ _ zero_lt_one).ne'
  have hbt : axialHaar a (ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
  have hball (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
      axialHaar a (ball (0 : E) 1) *
          (∫⁻ x : Sphere E, g (inner ℝ (a : E) (x : E)) ∂probability mu) =
        C * angularIntegral (Module.finrank ℝ E - 2) g := by
    rw [probability_haar_independent mu (axialHaar a) a,
      ← lintegral_ratio_ball (axialHaar a) a g hg, ball_integral a g hg]
    simp only [C, N, hn]
  have hone := hball (fun _ => 1) measurable_const
  simp only [lintegral_one, measure_univ, mul_one] at hone
  have hJ0 : angularIntegral (Module.finrank ℝ E - 2) (fun _ => 1) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hone
    exact hb0 hone
  have hJt : angularIntegral (Module.finrank ℝ E - 2) (fun _ => 1) ≠ ∞ :=
    (ENNReal.lt_top_of_mul_ne_top_right (hone ▸ hbt) hC0).ne
  have he := hball f hf
  rw [hone, mul_assoc] at he
  have he' := (ENNReal.mul_right_inj hC0 hCt).mp he
  calc
    _ = (angularIntegral (Module.finrank ℝ E - 2) (fun _ => 1))⁻¹ *
        (angularIntegral (Module.finrank ℝ E - 2) (fun _ => 1) *
          ∫⁻ x : Sphere E, f (inner ℝ (a : E) (x : E)) ∂probability mu) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hJ0 hJt, one_mul]
    _ = _ := by rw [he']

end ShadowVerification.SphericalAngularMeasure
#print axioms ShadowVerification.SphericalAngularMeasure.ball_integral
#print axioms ShadowVerification.SphericalAngularMeasure.lintegral_coordinate

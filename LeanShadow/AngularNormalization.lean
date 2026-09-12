import LeanShadow.SphericalAngularMeasure
import LeanShadow.CapFunctions

/-! # Angular normalization and integration over a spherical slice -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Real
open scoped Topology ENNReal
namespace ShadowVerification.AngularNormalization
open Spherical SphericalAngularMeasure CapFunctions

theorem lintegral_Ioo_eq_ofReal (w : ℝ → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hw : Continuous w) (hpos : ∀ t ∈ Ioo (0 : ℝ) r, 0 ≤ w t) :
    (∫⁻ t in Ioo (0 : ℝ) r, ENNReal.ofReal (w t)) = ENNReal.ofReal (∫ t in 0..r, w t) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (hw.integrableOn_Icc.mono_set Ioo_subset_Icc_self)]
  · rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hr]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hpos t ht

theorem angularIntegral_one (m : ℕ) :
    angularIntegral m (fun _ => 1) = ENNReal.ofReal (sinPrimitive m Real.pi) := by
  simp only [angularIntegral,mul_one]
  exact lintegral_Ioo_eq_ofReal _ _ Real.pi_pos.le (by fun_prop)
    (fun t ht => pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le ht.2.le) _)

theorem angularIntegral_slice (m : ℕ) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) Real.pi)
    (h : ℝ → ℝ≥0∞) :
    angularIntegral m ((Ioi (Real.cos r)).indicator h) =
      ∫⁻ t in Ioo (0 : ℝ) r, ENNReal.ofReal (Real.sin t ^ m) * h (Real.cos t) := by
  unfold angularIntegral
  have heq := setLIntegral_congr_fun (μ := volume) (s := Ioo (0 : ℝ) Real.pi) measurableSet_Ioo
    (f := fun t : ℝ => ENNReal.ofReal (Real.sin t ^ m) *
      (Ioi (Real.cos r)).indicator h (Real.cos t))
    (g := (Iio r).indicator (fun t : ℝ => ENNReal.ofReal (Real.sin t ^ m) * h (Real.cos t)))
    (fun t ht => ?_)
  · rw [heq,lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
    have hset : Iio r ∩ Ioo (0 : ℝ) Real.pi = Ioo 0 r := by
      ext t
      simp only [mem_inter_iff,mem_Iio,mem_Ioo]
      constructor <;> intro ht
      · exact ⟨ht.2.1,ht.1⟩
      · exact ⟨ht.2,ht.1,ht.2.trans_le hr.2⟩
    rw [hset]
  · have hc : Real.cos r < Real.cos t ↔ t < r :=
      Real.strictAntiOn_cos.lt_iff_gt hr ⟨ht.1.le,ht.2.le⟩
    by_cases htr : t < r <;> simp [indicator,hc,htr]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

def slice (a : Sphere E) (r : ℝ) : Set (Sphere E) :=
  {x | Real.cos r < inner ℝ (a : E) (x : E)}

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem slice_measurable (a : Sphere E) (r : ℝ) : MeasurableSet (slice a r) :=
  measurableSet_lt measurable_const (by fun_prop)

theorem lintegral_slice (mu : Measure E) [mu.IsAddHaarMeasure]
    (hd : 1 < Module.finrank ℝ E) (a : Sphere E) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) Real.pi)
    (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ x in slice a r, h (inner ℝ (a : E) (x : E)) ∂probability mu) =
      (ENNReal.ofReal (sinPrimitive (Module.finrank ℝ E - 2) Real.pi))⁻¹ *
        ∫⁻ t in Ioo (0 : ℝ) r,
          ENNReal.ofReal (Real.sin t ^ (Module.finrank ℝ E - 2)) * h (Real.cos t) := by
  have heq : (fun x : Sphere E =>
      (Ioi (Real.cos r)).indicator h (inner ℝ (a : E) (x : E))) =
      (slice a r).indicator (fun x : Sphere E => h (inner ℝ (a : E) (x : E))) := by
    funext x
    simp only [indicator,slice,mem_Ioi,mem_ofPred_eq]
  have hcoord := lintegral_coordinate mu hd a ((Ioi (Real.cos r)).indicator h)
    (hh.indicator measurableSet_Ioi)
  rw [heq,lintegral_indicator (slice_measurable a r),angularIntegral_one,
    angularIntegral_slice _ r hr h] at hcoord
  exact hcoord

end ShadowVerification.AngularNormalization
#print axioms ShadowVerification.AngularNormalization.lintegral_Ioo_eq_ofReal
#print axioms ShadowVerification.AngularNormalization.angularIntegral_one
#print axioms ShadowVerification.AngularNormalization.angularIntegral_slice
#print axioms ShadowVerification.AngularNormalization.slice_measurable
#print axioms ShadowVerification.AngularNormalization.lintegral_slice

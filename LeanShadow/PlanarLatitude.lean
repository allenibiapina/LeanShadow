import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! # The two-dimensional polar calculation behind spherical latitudes -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Real
open scoped Topology ENNReal
namespace ShadowVerification.PlanarLatitude

def kernel (m : ℕ) (f : ℝ → ℝ≥0∞) (q : ℝ × ℝ) : ℝ≥0∞ :=
  if 0 < q.2 ∧ q.1 ^ 2 + q.2 ^ 2 < 1 then
    ENNReal.ofReal (q.2 ^ m) * f (q.1 / Real.sqrt (q.1 ^ 2 + q.2 ^ 2)) else 0

theorem kernel_measurable (m : ℕ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    Measurable (kernel m f) := by
  unfold kernel
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

theorem kernel_iterated (m : ℕ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ q : ℝ × ℝ, kernel m f q) =
      ∫⁻ t : ℝ, ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ m) *
        (if t ^ 2 + r ^ 2 < 1 then f (t / Real.sqrt (t ^ 2 + r ^ 2)) else 0) := by
  rw [Measure.volume_eq_prod, lintegral_prod _ (kernel_measurable m f hf).aemeasurable]
  apply lintegral_congr
  intro t
  rw [← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro r
  by_cases hr : 0 < r <;> by_cases hb : t ^ 2 + r ^ 2 < 1 <;>
    simp [kernel, hr, hb]

theorem polar_kernel (m : ℕ) (f : ℝ → ℝ≥0∞) (R theta : ℝ)
    (hR : 0 < R) (htheta : theta ∈ Ioo (-Real.pi) Real.pi) :
    ENNReal.ofReal R * kernel m f (polarCoord.symm (R,theta)) =
      (Iio (1 : ℝ)).indicator (fun r => ENNReal.ofReal (r ^ (m+1))) R *
      (Ioi (0 : ℝ)).indicator
        (fun t => ENNReal.ofReal (Real.sin t ^ m) * f (Real.cos t)) theta := by
  have hsq : (R * Real.cos theta) ^ 2 + (R * Real.sin theta) ^ 2 = R ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq theta]
  have hr : R ^ 2 < 1 ↔ R < 1 := by constructor <;> intro h <;> nlinarith
  have ht : 0 < Real.sin theta ↔ 0 < theta := by
    constructor
    · intro h
      by_contra! hn
      exact (not_lt_of_ge (Real.sin_nonpos_of_nonpos_of_neg_pi_le hn htheta.1.le)) h
    · intro h
      exact Real.sin_pos_of_pos_of_lt_pi h htheta.2
  have hratio : R * Real.cos theta / Real.sqrt (R ^ 2) = Real.cos theta := by
    rw [Real.sqrt_sq hR.le]
    field_simp
  simp only [kernel, polarCoord_symm_apply, hsq, mul_pos_iff_of_pos_left hR, ht, hr, hratio]
  by_cases ht0 : 0 < theta <;> by_cases hr1 : R < 1
  · simp only [ht0, hr1, and_self, ite_true, indicator, mem_Iio, mem_Ioi]
    rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hR.le _), pow_succ,
      ENNReal.ofReal_mul (pow_nonneg hR.le _)]
    ac_rfl
  · simp [ht0, hr1]
  · simp [ht0, hr1]
  · simp [ht0, hr1]

theorem kernel_integral (m : ℕ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ q : ℝ × ℝ, kernel m f q) =
      ENNReal.ofReal ((1 : ℝ) / (m+2)) *
        ∫⁻ theta in Ioo (0 : ℝ) Real.pi, ENNReal.ofReal (Real.sin theta ^ m) * f (Real.cos theta) := by
  rw [← lintegral_comp_polarCoord_symm]
  simp only [smul_eq_mul]
  have heq := setLIntegral_congr_fun (μ := volume) (polarCoord.open_target.measurableSet)
    (fun q hq => polar_kernel m f q.1 q.2 hq.1 hq.2)
  rw [heq]
  change (∫⁻ q : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    (Iio (1 : ℝ)).indicator (fun r => ENNReal.ofReal (r ^ (m+1))) q.1 *
      (Ioi (0 : ℝ)).indicator
        (fun t => ENNReal.ofReal (Real.sin t ^ m) * f (Real.cos t)) q.2) = _
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := (Iio (1 : ℝ)).indicator (fun r => ENNReal.ofReal (r ^ (m+1))))
      (g := (Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal (Real.sin t ^ m) * f (Real.cos t)))
      ((by fun_prop : Measurable (fun r : ℝ => ENNReal.ofReal (r ^ (m+1)))).indicator measurableSet_Iio).aemeasurable
      ((by fun_prop : Measurable (fun t : ℝ => ENNReal.ofReal (Real.sin t ^ m) * f (Real.cos t))).indicator measurableSet_Ioi).aemeasurable,
    lintegral_indicator measurableSet_Iio, lintegral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Iio, Measure.restrict_restrict measurableSet_Ioi]
  have hfirst : Iio (1 : ℝ) ∩ Ioi 0 = Ioo 0 1 := by ext r; simp; tauto
  have hsecond : Ioi (0 : ℝ) ∩ Ioo (-Real.pi) Real.pi = Ioo 0 Real.pi := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
    constructor <;> intro h
    · exact ⟨h.1,h.2.2⟩
    · exact ⟨h.1, by linarith [Real.pi_pos], h.2⟩
  rw [hfirst, hsecond]
  congr 1
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    norm_num [add_assoc]
  · exact (continuous_pow _).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact pow_nonneg hr.1.le _

end ShadowVerification.PlanarLatitude
#print axioms ShadowVerification.PlanarLatitude.kernel_measurable
#print axioms ShadowVerification.PlanarLatitude.kernel_iterated
#print axioms ShadowVerification.PlanarLatitude.polar_kernel
#print axioms ShadowVerification.PlanarLatitude.kernel_integral

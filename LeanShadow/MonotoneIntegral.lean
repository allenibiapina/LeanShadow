import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-! # Integration inequalities that retain monotone singular variation

A monotone function's ordinary derivative is the density of only the
absolutely continuous part of its Stieltjes measure. The whole measure
bounds that density integral, including jumps and singular continuous mass.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace ShadowVerification.MonotoneIntegral

theorem stieltjes_deriv_integrable (f : StieltjesFunction ℝ) (a b : ℝ) :
    IntegrableOn (deriv f) (Icc a b) := by
  apply (Measure.integrableOn_toReal_rnDeriv (μ := f.measure) (ν := volume)
    (isCompact_Icc.measure_lt_top.ne)).congr
  filter_upwards [ae_restrict_of_ae f.ae_hasDerivAt] with x hx
  exact hx.deriv.symm

theorem stieltjes_density_integral (f : StieltjesFunction ℝ) (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, deriv f x) =
      (volume.withDensity (f.measure.rnDeriv volume)).real (Ioc a b) := by
  rw [intervalIntegral.integral_of_le hab]
  calc
    _ = ∫ x in Ioc a b, (f.measure.rnDeriv volume x).toReal := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae f.ae_hasDerivAt] with x hx
      exact hx.deriv
    _ = _ := Measure.setIntegral_toReal_rnDeriv_eq_withDensity (Ioc a b)

/-- The missing mass is exactly a nonnegative singular measure. -/
theorem stieltjes_increment_decomposition (f : StieltjesFunction ℝ) (a b : ℝ) (hab : a ≤ b) :
    f b - f a = (∫ x in a..b, deriv f x) + (f.measure.singularPart volume).real (Ioc a b) := by
  rw [stieltjes_density_integral f a b hab]
  have hf : f.measure (Ioc a b) ≠ ∞ := by rw [f.measure_Ioc]; exact ENNReal.ofReal_ne_top
  have hs : f.measure.singularPart volume (Ioc a b) ≠ ∞ :=
    (Measure.singularPart_le _ _ _ |>.trans_lt hf.lt_top).ne
  have ha : (volume.withDensity (f.measure.rnDeriv volume)) (Ioc a b) ≠ ∞ :=
    (Measure.withDensity_rnDeriv_le _ _ _ |>.trans_lt hf.lt_top).ne
  have he := congrArg (fun μ : Measure ℝ => μ.real (Ioc a b))
    (Measure.haveLebesgueDecomposition_add f.measure volume)
  rw [measureReal_add_apply hs ha,measureReal_def,f.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (f.mono hab))] at he
  linarith

theorem monotone_deriv_integrable (f : ℝ → ℝ) (hf : Monotone f) (a b : ℝ) :
    IntegrableOn (deriv f) (Icc a b) := by
  apply (Measure.integrableOn_toReal_rnDeriv (μ := hf.stieltjesFunction.measure) (ν := volume)
    (isCompact_Icc.measure_lt_top.ne)).congr
  filter_upwards [ae_restrict_of_ae hf.ae_hasDerivAt] with x hx
  exact hx.deriv.symm

theorem monotone_integral_deriv_le (f : ℝ → ℝ) (hf : Monotone f) (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, deriv f x) ≤ f b - f a := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have hfin : hf.stieltjesFunction.measure (Ioo a b) ≠ ∞ :=
    (measure_mono (Ioo_subset_Icc_self) |>.trans_lt isCompact_Icc.measure_lt_top).ne
  have h := Measure.setIntegral_toReal_rnDeriv_le
    (μ := hf.stieltjesFunction.measure) (ν := volume) hfin
  have he : (∫ x in a..b, deriv f x) =
      ∫ x in Ioo a b, (hf.stieltjesFunction.measure.rnDeriv volume x).toReal := by
    rw [intervalIntegral.integral_of_le hab.le,integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hf.ae_hasDerivAt] with x hx
    exact hx.deriv
  rw [he]
  apply h.trans
  rw [measureReal_def,StieltjesFunction.measure_Ioo]
  have hleft : leftLim hf.stieltjesFunction b = leftLim f b :=
    leftLim_rightLim (hf.tendsto_leftLim b)
  rw [hleft,Monotone.stieltjesFunction_eq]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (hf.rightLim_le_leftLim hab))]
  exact sub_le_sub (hf.leftLim_le le_rfl) (hf.le_rightLim le_rfl)

end ShadowVerification.MonotoneIntegral
#print axioms ShadowVerification.MonotoneIntegral.stieltjes_deriv_integrable
#print axioms ShadowVerification.MonotoneIntegral.stieltjes_density_integral
#print axioms ShadowVerification.MonotoneIntegral.monotone_deriv_integrable
#print axioms ShadowVerification.MonotoneIntegral.monotone_integral_deriv_le

#print axioms ShadowVerification.MonotoneIntegral.stieltjes_increment_decomposition

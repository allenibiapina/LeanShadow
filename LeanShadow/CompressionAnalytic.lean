import LeanShadow.CompactFrechetIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Analyticity of the compression integrals

We complexify the one-dimensional parameter. A positive combination a + t b
stays in the right half-plane when Re(t)>0. Its complex powers are holomorphic;
compactness supplies the domination needed to integrate their derivatives.
Restricting the resulting holomorphic integral to positive real parameters
proves real analyticity, even for measures restricted to arbitrary Borel sets.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Metric
open scoped Topology
namespace ShadowVerification.CompressionAnalytic

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Compact-fibre differentiation for a complex parameter on an open domain. -/
theorem hasDerivAt_integral_complex (nu : Measure X) [IsFiniteMeasure nu]
    (U : Set ℂ) (hU : IsOpen U) (F D : ℂ → X → ℂ)
    (hF : ContinuousOn (fun z : ℂ × X => F z.1 z.2) (U ×ˢ univ))
    (hD : ContinuousOn (fun z : ℂ × X => D z.1 z.2) (U ×ˢ univ))
    (hd : ∀ z ∈ U, ∀ x, HasDerivAt (fun w => F w x) (D z x) z)
    (z : ℂ) (hz : z ∈ U) :
    HasDerivAt (fun w => ∫ x, F w x ∂nu) (∫ x, D z x ∂nu) z := by
  obtain ⟨r, hr, hsub, C, hC⟩ := Parametric.local_uniform_bound U hU D hD z hz
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := ball z r) (bound := fun _ => C) (ball_mem_nhds z hr) ?_ ?_ ?_ ?_
    (integrable_const C) ?_).2
  · filter_upwards [hU.mem_nhds hz] with w hw
    exact (Parametric.continuous_fibre U F hF w hw).aestronglyMeasurable
  · exact (Parametric.continuous_fibre U F hF z hz).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (Parametric.continuous_fibre U D hD z hz).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x w hw => hC w hw x)
  · exact Filter.Eventually.of_forall (fun x w hw => hd w (hsub hw) x)

def rightHalfPlane : Set ℂ := {z | 0 < z.re}

theorem isOpen_rightHalfPlane : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

/-- Positive coefficients keep the complexified denominator off the branch cut. -/
theorem positive_combination_slitPlane (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a + b) (z : ℂ) (hz : z ∈ rightHalfPlane) :
    (a : ℂ) + z * (b : ℂ) ∈ Complex.slitPlane := by
  apply Or.inl
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  change 0 < z.re at hz
  by_cases ha0 : a = 0
  · rw [ha0]
    exact add_pos_of_nonneg_of_pos (by norm_num) (mul_pos hz (by linarith))
  · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne ha (Ne.symm ha0)) (mul_nonneg hz.le hb)

/-- Holomorphy is proved for the integral, rather than inferred merely from
pointwise holomorphy of the integrand. -/
theorem analyticOnNhd_complex_integral (nu : Measure X) [IsFiniteMeasure nu]
    (a b : X → ℝ) (ha : Continuous a) (hb : Continuous b)
    (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x) (hab : ∀ x, 0 < a x + b x)
    (c : ℂ) :
    AnalyticOnNhd ℂ (fun z => ∫ x, ((a x : ℂ) + z * (b x : ℂ)) ^ c ∂nu)
      rightHalfPlane := by
  let F := fun z : ℂ => fun x : X => ((a x : ℂ) + z * (b x : ℂ)) ^ c
  let D := fun z : ℂ => fun x : X => c * ((a x : ℂ) + z * (b x : ℂ)) ^ (c - 1) * (b x : ℂ)
  have hbase : Continuous (fun z : ℂ × X => (a z.2 : ℂ) + z.1 * (b z.2 : ℂ)) := by
    fun_prop
  have hcut : ∀ z ∈ rightHalfPlane ×ˢ (univ : Set X),
      (a z.2 : ℂ) + z.1 * (b z.2 : ℂ) ∈ Complex.slitPlane :=
    fun z hz => positive_combination_slitPlane (a z.2) (b z.2)
      (ha0 _) (hb0 _) (hab _) z.1 hz.1
  have hF : ContinuousOn (fun z : ℂ × X => F z.1 z.2) (rightHalfPlane ×ˢ univ) :=
    hbase.continuousOn.cpow_const hcut
  have hD : ContinuousOn (fun z : ℂ × X => D z.1 z.2) (rightHalfPlane ×ˢ univ) :=
    (continuousOn_const.mul (hbase.continuousOn.cpow_const hcut)).mul
      (Complex.continuous_ofReal.comp (hb.comp continuous_snd)).continuousOn
  apply DifferentiableOn.analyticOnNhd _ isOpen_rightHalfPlane
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply (hasDerivAt_integral_complex nu rightHalfPlane isOpen_rightHalfPlane F D hF hD ?_ z hz).differentiableAt
  intro w hw x
  simpa only [F, D, mul_one, one_mul, zero_add, Pi.add_apply, id_eq] using
    ((hasDerivAt_const w (a x : ℂ)).add
      ((hasDerivAt_id w).mul_const (b x : ℂ))).cpow_const
        (positive_combination_slitPlane (a x) (b x) (ha0 x) (hb0 x) (hab x) w hw)

/-- The actual real power integral is real analytic at every positive parameter. -/
theorem analyticOnNhd_real_integral (nu : Measure X) [IsFiniteMeasure nu]
    (a b : X → ℝ) (ha : Continuous a) (hb : Continuous b)
    (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x) (hab : ∀ x, 0 < a x + b x)
    (c : ℝ) :
    AnalyticOnNhd ℝ (fun t => ∫ x, (a x + t * b x) ^ c ∂nu) (Ioi 0) := by
  intro t ht
  have hc := analyticOnNhd_complex_integral nu a b ha hb ha0 hb0 hab (c : ℂ)
    (t : ℂ) ht
  have hre := (Complex.reCLM.analyticAt _).comp
    ((hc.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t))
  apply hre.congr
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  have hp (x : X) : 0 ≤ a x + s * b x := add_nonneg (ha0 x) (mul_nonneg hs.le (hb0 x))
  change (∫ x, ((a x : ℂ) + (s : ℂ) * (b x : ℂ)) ^ (c : ℂ) ∂nu).re =
    ∫ x, (a x + s * b x) ^ c ∂nu
  simp_rw [← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_cpow (hp _)]
  rw [integral_complex_ofReal, Complex.ofReal_re]

end ShadowVerification.CompressionAnalytic
#print axioms ShadowVerification.CompressionAnalytic.hasDerivAt_integral_complex
#print axioms ShadowVerification.CompressionAnalytic.isOpen_rightHalfPlane
#print axioms ShadowVerification.CompressionAnalytic.positive_combination_slitPlane
#print axioms ShadowVerification.CompressionAnalytic.analyticOnNhd_complex_integral
#print axioms ShadowVerification.CompressionAnalytic.analyticOnNhd_real_integral

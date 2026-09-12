import LeanShadow.CompressionJacobian

/-! # Uniform decay away from the compression axis

Outside any fixed tubular neighborhood of the axis, the actual normalized
Jacobian kernel is at most s^{-1} times a fixed constant. This gives the
far-region estimate in the density-point compression argument. It does not
estimate the shrinking neighborhood of the axis.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace ShadowVerification.CompressionTail
open Spherical Compression CompressionJacobian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem dilation_norm_sq (e : Sphere E) (x : E) (s : ℝ) :
    ‖dilation e s x‖ ^ 2 = ‖axisProjection e x‖ ^ 2 + s ^ 2 * ‖x - axisProjection e x‖ ^ 2 := by
  rw [dilation_apply, norm_add_sq_real, real_inner_smul_right, axisProjection_orthogonal,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem dilation_norm_lower (e : Sphere E) (x : E) (s : ℝ) :
    s * ‖x - axisProjection e x‖ ≤ ‖dilation e s x‖ := by
  have h := dilation_norm_sq e x s
  nlinarith [sq_nonneg ‖axisProjection e x‖, norm_nonneg (dilation e s x)]

variable [FiniteDimensional ℝ E] [Nontrivial E]

/-- The exact dimension-dependent bound used to discard the far region. -/
theorem kernel_le_away_axis (e x : Sphere E) (s r : ℝ) (hs : 0 < s) (hr : 0 < r)
    (hx : r ≤ ‖(x : E) - axisProjection e (x : E)‖) :
    kernel e s x ≤ s⁻¹ * r⁻¹ ^ Module.finrank ℝ E := by
  have hl : s * r ≤ ‖dilation e s (x : E)‖ :=
    (mul_le_mul_of_nonneg_left hx hs.le).trans (dilation_norm_lower e (x : E) s)
  have hi : ‖dilation e s (x : E)‖⁻¹ ≤ (s * r)⁻¹ := inv_anti₀ (mul_pos hs hr) hl
  have hp := pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) hi (Module.finrank ℝ E)
  have hn : 1 ≤ Module.finrank ℝ E := Module.finrank_pos
  calc
    kernel e s x ≤ s ^ (Module.finrank ℝ E - 1) * ((s * r)⁻¹ ^ Module.finrank ℝ E) :=
      mul_le_mul_of_nonneg_left hp (pow_nonneg hs.le _)
    _ = s⁻¹ * r⁻¹ ^ Module.finrank ℝ E := by
      rw [mul_inv, mul_pow, pow_sub₀ s hs.ne' hn, pow_one, inv_pow]
      field_simp

variable [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem kernel_continuous (e : Sphere E) (s : ℝ) (hs : 0 < s) : Continuous (kernel e s) := by
  have hn (x : Sphere E) : ‖dilation e s (x : E)‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    rw [← dilationEquiv_coe e s hs.ne']
    simpa only [ContinuousLinearEquiv.coe_coe, map_zero] using
      (dilationEquiv e s hs.ne').injective.ne (unit_ne_zero x)
  unfold kernel
  exact continuous_const.mul
    ((((dilation e s).continuous.comp continuous_subtype_val).norm.inv₀ hn).pow _)

theorem kernel_integrable (e : Sphere E) (s : ℝ) (hs : 0 < s) :
    Integrable (kernel e s) (probability mu) := by
  let : CompactSpace (Sphere E) := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E) 1)
  exact (kernel_continuous e s hs).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- All of the kernel mass in a region a fixed distance from the axis vanishes. -/
theorem tail_integral_tendsto_zero (e : Sphere E) (D : Set (Sphere E)) (hDm : MeasurableSet D)
    (r : ℝ) (hr : 0 < r)
    (hD : ∀ x ∈ D, r ≤ ‖(x : E) - axisProjection e (x : E)‖) :
    Tendsto (fun s => ∫ x in D, kernel e s x ∂probability mu) atTop (𝓝 0) := by
  have hb : ∀ᶠ s in atTop,
      (∫ x in D, kernel e s x ∂probability mu) ≤
        (probability mu).real D * (s⁻¹ * r⁻¹ ^ Module.finrank ℝ E) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    calc
      (∫ x in D, kernel e s x ∂probability mu) ≤
          ∫ _ in D, s⁻¹ * r⁻¹ ^ Module.finrank ℝ E ∂probability mu := by
        apply integral_mono_ae (kernel_integrable mu e s hs).integrableOn (integrable_const _)
        exact (ae_restrict_mem hDm).mono (fun x hx => kernel_le_away_axis e x s r hs hr (hD x hx))
      _ = _ := by simp [measureReal_def]
  have hz : ∀ᶠ s in atTop, 0 ≤ ∫ x in D, kernel e s x ∂probability mu := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact integral_nonneg (fun x => kernel_nonneg e s hs.le x)
  have ht : Tendsto (fun s : ℝ => (probability mu).real D * (s⁻¹ * r⁻¹ ^ Module.finrank ℝ E))
      atTop (𝓝 0) := by
    simpa using ((tendsto_inv_atTop_zero.mul_const (r⁻¹ ^ Module.finrank ℝ E)).const_mul
      ((probability mu).real D))
  exact squeeze_zero' hz hb ht

end ShadowVerification.CompressionTail
#print axioms ShadowVerification.CompressionTail.dilation_norm_sq
#print axioms ShadowVerification.CompressionTail.dilation_norm_lower
#print axioms ShadowVerification.CompressionTail.kernel_le_away_axis
#print axioms ShadowVerification.CompressionTail.kernel_continuous
#print axioms ShadowVerification.CompressionTail.kernel_integrable
#print axioms ShadowVerification.CompressionTail.tail_integral_tendsto_zero

import LeanShadow.LocalAreaConstancy
import LeanShadow.CompressionAnalytic

/-! # A concrete compression family for actual spherical sets

For a unit axis e, C_e(t) fixes e and dilates its orthogonal complement by
sqrt(t). Up to a positive scalar and a change of parameter, this is the
determinant-one family in the manuscript. We construct its inverse and prove
real analyticity of the actual transformed area, including for Borel sets
with irregular boundaries.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace ShadowVerification.Compression
open Spherical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def axisProjection (e : Sphere E) : E →L[ℝ] E :=
  (innerSL ℝ (e : E)).smulRight (e : E)

theorem axisProjection_apply (e : Sphere E) (x : E) :
    axisProjection e x = inner ℝ (e : E) x • (e : E) := rfl

theorem inner_axis_self (e : Sphere E) : inner ℝ (e : E) (e : E) = 1 := by
  rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp e.property, one_pow]

theorem axisProjection_idempotent (e : Sphere E) (x : E) :
    axisProjection e (axisProjection e x) = axisProjection e x := by
  simp only [axisProjection_apply, real_inner_smul_right, inner_axis_self, mul_one]

theorem axisProjection_orthogonal (e : Sphere E) (x : E) :
    inner ℝ (axisProjection e x) (x - axisProjection e x) = 0 := by
  simp only [axisProjection_apply, real_inner_smul_left, inner_sub_right,
    real_inner_smul_right, inner_axis_self, mul_one, sub_self]

noncomputable def dilation (e : Sphere E) (s : ℝ) : E →L[ℝ] E :=
  axisProjection e + s • (1 - axisProjection e)

theorem dilation_apply (e : Sphere E) (s : ℝ) (x : E) :
    dilation e s x = axisProjection e x + s • (x - axisProjection e x) := rfl

theorem projection_dilation (e : Sphere E) (s : ℝ) (x : E) :
    axisProjection e (dilation e s x) = axisProjection e x := by
  rw [dilation_apply, map_add, map_smul, map_sub, axisProjection_idempotent]
  simp

theorem dilation_comp (e : Sphere E) (s r : ℝ) (x : E) :
    dilation e s (dilation e r x) = dilation e (s * r) x := by
  rw [dilation_apply, projection_dilation, dilation_apply, dilation_apply]
  module

theorem dilation_one (e : Sphere E) : dilation e 1 = 1 := by
  ext x
  simp [dilation_apply]

noncomputable def dilationEquiv (e : Sphere E) (s : ℝ) (hs : s ≠ 0) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse (dilation e s) (dilation e s⁻¹)
    (fun x => by rw [dilation_comp, inv_mul_cancel₀ hs, dilation_one]; rfl)
    (fun x => by rw [dilation_comp, mul_inv_cancel₀ hs, dilation_one]; rfl)

theorem dilationEquiv_coe (e : Sphere E) (s : ℝ) (hs : s ≠ 0) :
    (dilationEquiv e s hs : E →L[ℝ] E) = dilation e s := rfl

noncomputable def compressionOperator (e : Sphere E) (t : ℝ) : E →L[ℝ] E :=
  dilation e (Real.sqrt t)

noncomputable def compressionEquiv (e : Sphere E) (t : ℝ) (ht : 0 < t) : E ≃L[ℝ] E :=
  dilationEquiv e (Real.sqrt t) (Real.sqrt_pos.mpr ht).ne'

theorem compressionEquiv_coe (e : Sphere E) (t : ℝ) (ht : 0 < t) :
    (compressionEquiv e t ht : E →L[ℝ] E) = compressionOperator e t := rfl

theorem compressionOperator_one (e : Sphere E) : compressionOperator e 1 = 1 := by
  simp only [compressionOperator, Real.sqrt_one, dilation_one]

theorem compressionOperator_continuous (e : Sphere E) : Continuous (compressionOperator e) := by
  unfold compressionOperator dilation
  fun_prop

/-- The squared norm has a positive affine dependence on the new parameter. -/
theorem compression_norm_sq (e : Sphere E) (x : E) (t : ℝ) (ht : 0 ≤ t) :
    ‖compressionOperator e t x‖ ^ 2 =
      ‖axisProjection e x‖ ^ 2 + t * ‖x - axisProjection e x‖ ^ 2 := by
  rw [compressionOperator, dilation_apply, norm_add_sq_real,
    real_inner_smul_right, axisProjection_orthogonal, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t), mul_pow, Real.sq_sqrt ht]
  ring

theorem projection_sq_sum (e x : Sphere E) :
    ‖axisProjection e (x : E)‖ ^ 2 + ‖(x : E) - axisProjection e (x : E)‖ ^ 2 = 1 := by
  have h := compression_norm_sq e (x : E) 1 zero_le_one
  rw [compressionOperator_one, one_apply_eq_self,
    mem_sphere_zero_iff_norm.mp x.property, one_pow, one_mul] at h
  exact h.symm

/-- A real power representation of the actual inverse-norm Jacobian factor. -/
theorem compression_density (e x : Sphere E) (N : ℕ) (t : ℝ) (ht : 0 < t) :
    ‖compressionOperator e t (x : E)‖⁻¹ ^ N =
      (‖axisProjection e (x : E)‖ ^ 2 + t * ‖(x : E) - axisProjection e (x : E)‖ ^ 2)
        ^ (-(N : ℝ) / 2) := by
  rw [← compression_norm_sq e (x : E) t ht.le]
  calc
    _ = ‖compressionOperator e t (x : E)‖ ^ (-(N : ℝ)) := by
      rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, inv_pow]
    _ = (‖compressionOperator e t (x : E)‖ ^ 2) ^ (-(N : ℝ) / 2) := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (norm_nonneg _)]
      congr 1
      push_cast
      ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Analyticity is established for the actual density integral of any finite
spherical measure, so it applies to arbitrary measurable restrictions. -/
theorem analytic_compression_integral (nu : Measure (Sphere E)) [IsFiniteMeasure nu]
    (e : Sphere E) (N : ℕ) :
    AnalyticOnNhd ℝ
      (fun t => Regularity.operatorDensityIntegral nu N (compressionOperator e t)) (Ioi 0) := by
  let : CompactSpace (Sphere E) := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E) 1)
  have ha : Continuous (fun x : Sphere E => ‖axisProjection e (x : E)‖ ^ 2) := by fun_prop
  have hb : Continuous (fun x : Sphere E => ‖(x : E) - axisProjection e (x : E)‖ ^ 2) := by fun_prop
  have h := CompressionAnalytic.analyticOnNhd_real_integral nu _ _ ha hb
    (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
    (fun x => by rw [projection_sq_sum]; exact zero_lt_one) (-(N : ℝ) / 2)
  intro t ht
  apply (h t ht).congr
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => (compression_density e x N s hs).symm)

variable [Nontrivial E] (mu : Measure E) [mu.IsAddHaarMeasure]

noncomputable def compressionArea (A : Set (Sphere E)) (e : Sphere E) (t : ℝ) : ℝ :=
  Regularity.areaExtension mu A (compressionOperator e t)

theorem compressionArea_eq_transformedArea (A : Set (Sphere E)) (hA : MeasurableSet A)
    (e : Sphere E) (t : ℝ) (ht : 0 < t) :
    compressionArea mu A e t = transformedArea mu A (compressionEquiv e t ht) := by
  exact (Regularity.transformedArea_eq_extension mu A hA (compressionEquiv e t ht)).symm

/-- This is analyticity of actual transformed measure, not only of the path. -/
theorem analytic_compressionArea (A : Set (Sphere E)) (e : Sphere E) :
    AnalyticOnNhd ℝ (compressionArea mu A e) (Ioi 0) := by
  intro t ht
  exact (analytic_compression_integral ((probability mu).restrict A) e (Module.finrank ℝ E) t ht).div
    (analytic_compression_integral (probability mu) e (Module.finrank ℝ E) t ht)
    (Regularity.whole_operator_integral_ne_zero mu (compressionEquiv e t ht))

end ShadowVerification.Compression
#print axioms ShadowVerification.Compression.axisProjection_apply
#print axioms ShadowVerification.Compression.inner_axis_self
#print axioms ShadowVerification.Compression.axisProjection_idempotent
#print axioms ShadowVerification.Compression.axisProjection_orthogonal
#print axioms ShadowVerification.Compression.dilation_apply
#print axioms ShadowVerification.Compression.projection_dilation
#print axioms ShadowVerification.Compression.dilation_comp
#print axioms ShadowVerification.Compression.dilation_one
#print axioms ShadowVerification.Compression.dilationEquiv_coe
#print axioms ShadowVerification.Compression.compressionEquiv_coe
#print axioms ShadowVerification.Compression.compressionOperator_one
#print axioms ShadowVerification.Compression.compressionOperator_continuous
#print axioms ShadowVerification.Compression.compression_norm_sq
#print axioms ShadowVerification.Compression.projection_sq_sum
#print axioms ShadowVerification.Compression.compression_density
#print axioms ShadowVerification.Compression.analytic_compression_integral
#print axioms ShadowVerification.Compression.compressionArea_eq_transformedArea
#print axioms ShadowVerification.Compression.analytic_compressionArea

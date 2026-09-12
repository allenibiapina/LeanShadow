import LeanShadow.ProjectiveCompression

/-! # The normalization of the actual compression kernel

The dilation is an exponential of the orthogonal-complement projection.
Its determinant is derived from the already proved exponential determinant
formula. The spherical change-of-variables theorem then gives a normalized
nonnegative kernel for its actual image area.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace ShadowVerification.CompressionJacobian
open Compression Spherical Projective

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem axisProjection_symmetric (e : Sphere E) :
    (axisProjection e : E →ₗ[ℝ] E).IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe, axisProjection_apply,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm (e : E) x]
  ring

theorem complementProjection_symmetric (e : Sphere E) :
    ((1 - axisProjection e : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric :=
  LinearMap.IsSymmetric.one.sub (axisProjection_symmetric e)

variable [FiniteDimensional ℝ E]

theorem axisProjection_trace (e : Sphere E) :
    LinearMap.trace ℝ E (axisProjection e : E →ₗ[ℝ] E) = 1 := by
  change LinearMap.trace ℝ E ((innerSL ℝ (e : E)).toLinearMap.smulRight (e : E)) = 1
  rw [LinearMap.trace_smulRight]
  exact inner_axis_self e

theorem complementProjection_trace (e : Sphere E) :
    LinearMap.trace ℝ E ((1 - axisProjection e : E →L[ℝ] E) : E →ₗ[ℝ] E) =
      (Module.finrank ℝ E : ℝ) - 1 := by
  change LinearMap.trace ℝ E (1 - (axisProjection e : E →ₗ[ℝ] E)) = _
  rw [map_sub, axisProjection_trace, LinearMap.trace_one]

/-- Decomposing each vector into its axial and orthogonal parts identifies
the actual exponential map with the dilation. -/
theorem flow_complementProjection (e : Sphere E) (u : ℝ) :
    (flowEquiv (1 - axisProjection e) u : E →L[ℝ] E) = dilation e (Real.exp u) := by
  ext x
  have hax : (1 - axisProjection e) (axisProjection e x) = (0 : ℝ) • axisProjection e x := by
    simp [axisProjection_idempotent]
  have hperp : (1 - axisProjection e) (x - axisProjection e x) =
      (1 : ℝ) • (x - axisProjection e x) := by
    simp [map_sub, axisProjection_idempotent]
  have hx : x = axisProjection e x + (x - axisProjection e x) := by module
  calc
    flowEquiv (1 - axisProjection e) u x =
        flowEquiv (1 - axisProjection e) u (axisProjection e x) +
          flowEquiv (1 - axisProjection e) u (x - axisProjection e x) := by rw [← map_add, ← hx]
    _ = dilation e (Real.exp u) x := by
      rw [flowEquiv_apply, flowEquiv_apply, flow_apply_eigenvector _ _ _ _ hax,
        flow_apply_eigenvector _ _ _ _ hperp]
      simp [dilation_apply]

/-- The determinant of a compression about an arbitrary unit axis. -/
theorem dilation_determinant (e : Sphere E) (s : ℝ) (hs : 0 < s) :
    LinearMap.det (dilationEquiv e s hs.ne' : E →ₗ[ℝ] E) =
      Real.exp (Real.log s * ((Module.finrank ℝ E : ℝ) - 1)) := by
  have heq : (dilationEquiv e s hs.ne' : E →ₗ[ℝ] E) =
      (flowEquiv (1 - axisProjection e) (Real.log s) : E →ₗ[ℝ] E) := by
    have h := flow_complementProjection e (Real.log s)
    rw [Real.exp_log hs] at h
    exact congrArg ContinuousLinearMap.toLinearMap h.symm
  rw [heq, flow_determinant _ (complementProjection_symmetric e), complementProjection_trace]

variable [Nontrivial E]

theorem dilation_determinant_pow (e : Sphere E) (s : ℝ) (hs : 0 < s) :
    LinearMap.det (dilationEquiv e s hs.ne' : E →ₗ[ℝ] E) = s ^ (Module.finrank ℝ E - 1) := by
  rw [dilation_determinant e s hs]
  have hn : 1 ≤ Module.finrank ℝ E := Module.finrank_pos
  have hcast : (Module.finrank ℝ E : ℝ) - 1 = ((Module.finrank ℝ E - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  rw [hcast, ← Real.rpow_def_of_pos hs, Real.rpow_natCast]

variable [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]

noncomputable def kernel (e : Sphere E) (s : ℝ) (x : Sphere E) : ℝ :=
  s ^ (Module.finrank ℝ E - 1) * ‖dilation e s (x : E)‖⁻¹ ^ Module.finrank ℝ E

/-- Actual image area equals integration against the concrete compression kernel. -/
theorem transformedArea_kernel (A : Set (Sphere E)) (hA : MeasurableSet A)
    (e : Sphere E) (s : ℝ) (hs : 0 < s) :
    transformedArea mu A (dilationEquiv e s hs.ne') = ∫ x in A, kernel e s x ∂probability mu := by
  rw [Radial.transformedArea_integral mu _ A hA, dilation_determinant_pow e s hs,
    abs_of_pos (pow_pos hs _)]
  exact (integral_const_mul _ _).symm

theorem kernel_integral_one (e : Sphere E) (s : ℝ) (hs : 0 < s) :
    ∫ x, kernel e s x ∂probability mu = 1 := by
  have h := transformedArea_kernel mu univ MeasurableSet.univ e s hs
  simpa only [transformedArea_univ, setIntegral_univ] using h.symm

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
theorem kernel_nonneg (e : Sphere E) (s : ℝ) (hs : 0 ≤ s) (x : Sphere E) :
    0 ≤ kernel e s x := by unfold kernel; positivity

end ShadowVerification.CompressionJacobian
#print axioms ShadowVerification.CompressionJacobian.axisProjection_symmetric
#print axioms ShadowVerification.CompressionJacobian.complementProjection_symmetric
#print axioms ShadowVerification.CompressionJacobian.axisProjection_trace
#print axioms ShadowVerification.CompressionJacobian.complementProjection_trace
#print axioms ShadowVerification.CompressionJacobian.flow_complementProjection
#print axioms ShadowVerification.CompressionJacobian.dilation_determinant
#print axioms ShadowVerification.CompressionJacobian.dilation_determinant_pow
#print axioms ShadowVerification.CompressionJacobian.transformedArea_kernel
#print axioms ShadowVerification.CompressionJacobian.kernel_integral_one
#print axioms ShadowVerification.CompressionJacobian.kernel_nonneg

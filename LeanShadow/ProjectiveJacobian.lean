import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-! # Actual exponential-flow derivatives of the projective density

This module computes derivatives of the inverse norm power along the actual
operator exponential. Its identification with the change of spherical
measure is proved separately in `RadialChange` and `ProjectiveArea`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace ShadowVerification.Projective

/-- A second derivative chain rule at a point where the positive base is one. -/
theorem rpow_second_deriv_at_one (q dq : ℝ → ℝ) (c p : ℝ)
    (hq : ∀ t, HasDerivAt q (dq t) t) (hq0 : q 0 = 1)
    (hdq : HasDerivAt dq c 0) :
    deriv (deriv (fun t => (q t) ^ p)) 0 =
      p * (p - 1) * (dq 0) ^ 2 + p * c := by
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ), q t ≠ 0 :=
    (hq 0).continuousAt.eventually_ne (by simpa only [hq0] using one_ne_zero)
  have heq : deriv (fun t => (q t) ^ p) =ᶠ[𝓝 0]
      fun t => dq t * p * (q t) ^ (p - 1) := by
    filter_upwards [hne] with t ht
    exact ((hq t).rpow_const (Or.inl ht)).deriv
  rw [heq.deriv_eq]
  have hd := (hdq.mul_const p).mul
    ((hq 0).rpow_const (p := p - 1) (Or.inl (by simpa only [hq0] using one_ne_zero)))
  have hd' : deriv (fun t => dq t * p * q t ^ (p - 1)) 0 =
      c * p * q 0 ^ (p - 1) + dq 0 * p * (dq 0 * (p - 1) * q 0 ^ (p - 1 - 1)) := hd.deriv
  rw [hd']
  simp only [hq0, Real.one_rpow]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def flow (H : E →L[ℝ] E) (x : E) (t : ℝ) : E :=
  (NormedSpace.exp (t • H)) x

omit [CompleteSpace E] in
theorem flow_zero (H : E →L[ℝ] E) (x : E) : flow H x 0 = x := by
  simp [flow]

theorem flow_hasDeriv (H : E →L[ℝ] E) (x : E) (t : ℝ) :
    HasDerivAt (flow H x) (flow H (H x) t) t := by
  unfold flow
  simpa only [mul_apply_eq_comp, map_zero, add_zero] using!
    (hasDerivAt_exp_smul_const H t).clm_apply (hasDerivAt_const t x)

noncomputable def flowNormSq (H : E →L[ℝ] E) (x : E) (t : ℝ) : ℝ :=
  inner ℝ (flow H x t) (flow H x t)

noncomputable def flowNormSqD (H : E →L[ℝ] E) (x : E) (t : ℝ) : ℝ :=
  2 * inner ℝ (flow H x t) (flow H (H x) t)

theorem flowNormSq_hasDeriv (H : E →L[ℝ] E) (x : E) (t : ℝ) :
    HasDerivAt (flowNormSq H x) (flowNormSqD H x t) t := by
  have h := (flow_hasDeriv H x t).inner ℝ (flow_hasDeriv H x t)
  unfold flowNormSq flowNormSqD
  simpa only [
    real_inner_comm (flow H (H x) t) (flow H x t), two_mul] using! h

theorem flowNormSqD_hasDeriv_zero (H : E →L[ℝ] E) (x : E)
    (hH : ∀ u v : E, inner ℝ (H u) v = inner ℝ u (H v)) :
    HasDerivAt (flowNormSqD H x) (4 * inner ℝ x (H (H x))) 0 := by
  have h := ((flow_hasDeriv H x 0).inner ℝ (flow_hasDeriv H (H x) 0)).const_mul 2
  have heq : 2 * (inner ℝ (flow H x 0) (flow H (H (H x)) 0) +
      inner ℝ (flow H (H x) 0) (flow H (H x) 0)) = 4 * inner ℝ x (H (H x)) := by
    simp only [flow_zero, hH x (H x)]
    ring
  rw [heq] at h
  exact h

/-- The inverse norm power that occurs as the determinant-one projective
Jacobian. The measure change formula is not part of this definition. -/
noncomputable def flowDensity (N : ℝ) (H : E →L[ℝ] E) (x : E) (t : ℝ) : ℝ :=
  (flowNormSq H x t) ^ (-N / 2)

omit [CompleteSpace E] in
theorem flowDensity_zero (N : ℝ) (H : E →L[ℝ] E) (x : E) (hx : ‖x‖ = 1) :
    flowDensity N H x 0 = 1 := by
  simp [flowDensity, flowNormSq, flow_zero, hx]

theorem flowDensity_hasDeriv_zero (N : ℝ) (H : E →L[ℝ] E) (x : E)
    (hx : ‖x‖ = 1) :
    HasDerivAt (flowDensity N H x) (-N * inner ℝ x (H x)) 0 := by
  have h0 : flowNormSq H x 0 = 1 := by
    simp [flowNormSq, flow_zero, hx]
  have h := (flowNormSq_hasDeriv H x 0).rpow_const
    (p := -N / 2) (Or.inl (by rw [h0]; norm_num))
  convert h using 1
  · rfl
  · simp only [h0, Real.one_rpow, flowNormSqD, flow_zero]
    ring

/-- The exact second derivative from the manuscript, for any real exponent
parameter and every self-adjoint continuous linear operator. -/
theorem flowDensity_second_deriv_zero (N : ℝ) (H : E →L[ℝ] E) (x : E)
    (hx : ‖x‖ = 1)
    (hH : ∀ u v : E, inner ℝ (H u) v = inner ℝ u (H v)) :
    deriv (deriv (flowDensity N H x)) 0 =
      N * (N + 2) * (inner ℝ x (H x)) ^ 2 - 2 * N * inner ℝ x (H (H x)) := by
  unfold flowDensity
  rw [rpow_second_deriv_at_one (flowNormSq H x) (flowNormSqD H x)
    (4 * inner ℝ x (H (H x))) (-N / 2)
    (flowNormSq_hasDeriv H x)
    (by simp [flowNormSq, flow_zero, hx])
    (flowNormSqD_hasDeriv_zero H x hH)]
  simp only [flowNormSqD, flow_zero]
  ring

omit [CompleteSpace E] in
/-- Agreement between the real-power expression differentiated above and the
integer inverse norm power in the spherical measure-change formula. -/
theorem flowDensity_eq_inverse_norm_power (N : ℕ) (H : E →L[ℝ] E) (x : E) (t : ℝ) :
    flowDensity (N : ℝ) H x t = ‖flow H x t‖⁻¹ ^ N := by
  unfold flowDensity flowNormSq
  rw [real_inner_self_eq_norm_sq,
    ← Real.rpow_natCast_mul (norm_nonneg _) 2]
  have heq : (2 : ℝ) * (-(N : ℝ) / 2) = -(N : ℝ) := by ring
  rw [Nat.cast_ofNat, heq, Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]

theorem flow_operator_isUnit (H : E →L[ℝ] E) (t : ℝ) :
    IsUnit (NormedSpace.exp (t • H)) := by
  apply NormedSpace.isUnit_exp_of_mem_ball (𝕂 := ℝ)
  rw [NormedSpace.expSeries_radius_eq_top]
  exact edist_lt_top _ _

/-- The invertible continuous linear map underlying the actual exponential
flow. Invertibility comes from the Banach-algebra exponential theorem. -/
noncomputable def flowEquiv (H : E →L[ℝ] E) (t : ℝ) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofUnit (flow_operator_isUnit H t).unit

theorem flowEquiv_apply (H : E →L[ℝ] E) (t : ℝ) (x : E) :
    flowEquiv H t x = flow H x t := by
  change ((flow_operator_isUnit H t).unit : E →L[ℝ] E) x = _
  rw [(flow_operator_isUnit H t).unit_spec]
  rfl


end ShadowVerification.Projective
#print axioms ShadowVerification.Projective.rpow_second_deriv_at_one
#print axioms ShadowVerification.Projective.flow_zero
#print axioms ShadowVerification.Projective.flow_hasDeriv
#print axioms ShadowVerification.Projective.flowNormSq_hasDeriv
#print axioms ShadowVerification.Projective.flowNormSqD_hasDeriv_zero
#print axioms ShadowVerification.Projective.flowDensity_zero
#print axioms ShadowVerification.Projective.flowDensity_hasDeriv_zero
#print axioms ShadowVerification.Projective.flowDensity_second_deriv_zero

#print axioms ShadowVerification.Projective.flowDensity_eq_inverse_norm_power
#print axioms ShadowVerification.Projective.flowEquiv_apply

#print axioms ShadowVerification.Projective.flow_operator_isUnit

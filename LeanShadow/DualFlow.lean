import LeanShadow.DualAreaRegularity
import LeanShadow.ProjectiveComposition

/-! # The actual inverse-adjoint exponential flow

The paired flow is derived from the inverse-adjoint construction. The order
of composition and the negative adjoint generator are conclusions. In the
symmetric directions this is exactly the opposite generator in the paper.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Topology
namespace ShadowVerification.DualFlow
open _root_.ShadowVerification.Dual _root_.ShadowVerification.Composition
open Projective Spherical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The inner-product identity determines the dual transformation uniquely. -/
theorem dual_unique (T U : E ≃L[ℝ] E)
    (h : ∀ x y : E, inner ℝ (T x) (U y) = inner ℝ x y) : U = dualEquiv T := by
  ext y
  apply ext_inner_left ℝ
  intro z
  obtain ⟨x, rfl⟩ := T.surjective z
  rw [h, dual_inner]

/-- Inverse adjoints respect the order of composition used by `trans`. -/
theorem dual_trans (T U : E ≃L[ℝ] E) :
    dualEquiv (T.trans U) = (dualEquiv T).trans (dualEquiv U) := by
  symm
  apply dual_unique
  intro x y
  change inner ℝ (U (T x)) (dualEquiv U (dualEquiv T y)) = _
  rw [dual_inner, dual_inner]

/-- The exponential inverse identity over the actual real operator algebra. -/
theorem exp_mul_neg (H : E →L[ℝ] E) :
    NormedSpace.exp H * NormedSpace.exp (-H) = 1 := by
  have hh := NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
    (Commute.refl H).neg_right
    (by rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _)
    (by rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _)
  simpa using hh.symm

/-- The negative adjoint exponential is the actual avoiding-side flow. -/
theorem dual_flow (H : E →L[ℝ] E) (t : ℝ) :
    dualEquiv (flowEquiv H t) = flowEquiv (-star H) t := by
  symm
  apply dual_unique
  intro x y
  simp only [flowEquiv_apply, flow]
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ x ((star (NormedSpace.exp (t • H)) *
    NormedSpace.exp (t • (-star H))) y) = inner ℝ x y
  rw [NormedSpace.star_exp, star_smul, star_trivial, smul_neg, exp_mul_neg]
  simp

/-- Symmetric flows have precisely the opposite dual generator. -/
theorem dual_flow_symmetric (H : E →L[ℝ] E)
    (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (t : ℝ) :
    dualEquiv (flowEquiv H t) = flowEquiv (-H) t := by
  rw [dual_flow]
  have hstar : star H = H := hH.isSelfAdjoint
  rw [hstar]

/-- The flow identity holds through every invertible base transformation. -/
theorem dual_trans_flow (T : E ≃L[ℝ] E) (H : E →L[ℝ] E) (t : ℝ) :
    dualEquiv (T.trans (flowEquiv H t)) = (dualEquiv T).trans (flowEquiv (-star H) t) := by
  rw [dual_trans, dual_flow]

/-- A skew-adjoint flow preserves the actual inner product. -/
theorem skew_flow_inner (H : E →L[ℝ] E) (hH : star H = -H) (t : ℝ) (x y : E) :
    inner ℝ (flowEquiv H t x) (flowEquiv H t y) = inner ℝ x y := by
  have h := dual_inner (flowEquiv H t) x y
  rwa [dual_flow, hH, neg_neg] at h

/-- In particular, skew-adjoint flows preserve vector norms. -/
theorem skew_flow_norm (H : E →L[ℝ] E) (hH : star H = -H) (t : ℝ) (x : E) :
    ‖flowEquiv H t x‖ = ‖x‖ := by
  have h := skew_flow_inner H hH t x x
  simp only [real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

variable [MeasurableSpace E] (mu : Measure E)

/-- Equality of actual image areas along the whole dual path. -/
theorem dual_area_flow (B : Set (Sphere E)) (T : E ≃L[ℝ] E)
    (H : E →L[ℝ] E) (t : ℝ) :
    transformedArea mu B (dualEquiv (T.trans (flowEquiv H t))) =
      transformedArea mu (action (dualEquiv T) '' B) (flowEquiv (-star H) t) := by
  rw [dual_trans_flow, transformedArea_trans]

theorem dual_area_flow_symmetric (B : Set (Sphere E)) (T : E ≃L[ℝ] E)
    (H : E →L[ℝ] E) (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (t : ℝ) :
    transformedArea mu B (dualEquiv (T.trans (flowEquiv H t))) =
      transformedArea mu (action (dualEquiv T) '' B) (flowEquiv (-H) t) := by
  rw [dual_trans, dual_flow_symmetric H hH, transformedArea_trans]

end ShadowVerification.DualFlow
#print axioms ShadowVerification.DualFlow.dual_unique
#print axioms ShadowVerification.DualFlow.dual_trans
#print axioms ShadowVerification.DualFlow.dual_flow
#print axioms ShadowVerification.DualFlow.dual_flow_symmetric
#print axioms ShadowVerification.DualFlow.dual_trans_flow
#print axioms ShadowVerification.DualFlow.dual_area_flow
#print axioms ShadowVerification.DualFlow.dual_area_flow_symmetric

#print axioms ShadowVerification.DualFlow.exp_mul_neg
#print axioms ShadowVerification.DualFlow.skew_flow_inner
#print axioms ShadowVerification.DualFlow.skew_flow_norm

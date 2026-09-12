import LeanShadow.JointAreaRegularity
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # The actual inverse-adjoint transformation and its area regularity

For a real inner-product space the inverse-adjoint is the coordinate-free
inverse transpose. We construct it as an invertible continuous linear map,
prove the inner-product identity that preserves orthogonality, and prove
joint C² regularity of the corresponding image-area function. No duality or
regularity identity is postulated as a premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Topology

namespace ShadowVerification.Dual
open Spherical Regularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def dualEquiv (T : E ≃L[ℝ] E) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofUnit (star T.symm.toUnit)

noncomputable def dualMap (L : E →L[ℝ] E) : E →L[ℝ] E :=
  star (ContinuousLinearMap.inverse L)

theorem dualEquiv_to_operator (T : E ≃L[ℝ] E) :
    (dualEquiv T : E →L[ℝ] E) = ContinuousLinearMap.adjoint (T.symm : E →L[ℝ] E) := rfl

theorem dualMap_equiv (T : E ≃L[ℝ] E) :
    dualMap (T : E →L[ℝ] E) = (dualEquiv T : E →L[ℝ] E) := by
  unfold dualMap
  rw [ContinuousLinearMap.inverse_equiv]
  rfl

/-- The defining inverse-transpose relation holds on actual vectors. -/
theorem dual_inner (T : E ≃L[ℝ] E) (x y : E) :
    inner ℝ (T x) (dualEquiv T y) = inner ℝ x y := by
  change inner ℝ (T x) ((dualEquiv T : E →L[ℝ] E) y) = _
  rw [dualEquiv_to_operator, ContinuousLinearMap.adjoint_inner_right]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

/-- The inverse-adjoint map is C^k near every invertible operator. -/
theorem contDiffAt_dualMap (k : ℕ) (T : E ≃L[ℝ] E) :
    ContDiffAt ℝ k (dualMap (E := E)) (T : E →L[ℝ] E) := by
  exact (starL' ℝ : (E →L[ℝ] E) ≃L[ℝ] (E →L[ℝ] E)).contDiff.contDiffAt.comp
    (T : E →L[ℝ] E) (contDiffAt_map_inverse T)

/-- A concrete avoiding pair remains avoiding under the paired transformations. -/
theorem avoids_dual_images (T : E ≃L[ℝ] E) (A B : Set (Sphere E)) (hAB : Avoids A B) :
    Avoids (action T '' A) (action (dualEquiv T) '' B) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  intro hzero
  exact hAB x hx y hy ((action_orthogonal_iff T (dualEquiv T) (dual_inner T) x y).mp hzero)

theorem shadow_covariance_dual (T : E ≃L[ℝ] E) (A : Set (Sphere E)) :
    shadow (action T '' A) = action (dualEquiv T) '' shadow A :=
  shadow_covariance T (dualEquiv T) (dual_inner T) A

variable [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

noncomputable def dualAreaExtension (B : Set (Sphere E)) (L : E →L[ℝ] E) : ℝ :=
  areaExtension mu B (dualMap L)

theorem transformedDualArea_eq_extension (B : Set (Sphere E)) (hB : MeasurableSet B)
    (T : E ≃L[ℝ] E) :
    transformedArea mu B (dualEquiv T) = dualAreaExtension mu B (T : E →L[ℝ] E) := by
  rw [transformedArea_eq_extension mu B hB]
  unfold dualAreaExtension
  rw [dualMap_equiv]

/-- The actual avoiding-side area has joint C² regularity in the primal operator. -/
theorem contDiffAt_dualAreaExtension (B : Set (Sphere E)) (T : E ≃L[ℝ] E) :
    ContDiffAt ℝ 2 (dualAreaExtension mu B) (T : E →L[ℝ] E) := by
  have hu : ContDiffAt ℝ 2 (areaExtension mu B) (dualMap (T : E →L[ℝ] E)) := by
    rw [dualMap_equiv]
    exact contDiffAt_areaExtension mu B (dualEquiv T)
  exact hu.comp (T : E →L[ℝ] E) (contDiffAt_dualMap 2 T)

end ShadowVerification.Dual

#print axioms ShadowVerification.Dual.dualEquiv_to_operator
#print axioms ShadowVerification.Dual.dualMap_equiv
#print axioms ShadowVerification.Dual.dual_inner
#print axioms ShadowVerification.Dual.contDiffAt_dualMap
#print axioms ShadowVerification.Dual.avoids_dual_images
#print axioms ShadowVerification.Dual.shadow_covariance_dual
#print axioms ShadowVerification.Dual.transformedDualArea_eq_extension
#print axioms ShadowVerification.Dual.contDiffAt_dualAreaExtension

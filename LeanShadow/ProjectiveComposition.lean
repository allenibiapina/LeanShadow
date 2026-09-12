import LeanShadow.AreaHarmonicity

/-! # Projective composition and harmonicity at every base transformation

Normalizing twice has the same effect as normalizing once after composition.
Consequently an exponential variation through a transformed set is exactly
an exponential variation based at that transformation. This transports the
vanishing sum of area second variations to every invertible linear map.

The conclusion is an identity of one-variable derivatives. Joint smoothness
and ellipticity of the associated operator remain separate obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped BigOperators

namespace ShadowVerification.Composition
open Spherical Projective Coordinates Integrated
open _root_.ShadowVerification.Frame

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Composition is in the order prescribed by `ContinuousLinearEquiv.trans`. -/
theorem action_trans (T U : E ≃L[ℝ] E) (x : Sphere E) :
    action (T.trans U) x = action U (action T x) := by
  apply Subtype.ext
  change NormedSpace.normalize (U (T x)) =
    NormedSpace.normalize (U (‖T x‖⁻¹ • T x))
  rw [map_smul, NormedSpace.normalize_smul_of_pos (by
    apply inv_pos.mpr
    exact norm_pos_iff.mpr (by simpa only [map_zero] using T.injective.ne (unit_ne_zero x)))]

theorem action_trans_image (T U : E ≃L[ℝ] E) (A : Set (Sphere E)) :
    action (T.trans U) '' A = action U '' (action T '' A) := by
  rw [image_image]
  congr 1
  funext x
  exact action_trans T U x

variable [MeasurableSpace E] (mu : Measure E)

/-- This is equality of actual image measures, without a regularity hypothesis on `A`. -/
theorem transformedArea_trans (T U : E ≃L[ℝ] E) (A : Set (Sphere E)) :
    transformedArea mu A (T.trans U) = transformedArea mu (action T '' A) U := by
  unfold transformedArea
  rw [action_trans_image]

end ShadowVerification.Composition

namespace ShadowVerification.Composition
open Spherical Projective Coordinates Integrated Harmonicity
open _root_.ShadowVerification.Frame

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]

/-- The symmetric harmonicity identity holds through every actual invertible
base transformation, not only at the identity. -/
theorem sum_second_deriv_at_transformation
    (A : Set (UnitSphere n)) (hA : MeasurableSet A)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) :
    (∑ i : FrobeniusIndex n,
      deriv (deriv (fun t => transformedArea mu A
        (T.trans (flowEquiv (operator (frame (frobeniusBasis (n := n)) i)) t)))) 0) = 0 := by
  simp_rw [transformedArea_trans]
  exact canonical_sum_second_deriv_eq_zero mu (action T '' A) (measurable_action_image T A hA)

end ShadowVerification.Composition

#print axioms ShadowVerification.Composition.action_trans
#print axioms ShadowVerification.Composition.action_trans_image
#print axioms ShadowVerification.Composition.transformedArea_trans
#print axioms ShadowVerification.Composition.sum_second_deriv_at_transformation

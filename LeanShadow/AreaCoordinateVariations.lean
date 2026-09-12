import LeanShadow.JointAreaRegularity
import LeanShadow.CurveCalculus
import LeanShadow.ProjectiveComposition

/-! # Actual area variations in the ambient operator coordinates

The joint C² extension constructed in `JointAreaRegularity` is evaluated on
the actual curve `exp(t H) T`. Its first two derivatives are computed using
the chain rule already checked in `CurveCalculus`. The resulting Hessian
and drift identities are about actual image measures, with regularity now
proved rather than assumed. The symmetric harmonicity sum is consequently
an identity in these ambient coordinates at every invertible base point.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Topology BigOperators

namespace ShadowVerification.AreaCoordinates
open Spherical Projective Regularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def operatorPath (H L : E →L[ℝ] E) (t : ℝ) : E →L[ℝ] E :=
  NormedSpace.exp (t • H) * L

omit [FiniteDimensional ℝ E] in
theorem operatorPath_zero (H L : E →L[ℝ] E) : operatorPath H L 0 = L := by
  simp [operatorPath]

/-- The derivative is computed in the normed space of all operators. -/
theorem operatorPath_hasDeriv (H L : E →L[ℝ] E) (t : ℝ) :
    HasDerivAt (operatorPath H L) (operatorPath H (H * L) t) t := by
  simpa only [operatorPath, mul_assoc] using!
    (hasDerivAt_exp_smul_const H t).mul_const L

/-- The operator path has exactly the order of composition of the geometric flow. -/
theorem trans_flow_to_operator (H : E →L[ℝ] E) (T : E ≃L[ℝ] E) (t : ℝ) :
    ((T.trans (flowEquiv H t)) : E →L[ℝ] E) = operatorPath H (T : E →L[ℝ] E) t := by
  ext x
  change flowEquiv H t (T x) = NormedSpace.exp (t • H) (T x)
  exact flowEquiv_apply H t (T x)

variable [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

/-- Equality holds along the entire curve, so it may be differentiated twice. -/
theorem area_path_eq_extension (A : Set (Sphere E)) (hA : MeasurableSet A)
    (H : E →L[ℝ] E) (T : E ≃L[ℝ] E) (t : ℝ) :
    transformedArea mu A (T.trans (flowEquiv H t)) =
      areaExtension mu A (operatorPath H (T : E →L[ℝ] E) t) := by
  rw [transformedArea_eq_extension mu A hA, trans_flow_to_operator]

/-- The first variation of actual image area is its coordinate derivative. -/
theorem first_area_in_coordinates (A : Set (Sphere E)) (hA : MeasurableSet A)
    (H : E →L[ℝ] E) (T : E ≃L[ℝ] E) :
    HasDerivAt (fun t => transformedArea mu A (T.trans (flowEquiv H t)))
      (fderiv ℝ (areaExtension mu A) (T : E →L[ℝ] E) (H * (T : E →L[ℝ] E))) 0 := by
  simp_rw [area_path_eq_extension mu A hA H T]
  have hd := (contDiffAt_areaExtension mu A T).differentiableAt (by norm_num)
  simpa only [Function.comp_def, operatorPath_zero] using!
    hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (operatorPath_hasDeriv H (T : E →L[ℝ] E) 0)
      (operatorPath_zero H (T : E →L[ℝ] E)).symm

/-- The Hessian term and the acceleration term for the actual area function. -/
theorem second_area_in_coordinates (A : Set (Sphere E)) (hA : MeasurableSet A)
    (H : E →L[ℝ] E) (T : E ≃L[ℝ] E) :
    deriv (deriv (fun t => transformedArea mu A (T.trans (flowEquiv H t)))) 0 =
      (fderiv ℝ (fderiv ℝ (areaExtension mu A)) (T : E →L[ℝ] E)
        (H * (T : E →L[ℝ] E))) (H * (T : E →L[ℝ] E)) +
      fderiv ℝ (areaExtension mu A) (T : E →L[ℝ] E) (H * (H * (T : E →L[ℝ] E))) := by
  simp_rw [area_path_eq_extension mu A hA H T]
  simpa only [operatorPath_zero] using!
    Curves.second_deriv_comp (areaExtension mu A) (operatorPath H (T : E →L[ℝ] E))
      (operatorPath H (H * (T : E →L[ℝ] E))) 0 (H * (H * (T : E →L[ℝ] E)))
      (by simpa only [operatorPath_zero] using contDiffAt_areaExtension mu A T)
      (operatorPath_hasDeriv H (T : E →L[ℝ] E))
      (by simpa only [operatorPath_zero] using
        operatorPath_hasDeriv H (H * (T : E →L[ℝ] E)) 0)

theorem sum_area_second_in_coordinates {ι : Type*} [Fintype ι]
    (A : Set (Sphere E)) (hA : MeasurableSet A)
    (H : ι → E →L[ℝ] E) (T : E ≃L[ℝ] E) :
    (∑ i, deriv (deriv (fun t => transformedArea mu A (T.trans (flowEquiv (H i) t)))) 0) =
      (∑ i, (fderiv ℝ (fderiv ℝ (areaExtension mu A)) (T : E →L[ℝ] E)
        (H i * (T : E →L[ℝ] E))) (H i * (T : E →L[ℝ] E))) +
      fderiv ℝ (areaExtension mu A) (T : E →L[ℝ] E)
        (∑ i, H i * (H i * (T : E →L[ℝ] E))) := by
  simp_rw [second_area_in_coordinates mu A hA]
  rw [Finset.sum_add_distrib, map_sum]

end ShadowVerification.AreaCoordinates

namespace ShadowVerification.AreaCoordinates
open Spherical Regularity Coordinates Integrated
open _root_.ShadowVerification.Frame

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]

/-- The actual symmetric harmonicity sum, now written using the ordinary
Fréchet Hessian and the drift in operator coordinates. -/
theorem coordinate_harmonicity (A : Set (UnitSphere n)) (hA : MeasurableSet A)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) :
    let u := areaExtension mu A
    let H : FrobeniusIndex n → EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
      fun i => operator (frame (frobeniusBasis (n := n)) i)
    (∑ i, (fderiv ℝ (fderiv ℝ u) (T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)
      (H i * (T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)))
      (H i * (T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n))) +
    fderiv ℝ u (T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)
      (∑ i, H i * (H i * (T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n))) = 0 := by
  dsimp only
  rw [← sum_area_second_in_coordinates mu A hA]
  exact Composition.sum_second_deriv_at_transformation mu A hA T

end ShadowVerification.AreaCoordinates

#print axioms ShadowVerification.AreaCoordinates.operatorPath_zero
#print axioms ShadowVerification.AreaCoordinates.operatorPath_hasDeriv
#print axioms ShadowVerification.AreaCoordinates.trans_flow_to_operator
#print axioms ShadowVerification.AreaCoordinates.area_path_eq_extension
#print axioms ShadowVerification.AreaCoordinates.first_area_in_coordinates
#print axioms ShadowVerification.AreaCoordinates.second_area_in_coordinates
#print axioms ShadowVerification.AreaCoordinates.sum_area_second_in_coordinates
#print axioms ShadowVerification.AreaCoordinates.coordinate_harmonicity

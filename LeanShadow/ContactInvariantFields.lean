import LeanShadow.ActualContact

/-! # Vanishing of the supplementary contact variations

The scalar and skew fields completing the ambient frame contribute zero
along the actual contact function. This follows from the actual area
invariances, at every invertible base point.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set MeasureTheory
open scoped BigOperators Topology
namespace ShadowVerification.ContactInvariance
open ActualContact FullFrame Coordinates Spherical Projective AmbientArea Integrated
open _root_.ShadowVerification.Frame _root_.ShadowVerification.Dual

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem operator_star (H : Matrix n n ℝ) : star (operator H) = operator H.transpose := by
  change H.toEuclideanLin.toContinuousLinearMap.adjoint = H.transpose.toEuclideanLin.toContinuousLinearMap
  rw [← LinearMap.adjoint_toContinuousLinearMap, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  simp

theorem skewGenerator_adjoint (i j : n) : star (operator (skewGenerator i j)) =
    -operator (skewGenerator i j) := by
  rw [operator_star, ← operator_neg]
  congr 1
  simp [skewGenerator, Matrix.transpose_sub, Matrix.transpose_single]

variable [Nonempty n] [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]

theorem contact_skew_flow (A B : Set (UnitSphere n)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (q p k rho : ℝ) (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n)
    (H : Matrix n n ℝ) (hH : star (operator H) = -operator H) (t : ℝ) :
    contact mu A B q p k rho (flow (leftField H) (point T) t) =
      contact mu A B q p k rho (point T) := by
  simp only [contact, flow_point, primal_point mu A hA, dual_point mu B hB]
  rw [Invariance.skew_area_at_transformation mu A hA T (operator H) hH,
    Invariance.dual_skew_area_at_transformation mu B hB T (operator H) hH]

theorem contact_scalar_flow (A B : Set (UnitSphere n)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (q p k rho : ℝ) (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) (t : ℝ) :
    contact mu A B q p k rho (flow (leftField 1) (point T) t) =
      contact mu A B q p k rho (point T) := by
  simp only [contact, flow_point, primal_point mu A hA, dual_point mu B hB, operator_one]
  simpa only [one_smul] using congrArg₂ (fun b a => b + Contact.support q p k rho a)
    (Invariance.dual_scalar_area_at_transformation mu B hB T 1 t)
    (Invariance.scalar_area_at_transformation mu A hA T 1 t)

theorem extra_contact_flow (A B : Set (UnitSphere n)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (q p k rho : ℝ) (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n)
    (i : ExtraIndex n) (t : ℝ) :
    contact mu A B q p k rho (flow (leftField (generator (.inr i))) (point T) t) =
      contact mu A B q p k rho (point T) := by
  cases i with
  | inl ij => exact contact_skew_flow mu A B hA hB q p k rho T _ (skewGenerator_adjoint ij.1 ij.2) t
  | inr u => exact contact_scalar_flow mu A B hA hB q p k rho T t

theorem extra_contact_first_zero (A B : Set (UnitSphere n))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (q p k rho : ℝ)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) (i : ExtraIndex n) :
    deriv (fun t => contact mu A B q p k rho
      (flow (leftField (generator (.inr i))) (point T) t)) 0 = 0 := by
  simp_rw [extra_contact_flow mu A B hA hB]
  exact deriv_const _ _

theorem extra_contact_second_zero (A B : Set (UnitSphere n))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (q p k rho : ℝ)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) (i : ExtraIndex n) :
    deriv (deriv (fun t => contact mu A B q p k rho
      (flow (leftField (generator (.inr i))) (point T) t))) 0 = 0 := by
  simp only [extra_contact_flow mu A B hA hB]
  have he : deriv (fun _ : ℝ => contact mu A B q p k rho (point T)) = (fun _ : ℝ => 0) :=
    funext fun t => deriv_const t _
  rw [he]
  exact deriv_const 0 0

end ShadowVerification.ContactInvariance
#print axioms ShadowVerification.ContactInvariance.operator_star
#print axioms ShadowVerification.ContactInvariance.skewGenerator_adjoint
#print axioms ShadowVerification.ContactInvariance.contact_skew_flow
#print axioms ShadowVerification.ContactInvariance.contact_scalar_flow
#print axioms ShadowVerification.ContactInvariance.extra_contact_flow
#print axioms ShadowVerification.ContactInvariance.extra_contact_first_zero
#print axioms ShadowVerification.ContactInvariance.extra_contact_second_zero

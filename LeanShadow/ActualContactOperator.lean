import LeanShadow.ContactInvariantFields
import LeanShadow.WeightedFullOperator

/-! # The weighted source inequality for the actual coordinate contact function

At every invertible parameter, the operator coefficients are constructed
from the actual transformed moment. The full ambient frame is used, with
identity weights on the skew and scalar fields. These fields contribute
zero by their proved whole-flow invariance. The trace correction is realized
as an actual first-order vector field. Coefficients are frozen at the point
of evaluation; no derivatives of the weight enter the nondivergence operator.

This is a differential inequality for actual Borel sets. A local maximum
coming from optimizer/profile theory is not assumed or concluded here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set MeasureTheory
open scoped BigOperators Topology Matrix.Norms.Frobenius
namespace ShadowVerification.ContactOperator
open ActualContact ContactInvariance FullFrame Coordinates Spherical Projective AmbientArea Integrated
open WeightedFlow WeightedFrame FullWeight Weighted
open _root_.ShadowVerification.Frame _root_.ShadowVerification.Dual

section Calculus
variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem flowHessian_diagonal (u : E → ℝ) (H : ι → E →L[ℝ] E) (x : E)
    (hu : ContDiffAt ℝ 2 u x) (i : ι) :
    flowHessian u H x i i = deriv (deriv (fun t => u (flow (H i) x t))) 0 := by
  rw [flowHessian_coordinates u H x hu, Curves.flow_second_deriv u (H i) x hu,
    Curves.secondLine_eq_fderiv u x _ hu,
    Curves.firstLine_eq_fderiv u x _ (hu.differentiableAt (by norm_num))]
  simp only [map_smul, map_add, smul_eq_mul]
  ring
end Calculus

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def fullFields : FullIndex n → Ambient n →L[ℝ] Ambient n :=
  fun i => leftField (generator i)

/-- The trace correction expressed as a genuine vector field. -/
noncomputable def traceDrift (Z : Matrix n n ℝ) (c : ℝ) (x : Ambient n) : Ambient n :=
  (-c) • ∑ i : FrobeniusIndex n,
    (frame (frobeniusBasis (n := n)) i * Z).trace • symmetricFields i x

variable [Nonempty n] [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]

theorem traceDrift_contact (A B : Set (UnitSphere n))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (q p k rho : ℝ)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) (Z : Matrix n n ℝ) (c : ℝ) :
    Elliptic.firstLine (contact mu A B q p k rho) (point T) (traceDrift Z c (point T)) =
      -c * (WeightedSource.contactGradient mu (action T '' A) (action (dualEquiv T) '' B)
        (Contact.slope p k rho (primal mu A (point T))) * Z).trace := by
  have hu := (contact_contDiffAt mu A B q p k rho T).differentiableAt (by norm_num)
  rw [Curves.firstLine_eq_fderiv _ _ _ hu, traceDrift, map_smul, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [← contact_gradient mu A B hA hB q p k rho T]
  simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  simp_rw [Curves.flow_first_deriv _ _ _ hu, Curves.firstLine_eq_fderiv _ _ _ hu]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Completing the weight does not change its action on the contact function. -/
theorem complete_contact_contraction (A B : Set (UnitSphere n))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (q p k rho : ℝ)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n)
    (W : Matrix (FrobeniusIndex n) (FrobeniusIndex n) ℝ) :
    (∑ i, ∑ j, completeWeight (κ := ExtraIndex n) W i j *
      flowHessian (contact mu A B q p k rho) fullFields (point T) i j) =
      ∑ i, ∑ j, W i j * WeightedSource.contactMatrix mu (action T '' A)
        (action (dualEquiv T) '' B) (Contact.slope p k rho (primal mu A (point T))) rho i j := by
  have hu := contact_contDiffAt mu A B q p k rho T
  have hd (i : ExtraIndex n) :
      flowHessian (contact mu A B q p k rho) fullFields (point T) (.inr i) (.inr i) = 0 := by
    rw [flowHessian_diagonal _ _ _ hu]
    exact extra_contact_second_zero mu A B hA hB q p k rho T i
  have he (i j : FrobeniusIndex n) :
      flowHessian (contact mu A B q p k rho) fullFields (point T) (.inl i) (.inl j) =
        flowHessian (contact mu A B q p k rho) symmetricFields (point T) i j := rfl
  simp [Fintype.sum_sum_type, completeWeight, Matrix.one_apply, he, hd,
    contact_hessian mu A B hA hB q p k rho T]

/-- The differential inequality for the actual contact function, with the
full coordinate operator, all acceleration terms, and the trace drift. -/
theorem actual_full_source (A B : Set (UnitSphere n))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (q p k rho L : ℝ)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n)
    (hrho : 0 ≤ rho) (hL : 0 ≤ L)
    (hcoefficient : 2 * rho ≤ ((Fintype.card n : ℝ) - 2) * L *
      Contact.slope p k rho (primal mu A (point T)))
    (hsmall : L * ‖Paired.actualMoment mu (action T '' A)‖ ≤ 1 / 2) :
    let Z := 1 - L • Paired.actualMoment mu (action T '' A)
    let W := weightCoefficients (frame (frobeniusBasis (n := n))) Z
    let coeff : Ambient n → Matrix (FullIndex n) (FullIndex n) ℝ := fun _ => completeWeight W
    let c := ((Fintype.card n : ℝ) - 2) / 2
    rho / 2 * ‖Paired.actualMoment mu (action T '' A)‖ ^ 2 ≤
      op coeff (fun i x => fullFields i x)
        (fun x => acceleration coeff fullFields x + traceDrift Z c x)
        (contact mu A B q p k rho) (point T) := by
  let Z := 1 - L • Paired.actualMoment mu (action T '' A)
  let W := weightCoefficients (frame (frobeniusBasis (n := n))) Z
  let coeff : Ambient n → Matrix (FullIndex n) (FullIndex n) ℝ := fun _ => completeWeight W
  let c := ((Fintype.card n : ℝ) - 2) / 2
  change rho / 2 * ‖Paired.actualMoment mu (action T '' A)‖ ^ 2 ≤
    op coeff (fun i x => fullFields i x)
      (fun x => acceleration coeff fullFields x + traceDrift Z c x)
      (contact mu A B q p k rho) (point T)
  rw [← weighted_flow_eq_op coeff fullFields (traceDrift Z c)
    (contact mu A B q p k rho) (point T)
    (completeWeight_symm W (weightCoefficients_symm _ _))
    (contact_contDiffAt mu A B q p k rho T)]
  dsimp only [coeff]
  rw [complete_contact_contraction mu A B hA hB q p k rho T,
    traceDrift_contact mu A B hA hB q p k rho T]
  have hh := WeightedSource.actual_source_lower_bound mu (action T '' A)
    (action (dualEquiv T) '' B) (measurable_action_image T A hA)
    (measurable_action_image (dualEquiv T) B hB)
    (Contact.slope p k rho (primal mu A (point T))) rho L hrho hL hcoefficient hsmall
  simpa only [W, Z, c, mul_comm, sub_eq_add_neg, neg_mul] using hh

end ShadowVerification.ContactOperator
#print axioms ShadowVerification.ContactOperator.flowHessian_diagonal
#print axioms ShadowVerification.ContactOperator.traceDrift_contact
#print axioms ShadowVerification.ContactOperator.complete_contact_contraction
#print axioms ShadowVerification.ContactOperator.actual_full_source

import LeanShadow.AmbientArea
import LeanShadow.InvariantArea
import LeanShadow.ContactCalculus
import LeanShadow.WeightedAreaSource
import LeanShadow.WeightedFlow

/-! # Contact variations of the actual primal and dual image measures

The contact function is defined on the full Euclidean matrix coordinates.
Its first and second exponential variations are proved from the actual
primal/dual flows and the scalar chain rule. In particular the negative
rank-one term is a conclusion, not a hypothesis about a formal matrix.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set MeasureTheory
open scoped BigOperators Topology Matrix.Norms.Frobenius
namespace ShadowVerification.ActualContact
open FullFrame Coordinates Spherical Projective AmbientArea AreaContraction Integrated
open _root_.ShadowVerification.Frame _root_.ShadowVerification.Dual

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem operator_neg (H : Matrix n n ℝ) : operator (-H) = -operator H :=
  (matrixOperator (n := n)).map_neg H

theorem leftField_add (H K : Matrix n n ℝ) : leftField (H + K) = leftField H + leftField K := by
  ext x
  simp only [leftField_apply, Matrix.add_mul, map_add, _root_.add_apply]

variable [Nonempty n] [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]

noncomputable def contact (A B : Set (UnitSphere n)) (q p k rho : ℝ) (x : Ambient n) : ℝ :=
  dual mu B x + Contact.support q p k rho (primal mu A x)

theorem primal_flow (A : Set (UnitSphere n)) (hA : MeasurableSet A)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) (H : Matrix n n ℝ) (t : ℝ) :
    primal mu A (flow (leftField H) (point T) t) =
      transformedArea mu (action T '' A) (flowEquiv (operator H) t) := by
  rw [flow_point, primal_point mu A hA, Composition.transformedArea_trans]

theorem dual_flow_symmetric (B : Set (UnitSphere n)) (hB : MeasurableSet B)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) (H : Matrix n n ℝ)
    (hH : H.IsSymm) (t : ℝ) :
    dual mu B (flow (leftField H) (point T) t) =
      transformedArea mu (action (dualEquiv T) '' B) (flowEquiv (operator (-H)) t) := by
  rw [flow_point, dual_point mu B hB,
    DualFlow.dual_area_flow_symmetric mu B T (operator H) (operator_symmetric H hH), operator_neg]

theorem first_primal (A : Set (UnitSphere n)) (hA : MeasurableSet A)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) (H : Matrix n n ℝ) :
    deriv (fun t => primal mu A (flow (leftField H) (point T) t)) 0 =
      firstArea mu (action T '' A) H := by
  simp_rw [primal_flow mu A hA]
  rfl

theorem second_primal (A : Set (UnitSphere n)) (hA : MeasurableSet A)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) (H : Matrix n n ℝ) :
    deriv (deriv (fun t => primal mu A (flow (leftField H) (point T) t))) 0 =
      secondArea mu (action T '' A) H := by
  simp_rw [primal_flow mu A hA]
  rfl

theorem first_dual (B : Set (UnitSphere n)) (hB : MeasurableSet B)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) (H : Matrix n n ℝ)
    (hH : H.IsSymm) (ht : H.trace = 0) :
    deriv (fun t => dual mu B (flow (leftField H) (point T) t)) 0 =
      -firstArea mu (action (dualEquiv T) '' B) H := by
  simp_rw [dual_flow_symmetric mu B hB T H hH]
  exact firstArea_neg mu _ (measurable_action_image (dualEquiv T) B hB) H hH ht

theorem second_dual (B : Set (UnitSphere n)) (hB : MeasurableSet B)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) (H : Matrix n n ℝ)
    (hH : H.IsSymm) (ht : H.trace = 0) :
    deriv (deriv (fun t => dual mu B (flow (leftField H) (point T) t))) 0 =
      secondArea mu (action (dualEquiv T) '' B) H := by
  simp_rw [dual_flow_symmetric mu B hB T H hH]
  exact secondArea_neg mu _ (measurable_action_image (dualEquiv T) B hB) H hH ht

theorem contact_contDiffAt (A B : Set (UnitSphere n)) (q p k rho : ℝ)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) :
    ContDiffAt ℝ 2 (contact mu A B q p k rho) (point T) := by
  have ha := primal_contDiffAt mu A T
  have hb := dual_contDiffAt mu B T
  unfold contact Contact.support
  fun_prop

theorem contact_first (A B : Set (UnitSphere n)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (q p k rho : ℝ) (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n)
    (H : Matrix n n ℝ) (hH : H.IsSymm) (ht : H.trace = 0) :
    deriv (fun t => contact mu A B q p k rho (flow (leftField H) (point T) t)) 0 =
      Contact.slope p k rho (primal mu A (point T)) * firstArea mu (action T '' A) H -
        firstArea mu (action (dualEquiv T) '' B) H := by
  have ha := Contact.along_flow_contDiffAt _ (leftField H) _ (primal_contDiffAt mu A T)
  have hb := Contact.along_flow_contDiffAt _ (leftField H) _ (dual_contDiffAt mu B T)
  have hd := (Contact.contact_hasDeriv q p k rho _ _ 0 _ _
    (ha.differentiableAt (by norm_num)).hasDerivAt
    (hb.differentiableAt (by norm_num)).hasDerivAt).deriv
  change deriv (fun t => dual mu B (flow (leftField H) (point T) t) +
    Contact.support q p k rho (primal mu A (flow (leftField H) (point T) t))) 0 = _
  rw [hd, first_primal mu A hA, first_dual mu B hB T H hH ht, flow_zero]
  ring

theorem contact_second (A B : Set (UnitSphere n)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (q p k rho : ℝ) (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n)
    (H : Matrix n n ℝ) (hH : H.IsSymm) (ht : H.trace = 0) :
    deriv (deriv (fun t => contact mu A B q p k rho (flow (leftField H) (point T) t))) 0 =
      secondArea mu (action (dualEquiv T) '' B) H +
        Contact.slope p k rho (primal mu A (point T)) * secondArea mu (action T '' A) H -
        rho * (firstArea mu (action T '' A) H) ^ 2 := by
  have ha := Contact.along_flow_contDiffAt _ (leftField H) _ (primal_contDiffAt mu A T)
  have hb := Contact.along_flow_contDiffAt _ (leftField H) _ (dual_contDiffAt mu B T)
  change deriv (deriv (fun t => dual mu B (flow (leftField H) (point T) t) +
    Contact.support q p k rho (primal mu A (flow (leftField H) (point T) t)))) 0 = _
  rw [Contact.contact_second_deriv q p k rho _ _ ha hb,
    first_primal mu A hA, second_primal mu A hA, second_dual mu B hB T H hH ht, flow_zero]

/-- Linearity follows from the proved Fréchet regularity of actual area. -/
theorem first_primal_add (A : Set (UnitSphere n)) (hA : MeasurableSet A)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) (H K : Matrix n n ℝ) :
    firstArea mu (action T '' A) (H + K) =
      firstArea mu (action T '' A) H + firstArea mu (action T '' A) K := by
  have ha := (primal_contDiffAt mu A T).differentiableAt (by norm_num)
  rw [← first_primal mu A hA T (H + K), ← first_primal mu A hA T H,
    ← first_primal mu A hA T K]
  simp_rw [Curves.flow_first_deriv _ _ _ ha, Curves.firstLine_eq_fderiv _ _ _ ha]
  rw [leftField_add, _root_.add_apply, map_add]

/-- The symmetric projective fields used in the geometric contraction. -/
noncomputable def symmetricFields : FrobeniusIndex n → Ambient n →L[ℝ] Ambient n :=
  fun i => leftField (frame (frobeniusBasis (n := n)) i)

/-- The actual contact Hessian is precisely the area matrix minus the rank-one term. -/
theorem contact_hessian (A B : Set (UnitSphere n)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (q p k rho : ℝ) (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) :
    WeightedFlow.flowHessian (contact mu A B q p k rho) symmetricFields (point T) =
      WeightedSource.contactMatrix mu (action T '' A) (action (dualEquiv T) '' B)
        (Contact.slope p k rho (primal mu A (point T))) rho := by
  ext i j
  let H := frame (frobeniusBasis (n := n))
  have hH (i : FrobeniusIndex n) : (H i).IsSymm := (frobeniusBasis i).property.1
  have ht (i : FrobeniusIndex n) : (H i).trace = 0 := (frobeniusBasis i).property.2
  change (deriv (deriv (fun t => contact mu A B q p k rho
      (flow (leftField (H i) + leftField (H j)) (point T) t))) 0 -
    deriv (deriv (fun t => contact mu A B q p k rho
      (flow (leftField (H i)) (point T) t))) 0 -
    deriv (deriv (fun t => contact mu A B q p k rho
      (flow (leftField (H j)) (point T) t))) 0) / 2 = _
  rw [← leftField_add, contact_second mu A B hA hB q p k rho T (H i + H j)
    ((hH i).add (hH j)) (by simp [Matrix.trace_add, ht]),
    contact_second mu A B hA hB q p k rho T (H i) (hH i) (ht i),
    contact_second mu A B hA hB q p k rho T (H j) (hH j) (ht j),
    first_primal_add mu A hA T]
  simp only [WeightedSource.contactMatrix, Paired.pairedMatrix, Paired.actualMatrix,
    polarizedAreaMatrix, Paired.actualFirst, rankOne, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  change _ = (secondArea mu (action (dualEquiv T) '' B) (H i + H j) -
    secondArea mu (action (dualEquiv T) '' B) (H i) -
    secondArea mu (action (dualEquiv T) '' B) (H j)) / 2 +
    Contact.slope p k rho (primal mu A (point T)) *
      ((secondArea mu (action T '' A) (H i + H j) -
        secondArea mu (action T '' A) (H i) - secondArea mu (action T '' A) (H j)) / 2) -
    rho * (firstArea mu (action T '' A) (H i) * firstArea mu (action T '' A) (H j))
  ring

/-- The reconstructed actual first derivatives give the moment defect. -/
theorem contact_gradient (A B : Set (UnitSphere n)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (q p k rho : ℝ) (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) :
    (∑ i : FrobeniusIndex n,
      deriv (fun t => contact mu A B q p k rho (flow (symmetricFields i) (point T) t)) 0 •
        frame (frobeniusBasis (n := n)) i) =
      WeightedSource.contactGradient mu (action T '' A) (action (dualEquiv T) '' B)
        (Contact.slope p k rho (primal mu A (point T))) := by
  simp only [symmetricFields]
  have hfirst (i : FrobeniusIndex n) := contact_first mu A B hA hB q p k rho T
    (frame (frobeniusBasis (n := n)) i) (frobeniusBasis i).property.1 (frobeniusBasis i).property.2
  simp_rw [hfirst, sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
  change _ = _ • Paired.actualMoment mu (action T '' A) -
    Paired.actualMoment mu (action (dualEquiv T) '' B)
  rw [← Paired.actual_first_reconstruction mu (action T '' A) (measurable_action_image T A hA),
    ← Paired.actual_first_reconstruction mu (action (dualEquiv T) '' B)
      (measurable_action_image (dualEquiv T) B hB)]
  rfl

end ShadowVerification.ActualContact
#print axioms ShadowVerification.ActualContact.operator_neg
#print axioms ShadowVerification.ActualContact.leftField_add
#print axioms ShadowVerification.ActualContact.primal_flow
#print axioms ShadowVerification.ActualContact.dual_flow_symmetric
#print axioms ShadowVerification.ActualContact.first_primal
#print axioms ShadowVerification.ActualContact.second_primal
#print axioms ShadowVerification.ActualContact.first_dual
#print axioms ShadowVerification.ActualContact.second_dual
#print axioms ShadowVerification.ActualContact.contact_contDiffAt
#print axioms ShadowVerification.ActualContact.contact_first
#print axioms ShadowVerification.ActualContact.contact_second
#print axioms ShadowVerification.ActualContact.first_primal_add

#print axioms ShadowVerification.ActualContact.contact_hessian
#print axioms ShadowVerification.ActualContact.contact_gradient

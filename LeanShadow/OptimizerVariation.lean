import LeanShadow.FlowMaximum
import LeanShadow.ProfileContactMaximum

/-! # Block 3: the actual optimizer supplies the variational hypotheses

At a Peano point of the unchanged shadow profile, feasibility supplies a
smooth local contact maximum with curvature rho + eps, for every eps > 0.
Its first derivative gives stationarity. Its Hessian gives the positive
matrix order, and closedness removes eps. The existing contraction then
applies to the actual centered moments, with no variation hypothesis left.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius
namespace ShadowVerification.OptimizerVariation
open Spherical Profile ProfileSupport ProfileContact ActualContact ActualLocal
open AmbientArea FullFrame Paired Integrated FlowMaximum
open _root_.ShadowVerification.Frame

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]

theorem stationarity_at_maximum (p : ℝ) (A B : Set (UnitSphere n))
    (h : IsOptimalPair mu p A B) (k rho : ℝ)
    (hm : IsLocalMax (contact mu A B (profile mu p) p k rho) (base (n := n))) :
    ∀ i, actualFirst mu B i = k * actualFirst mu A i := by
  intro i
  let T := ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ n)
  have hc := contact_contDiffAt mu A B (profile mu p) p k rho T
  have hd := contact_first mu A B h.measurable_left h.measurable_right
    (profile mu p) p k rho T (frame (frobeniusBasis (n := n)) i)
    (frobeniusBasis i).property.1 (frobeniusBasis i).property.2
  have he : action T = id := funext action_identity
  have hm' : IsLocalMax (contact mu A B (profile mu p) p k rho) (point T) := by
    simpa only [T, point_identity] using hm
  rw [flow_first_zero _ _ _ (hc.differentiableAt (by norm_num)) hm'] at hd
  simp only [T, point_identity, primal_base mu A h.measurable_left, h.mass_left,
    slope_at_center, dual_identity] at hd
  change 0 = k * AreaContraction.firstArea mu (action T '' A) (frame frobeniusBasis i) -
    AreaContraction.firstArea mu (action T '' B) (frame frobeniusBasis i) at hd
  rw [he, image_id, image_id] at hd
  exact (sub_eq_zero.mp hd.symm).symm

theorem variation_at_maximum (p : ℝ) (A B : Set (UnitSphere n))
    (h : IsOptimalPair mu p A B) (k rho : ℝ)
    (hm : IsLocalMax (contact mu A B (profile mu p) p k rho) (base (n := n))) :
    (rho • rankOne (actualFirst mu A) - pairedMatrix mu A B k).PosSemidef := by
  let T := ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ n)
  have hc := contact_contDiffAt mu A B (profile mu p) p k rho T
  have hm' : IsLocalMax (contact mu A B (profile mu p) p k rho) (point T) := by
    simpa only [T, point_identity] using hm
  have hv := flowHessian_neg_posSemidef _ symmetricFields _ hc hm'
  rw [contact_hessian mu A B h.measurable_left h.measurable_right] at hv
  have he : action T = id := funext action_identity
  simp only [T, point_identity, primal_base mu A h.measurable_left, h.mass_left,
    slope_at_center, dual_identity] at hv
  change (-WeightedSource.contactMatrix mu (action T '' A) (action T '' B) k rho).PosSemidef at hv
  simpa only [he, image_id, WeightedSource.contactMatrix, neg_sub] using hv

/-- The true first variations are stationary; no curvature sign is assumed. -/
theorem pair_stationarity (p : ℝ) (A B : Set (UnitSphere n))
    (h : IsOptimalPair mu p A B) (k rho : ℝ)
    (hexp : HasQuadraticExpansion (profile mu) p k rho) :
    ∀ i, actualFirst mu B i = k * actualFirst mu A i :=
  stationarity_at_maximum mu p A B h k (rho + 1)
    (contact_maximum_of_expansion mu p A B h k rho 1 hexp zero_lt_one)

/-- The limiting order uses rho itself, not a fixed inflated curvature. -/
theorem pair_second_variation (p : ℝ) (A B : Set (UnitSphere n))
    (h : IsOptimalPair mu p A B) (k rho : ℝ)
    (hexp : HasQuadraticExpansion (profile mu) p k rho) :
    (rho • rankOne (actualFirst mu A) - pairedMatrix mu A B k).PosSemidef := by
  apply posSemidef_of_pos_perturbation _ (rankOne (actualFirst mu A))
  intro eps heps
  have hv := variation_at_maximum mu p A B h k (rho + eps)
    (contact_maximum_of_expansion mu p A B h k rho eps hexp heps)
  convert hv using 1
  module

theorem pair_moment_stationarity (p : ℝ) (A B : Set (UnitSphere n))
    (h : IsOptimalPair mu p A B) (k rho : ℝ)
    (hexp : HasQuadraticExpansion (profile mu) p k rho) :
    actualMoment mu B = k • actualMoment mu A :=
  stationary_moments mu A B h.measurable_left h.measurable_right k
    (pair_stationarity mu p A B h k rho hexp)

/-- All optimizer, contact, variation, and contraction inputs are discharged. -/
theorem pair_matrix_bound (p : ℝ) (A B : Set (UnitSphere n))
    (h : IsOptimalPair mu p A B) (k rho : ℝ)
    (hexp : HasQuadraticExpansion (profile mu) p k rho) :
    (rho • (actualMoment mu A * actualMoment mu A) +
      (((Fintype.card n : ℝ) - 2) * k) • actualMoment mu A).PosSemidef :=
  actual_variation_bound mu A B h.measurable_left h.measurable_right k rho
    (pair_stationarity mu p A B h k rho hexp)
    (pair_second_variation mu p A B h k rho hexp)

theorem optimizer_matrix_bound (p : ℝ) (A : Set (UnitSphere n))
    (hA : IsOptimizer mu p A) (k rho : ℝ)
    (hexp : HasQuadraticExpansion (profile mu) p k rho) :
    (rho • (actualMoment mu A * actualMoment mu A) +
      (((Fintype.card n : ℝ) - 2) * k) • actualMoment mu A).PosSemidef :=
  pair_matrix_bound mu p A (avoidingPartner mu A) (optimalPair_of_optimizer mu p A hA)
    k rho hexp

end ShadowVerification.OptimizerVariation
#print axioms ShadowVerification.OptimizerVariation.stationarity_at_maximum
#print axioms ShadowVerification.OptimizerVariation.variation_at_maximum
#print axioms ShadowVerification.OptimizerVariation.pair_stationarity
#print axioms ShadowVerification.OptimizerVariation.pair_second_variation
#print axioms ShadowVerification.OptimizerVariation.pair_moment_stationarity
#print axioms ShadowVerification.OptimizerVariation.pair_matrix_bound
#print axioms ShadowVerification.OptimizerVariation.optimizer_matrix_bound

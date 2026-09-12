import LeanShadow.ProfileContactMaximum
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # From actual moment vanishing to actual area constancy

The moment field records the symmetric trace-free first variations. Rotations
and scalar dilations supply the remaining zero derivatives. The already
constructed full frame separates all covectors near the identity, so the
entire Fréchet derivative vanishes. The mean-value theorem then gives local
constancy of actual transformed area. No analyticity or compression limit is
assumed in this step.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set MeasureTheory Filter
open scoped BigOperators Topology Matrix.Norms.Frobenius
namespace ShadowVerification.LocalArea
open FullFrame Coordinates Spherical Projective AmbientArea Integrated ActualContact
open _root_.ShadowVerification.Frame

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]

omit [Nonempty n] [BorelSpace (EuclideanSpace ℝ n)] [mu.IsAddHaarMeasure] in
/-- Extracting a coefficient from the actual moment expansion. -/
theorem symmetric_derivative_eq_pairing (A : Set (UnitSphere n)) (x : Ambient n)
    (i : FrobeniusIndex n) :
    fderiv ℝ (primal mu A) x (symmetricFields i x) =
      pairing (frame (frobeniusBasis (n := n)) i) (MomentField.moment mu A x) := by
  classical
  rw [MomentField.moment, pairing_sum_right]
  simp only [pairing_smul_right]
  have h := frobeniusBasis_orthonormal (n := n)
  unfold Frame.IsOrthonormal at h
  simp_rw [h]
  simp

omit [Nonempty n] [BorelSpace (EuclideanSpace ℝ n)] [mu.IsAddHaarMeasure] in
theorem symmetric_derivative_zero (A : Set (UnitSphere n)) (x : Ambient n)
    (hz : MomentField.moment mu A x = 0) (i : FrobeniusIndex n) :
    fderiv ℝ (primal mu A) x (symmetricFields i x) = 0 := by
  rw [symmetric_derivative_eq_pairing, hz]
  simp [pairing]

/-- Rotations preserve the actual primal area along the entire flow. -/
theorem primal_skew_flow (A : Set (UnitSphere n)) (hA : MeasurableSet A)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n)
    (H : Matrix n n ℝ) (hH : star (operator H) = -operator H) (t : ℝ) :
    primal mu A (flow (leftField H) (point T) t) = primal mu A (point T) := by
  simp only [flow_point, primal_point mu A hA]
  exact Invariance.skew_area_at_transformation mu A hA T (operator H) hH t

/-- Scalar dilation acts trivially on directions and hence on actual area. -/
theorem primal_scalar_flow (A : Set (UnitSphere n)) (hA : MeasurableSet A)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) (t : ℝ) :
    primal mu A (flow (leftField 1) (point T) t) = primal mu A (point T) := by
  simp only [flow_point, primal_point mu A hA, operator_one]
  simpa only [one_smul] using Invariance.scalar_area_at_transformation mu A hA T 1 t

theorem extra_primal_flow (A : Set (UnitSphere n)) (hA : MeasurableSet A)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) (i : ExtraIndex n) (t : ℝ) :
    primal mu A (flow (leftField (generator (.inr i))) (point T) t) =
      primal mu A (point T) := by
  cases i with
  | inl ij =>
    exact primal_skew_flow mu A hA T _
      (ContactInvariance.skewGenerator_adjoint ij.1 ij.2) t
  | inr u => exact primal_scalar_flow mu A hA T t

theorem extra_derivative_zero (A : Set (UnitSphere n)) (hA : MeasurableSet A)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) (i : ExtraIndex n) :
    fderiv ℝ (primal mu A) (point T) (leftField (generator (.inr i)) (point T)) = 0 := by
  have ha := (primal_contDiffAt mu A T).differentiableAt (by norm_num)
  rw [← Curves.firstLine_eq_fderiv _ _ _ ha, ← Curves.flow_first_deriv _ _ _ ha]
  simp_rw [extra_primal_flow mu A hA]
  exact deriv_const _ _

theorem full_field_derivatives_zero (A : Set (UnitSphere n)) (hA : MeasurableSet A)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n)
    (hz : MomentField.moment mu A (point T) = 0) (i : FullIndex n) :
    fderiv ℝ (primal mu A) (point T) (leftField (generator i) (point T)) = 0 := by
  cases i with
  | inl j => exact symmetric_derivative_zero mu A (point T) hz j
  | inr j => exact extra_derivative_zero mu A hA T j

omit [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)] in
/-- Near the identity, annihilating the full frame annihilates a covector. -/
theorem eventually_covector_separation :
    ∀ᶠ x in 𝓝 (base (n := n)), ∀ d : Ambient n →L[ℝ] ℝ,
      (∀ i : FullIndex n, d (leftField (generator i) x) = 0) → d = 0 := by
  obtain ⟨lam, hlam, hnear⟩ := FullWeight.geometric_uniform_ellipticity
    (fun _ : Ambient n => (0 : Matrix n n ℝ)) 0 continuousAt_const (by norm_num) (by norm_num)
  filter_upwards [hnear] with x hx d hd
  let v := (InnerProductSpace.toDual ℝ (Ambient n)).symm d
  have hv (i : FullIndex n) : inner ℝ v (leftField (generator i) x) = 0 := by
    rw [InnerProductSpace.toDual_symm_apply]
    exact hd i
  have hb := hx v
  simp only [WeightedEllipticity.symbol, hv, dotProduct, zero_mul, Finset.sum_const_zero] at hb
  have hn : v = 0 := by
    have : ‖v‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  apply (InnerProductSpace.toDual ℝ (Ambient n)).symm.injective
  simpa only [map_zero] using hn

/-- This implication concerns the full derivative of actual area. -/
theorem eventually_fderiv_zero_of_moment_zero (A : Set (UnitSphere n))
    (hA : MeasurableSet A)
    (hz : ∀ᶠ x in 𝓝 (base (n := n)), MomentField.moment mu A x = 0) :
    ∀ᶠ x in 𝓝 (base (n := n)),
      DifferentiableAt ℝ (primal mu A) x ∧ fderiv ℝ (primal mu A) x = 0 := by
  have hp : ∀ᶠ x in 𝓝 (base (n := n)),
      ∃ T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n, point T = x := by
    simpa only [ActualLocal.point_identity] using
      MomentField.eventually_point (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ n))
  filter_upwards [hp, hz, eventually_covector_separation (n := n)] with x hx hxz hsep
  obtain ⟨T, rfl⟩ := hx
  exact ⟨(primal_contDiffAt mu A T).differentiableAt (by norm_num),
    hsep _ (full_field_derivatives_zero mu A hA T hxz)⟩

/-- Moment vanishing on a neighborhood forces the actual area to be constant there. -/
theorem locally_constant_of_moment_zero (A : Set (UnitSphere n)) (hA : MeasurableSet A)
    (hz : ∀ᶠ x in 𝓝 (base (n := n)), MomentField.moment mu A x = 0) :
    primal mu A =ᶠ[𝓝 (base (n := n))] (fun _ => area mu A) := by
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp
    (eventually_fderiv_zero_of_moment_zero mu A hA hz)
  have hc := Nonisotropy.locally_constant_of_derivative_zero (primal mu A) base r hr
    (fun x hx => (hb hx).1.differentiableWithinAt) (fun x hx => (hb hx).2)
  simpa only [ProfileContact.primal_base mu A hA] using hc

/-- The local constancy conclusion is now derived from an actual optimizer and
a positive-slope second-order profile expansion. -/
theorem isotropic_optimizer_area_constant_near (p : ℝ) (A : Set (UnitSphere n))
    (hA : Profile.IsOptimizer mu p A) (k rho : ℝ)
    (hexp : ProfileSupport.HasQuadraticExpansion (Profile.profile mu) p k rho)
    (hk : 0 < k) (hn : (2 : ℝ) < Fintype.card n) (hiso : Paired.actualMoment mu A = 0) :
    primal mu A =ᶠ[𝓝 (base (n := n))] (fun _ => p) := by
  have hc := locally_constant_of_moment_zero mu A hA.measurable
    (ProfileContact.isotropic_optimizer_moment_zero_near mu p A hA k rho hexp hk hn hiso)
  simpa only [hA.mass] using hc

end ShadowVerification.LocalArea
#print axioms ShadowVerification.LocalArea.symmetric_derivative_eq_pairing
#print axioms ShadowVerification.LocalArea.symmetric_derivative_zero
#print axioms ShadowVerification.LocalArea.primal_skew_flow
#print axioms ShadowVerification.LocalArea.primal_scalar_flow
#print axioms ShadowVerification.LocalArea.extra_primal_flow
#print axioms ShadowVerification.LocalArea.extra_derivative_zero
#print axioms ShadowVerification.LocalArea.full_field_derivatives_zero
#print axioms ShadowVerification.LocalArea.eventually_covector_separation
#print axioms ShadowVerification.LocalArea.eventually_fderiv_zero_of_moment_zero
#print axioms ShadowVerification.LocalArea.locally_constant_of_moment_zero
#print axioms ShadowVerification.LocalArea.isotropic_optimizer_area_constant_near

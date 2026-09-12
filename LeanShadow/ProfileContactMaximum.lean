import LeanShadow.ShadowProfile
import LeanShadow.QuadraticSupport
import LeanShadow.ActualLocalNonisotropy

/-! # Contact maxima derived from the actual optimal shadow profile

For an actual optimal pair, feasibility gives b(T) + f(a(T)) <= 1. A local
quadratic lower support phi <= f, with phi(p)=f(p), then gives h=b+phi(a)<=1
near the identity and h(I)=1. Continuity of actual area and openness of the
invertible parameters justify the composition on a full coordinate neighborhood.

The optimizer versions construct the partner from the optimizer itself.
The expansion version derives its lower support from a Peano remainder.
The final theorem applies the previously checked elliptic argument without
assuming a contact maximum, feasibility formula, or operator inequality.
Existence of optimizers and of second-order profile points is not asserted.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set MeasureTheory Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius
namespace ShadowVerification.ProfileContact
open Spherical Profile ProfileSupport ActualContact ActualLocal AmbientArea FullFrame Integrated
open _root_.ShadowVerification.Dual

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem dual_identity : dualEquiv (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ n)) =
    ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ n) := by
  symm
  apply DualFlow.dual_unique
  intro x y
  rfl

variable [Nonempty n] [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]

theorem primal_base (A : Set (UnitSphere n)) (hA : MeasurableSet A) :
    primal mu A (base (n := n)) = area mu A := by
  rw [← point_identity, primal_point mu A hA]
  have he : action (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ n)) = id :=
    funext action_identity
  simp only [transformedArea, he, image_id]

theorem dual_base (B : Set (UnitSphere n)) (hB : MeasurableSet B) :
    dual mu B (base (n := n)) = area mu B := by
  rw [← point_identity, dual_point mu B hB, dual_identity]
  have he : action (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ n)) = id :=
    funext action_identity
  simp only [transformedArea, he, image_id]

theorem optimal_contact_value (p : ℝ) (A B : Set (UnitSphere n))
    (h : IsOptimalPair mu p A B) (k rho : ℝ) :
    contact mu A B (profile mu p) p k rho (base (n := n)) = 1 := by
  rw [contact, primal_base mu A h.measurable_left, dual_base mu B h.measurable_right,
    h.mass_left, support_at_center, h.mass_right]
  ring

theorem contact_le_one_at_transformation (p : ℝ) (A B : Set (UnitSphere n))
    (h : IsOptimalPair mu p A B) (k rho : ℝ)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n)
    (hlower : Contact.support (profile mu p) p k rho (primal mu A (point T)) ≤
      profile mu (primal mu A (point T))) :
    contact mu A B (profile mu p) p k rho (point T) ≤ 1 := by
  have hf := transformed_feasible_bound mu A B h.measurable_left h.measurable_right
    h.antipodal_left h.avoids T
  rw [primal_point mu A h.measurable_left] at hlower
  rw [contact, primal_point mu A h.measurable_left, dual_point mu B h.measurable_right]
  linarith

/-- The actual profile lower support implies a local maximum in the full coordinates. -/
theorem contact_maximum_of_lower_support (p : ℝ) (A B : Set (UnitSphere n))
    (h : IsOptimalPair mu p A B) (k rho : ℝ)
    (hlower : ∀ᶠ s in 𝓝 p, Contact.support (profile mu p) p k rho s ≤ profile mu s) :
    IsLocalMax (contact mu A B (profile mu p) p k rho) (base (n := n)) := by
  have ha : ContinuousAt (primal mu A) (base (n := n)) := by
    simpa only [point_identity] using
      (primal_contDiffAt mu A (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ n))).continuousAt
  have ht : Tendsto (primal mu A) (𝓝 (base (n := n))) (𝓝 p) := by
    simpa only [primal_base mu A h.measurable_left, h.mass_left] using ha.tendsto
  have hpoints : ∀ᶠ x in 𝓝 (base (n := n)),
      ∃ T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n, point T = x := by
    simpa only [point_identity] using
      MomentField.eventually_point (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ n))
  change ∀ᶠ x in 𝓝 (base (n := n)),
    contact mu A B (profile mu p) p k rho x ≤ contact mu A B (profile mu p) p k rho base
  rw [optimal_contact_value mu p A B h k rho]
  filter_upwards [hpoints, ht.eventually hlower] with x hx hsupport
  obtain ⟨T, rfl⟩ := hx
  exact contact_le_one_at_transformation mu p A B h k rho T hsupport

/-- No differentiability of the profile at neighboring masses is needed. -/
theorem contact_maximum_of_expansion (p : ℝ) (A B : Set (UnitSphere n))
    (h : IsOptimalPair mu p A B) (k rho eps : ℝ)
    (hexp : HasQuadraticExpansion (profile mu) p k rho) (heps : 0 < eps) :
    IsLocalMax (contact mu A B (profile mu p) p k (rho + eps)) (base (n := n)) :=
  contact_maximum_of_lower_support mu p A B h k (rho + eps)
    (lower_support_of_expansion (profile mu) p k rho hexp eps heps)

/-- For a given actual optimizer, both the partner and the contact maximum are supplied. -/
theorem optimizer_contact_maximum (p : ℝ) (A : Set (UnitSphere n))
    (hA : IsOptimizer mu p A) (k rho eps : ℝ)
    (hexp : HasQuadraticExpansion (profile mu) p k rho) (heps : 0 < eps) :
    IsLocalMax (contact mu A (avoidingPartner mu A) (profile mu p) p k (rho + eps))
      (base (n := n)) :=
  contact_maximum_of_expansion mu p A _ (optimalPair_of_optimizer mu p A hA) k rho eps hexp heps

/-- The local elliptic implication now follows from actual profile optimality
and a single second-order expansion, without a contact-maximum hypothesis. -/
theorem isotropic_optimizer_moment_zero_near (p : ℝ) (A : Set (UnitSphere n))
    (hA : IsOptimizer mu p A) (k rho : ℝ)
    (hexp : HasQuadraticExpansion (profile mu) p k rho)
    (hk : 0 < k) (hn : (2 : ℝ) < Fintype.card n)
    (hiso : Paired.actualMoment mu A = 0) :
    ∀ᶠ x in 𝓝 (base (n := n)), MomentField.moment mu A x = 0 := by
  obtain ⟨rho₀, hrho₀, _, hlower⟩ := positive_lower_support (profile mu) p k rho hexp
  have hmax := contact_maximum_of_lower_support mu p A (avoidingPartner mu A)
    (optimalPair_of_optimizer mu p A hA) k rho₀ hlower
  have hslope : 0 < Contact.slope p k rho₀ (primal mu A (base (n := n))) := by
    rw [primal_base mu A hA.measurable, hA.mass, slope_at_center]
    exact hk
  have hh := isotropic_contact_maximum mu A (avoidingPartner mu A) hA.measurable
    (avoidingPartner_measurable mu A) (profile mu p) p k rho₀ hn
    hrho₀ hslope hiso hmax
  exact hh.mono fun _ hx => hx.2

end ShadowVerification.ProfileContact
#print axioms ShadowVerification.ProfileContact.dual_identity
#print axioms ShadowVerification.ProfileContact.primal_base
#print axioms ShadowVerification.ProfileContact.dual_base
#print axioms ShadowVerification.ProfileContact.optimal_contact_value
#print axioms ShadowVerification.ProfileContact.contact_le_one_at_transformation
#print axioms ShadowVerification.ProfileContact.contact_maximum_of_lower_support
#print axioms ShadowVerification.ProfileContact.contact_maximum_of_expansion
#print axioms ShadowVerification.ProfileContact.optimizer_contact_maximum
#print axioms ShadowVerification.ProfileContact.isotropic_optimizer_moment_zero_near

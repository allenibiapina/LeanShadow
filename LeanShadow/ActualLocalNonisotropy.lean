import LeanShadow.ActualMomentField
import LeanShadow.WeightedOpenMaximum

/-! # The actual local elliptic consequence of hypothetical isotropy

For the contact function of two actual Borel sets, isotropy at the identity,
a positive quadratic-support slope, and a local maximum imply that the
actual transformed moment vanishes on a neighborhood. Every coefficient,
regularity, source, and ellipticity input is supplied by proved constructions.

The local maximum is still explicit. Deriving it from the optimal profile,
and proving the compression contradiction after local moment vanishing,
remain necessary to conclude nonisotropy of actual optimizers.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set MeasureTheory Filter
open scoped BigOperators Topology Matrix.Norms.Frobenius
namespace ShadowVerification.ActualLocal
open ActualContact ContactOperator FullFrame Coordinates Spherical Projective AmbientArea Integrated
open MomentField WeightedFrame
open _root_.ShadowVerification.Frame

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem point_identity : point (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ n)) =
    base (n := n) := by
  apply coordinateEquiv.injective
  rw [coordinate_point, coordinate_base]
  rfl

omit [DecidableEq n] in
theorem action_identity (x : UnitSphere n) :
    action (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ n)) x = x := by
  apply Subtype.ext
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp x.property)

variable [Nonempty n] [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]

theorem moment_base (A : Set (UnitSphere n)) (hA : MeasurableSet A) :
    moment mu A (base (n := n)) = Paired.actualMoment mu A := by
  rw [← point_identity, moment_point mu A hA]
  have he : action (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ n)) = id :=
    funext action_identity
  rw [he, image_id]

/-- The weighted elliptic argument now acts on actual image measures. -/
theorem isotropic_contact_maximum (A B : Set (UnitSphere n))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (q p k rho : ℝ)
    (hn : (2 : ℝ) < Fintype.card n) (hrho : 0 < rho)
    (hslope : 0 < Contact.slope p k rho (primal mu A (base (n := n))))
    (hiso : Paired.actualMoment mu A = 0)
    (hmax : IsLocalMax (contact mu A B q p k rho) (base (n := n))) :
    ∀ᶠ x in 𝓝 (base (n := n)),
      contact mu A B q p k rho x = contact mu A B q p k rho base ∧ moment mu A x = 0 := by
  let T := ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ n)
  have hp : point T = base := point_identity
  obtain ⟨L, hL, hnear⟩ := local_source_at_isotropic mu A B hA hB q p k rho T hn hrho
    (by simpa only [hp] using hslope) (by rw [hp, moment_base mu A hA, hiso])
  rw [hp] at hnear
  apply WeightedOpen.source_zero_near_local_maximum
    (coefficients mu A L) (fun i x => fullFields i x) (drift mu A L)
    (contact mu A B q p k rho) (moment mu A) base (rho / 2) (half_pos hrho)
  · intro i j
    simpa only [hp] using coefficients_continuousAt mu A L T i j
  · intro i
    exact (fullFields i).continuous.continuousAt
  · simpa only [hp] using drift_continuousAt mu A L T
  · exact hnear.self_of_nhds.1
  · exact fields_separate_at_base
  · exact hmax
  · filter_upwards [hnear] with x hx
    exact ⟨hx.2.1, hx.1.posSemidef, hx.2.2⟩

end ShadowVerification.ActualLocal
#print axioms ShadowVerification.ActualLocal.point_identity
#print axioms ShadowVerification.ActualLocal.action_identity
#print axioms ShadowVerification.ActualLocal.moment_base
#print axioms ShadowVerification.ActualLocal.isotropic_contact_maximum

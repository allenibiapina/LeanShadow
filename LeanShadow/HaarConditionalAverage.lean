import LeanShadow.OrthogonalStabilizer
import LeanShadow.SphericalIncidenceOperator
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! # Continuous orthogonality averages from actual stabilizer Haar measure

Averaging over the stabilizer is a proved conditional-averaging operation.
The averaged continuous function descends along the sphere orbit map.
Its pairing identity identifies it with the already constructed L² operator.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.ConditionalAverage
open Spherical OrthogonalHaar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

def translated (a : Sphere E) (f : C(OrthogonalHaar.Group E, ℝ)) :
    C(AxisStabilizer.subgroup a, C(OrthogonalHaar.Group E, ℝ)) :=
  (f.comp ⟨fun z : AxisStabilizer.subgroup a × OrthogonalHaar.Group E => z.2 * z.1.1,
    continuous_snd.mul (continuous_subtype_val.comp continuous_fst)⟩).curry

def average (a : Sphere E) (f : C(OrthogonalHaar.Group E, ℝ)) : C(OrthogonalHaar.Group E, ℝ) :=
  ∫ U, translated a f U ∂AxisStabilizer.haar a

theorem average_apply (a : Sphere E) (f : C(OrthogonalHaar.Group E, ℝ))
    (R : OrthogonalHaar.Group E) :
    average a f R = ∫ U : AxisStabilizer.subgroup a, f (R * U.1) ∂AxisStabilizer.haar a :=
  ContinuousMap.integral_apply
    (memLp_one_iff_integrable.mp
      ((translated a f).memLp ℝ (p := 1) (μ := AxisStabilizer.haar a))) R

theorem average_right (a : Sphere E) (f : C(OrthogonalHaar.Group E, ℝ))
    (R : OrthogonalHaar.Group E) (S : AxisStabilizer.subgroup a) :
    average a f (R * S.1) = average a f R := by
  rw [average_apply, average_apply]
  simpa only [mul_assoc, Subgroup.coe_mul] using
    integral_mul_left_eq_self (μ := AxisStabilizer.haar a)
      (fun U : AxisStabilizer.subgroup a => f (R * U.1)) S

/-- Stabilizer averaging preserves pairings with right-invariant continuous functions. -/
theorem pairing (a : Sphere E) (f w : C(OrthogonalHaar.Group E, ℝ))
    (hw : ∀ R (U : AxisStabilizer.subgroup a), w (R * U.1) = w R) :
    (∫ R, w R * average a f R ∂haar E) = ∫ R, w R * f R ∂haar E := by
  simp_rw [average_apply, ← integral_const_mul]
  let k : C(OrthogonalHaar.Group E × AxisStabilizer.subgroup a, ℝ) :=
    ⟨fun z => w z.1 * f (z.1 * z.2.1), by fun_prop⟩
  have hi : Integrable (fun z : OrthogonalHaar.Group E × AxisStabilizer.subgroup a =>
      w z.1 * f (z.1 * z.2.1)) ((haar E).prod (AxisStabilizer.haar a)) :=
    memLp_one_iff_integrable.mp
      (k.memLp ℝ (p := 1) (μ := (haar E).prod (AxisStabilizer.haar a)))
  rw [integral_integral_swap hi]
  have he (U : AxisStabilizer.subgroup a) :
      (∫ R, w R * f (R * U.1) ∂haar E) = ∫ R, w R * f R ∂haar E := by
    calc
      _ = ∫ R, w (R * U.1) * f (R * U.1) ∂haar E := by
        apply integral_congr_ae
        exact Eventually.of_forall fun R => by
          change w R * f (R * U.1) = w (R * U.1) * f (R * U.1)
          rw [hw]
      _ = _ := integral_mul_right_eq_self (fun R : OrthogonalHaar.Group E => w R * f R) U.1
  simp_rw [he]
  simp

def orbit (a : Sphere E) : C(OrthogonalHaar.Group E, Sphere E) :=
  ⟨fun R => rotate R a, rotate_continuous.comp (continuous_id.prodMk continuous_const)⟩

theorem orbit_quotient (a : Sphere E) : Topology.IsQuotientMap (orbit a) :=
  Topology.IsQuotientMap.of_surjective_continuous
    (fun x => by obtain ⟨R, h, _⟩ := exists_exchange a x; exact ⟨R, h⟩) (orbit a).continuous

theorem average_factors (a : Sphere E) (f : C(OrthogonalHaar.Group E, ℝ)) :
    Function.FactorsThrough (average a f) (orbit a) := by
  intro R S h
  obtain ⟨U, rfl⟩ := AxisStabilizer.same_axis a R S h
  exact average_right a f S U

def descend (a : Sphere E) (f : C(OrthogonalHaar.Group E, ℝ)) : C(Sphere E, ℝ) :=
  (orbit_quotient a).lift (average a f) (average_factors a f)

theorem descend_orbit (a : Sphere E) (f : C(OrthogonalHaar.Group E, ℝ))
    (R : OrthogonalHaar.Group E) : descend a f (rotate R a) = average a f R := by
  exact congrArg (fun g : C(OrthogonalHaar.Group E, ℝ) => g R)
    ((orbit_quotient a).lift_comp (average a f) (average_factors a f))

def spherical (a b : Sphere E) (v : C(Sphere E, ℝ)) : C(Sphere E, ℝ) :=
  descend a (v.comp (orbit b))

theorem spherical_orbit (a b : Sphere E) (v : C(Sphere E, ℝ))
    (R : OrthogonalHaar.Group E) :
    spherical a b v (rotate R a) =
      ∫ U : AxisStabilizer.subgroup a, v (rotate (R * U.1) b) ∂AxisStabilizer.haar a := by
  rw [spherical, descend_orbit, average_apply]
  rfl

variable [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

/-- The descended spherical average has exactly the Haar-frame pairing. -/
theorem spherical_pairing (a b : Sphere E) (u v : C(Sphere E, ℝ)) :
    (∫ x, u x * spherical a b v x ∂probability mu) =
      ∫ R : OrthogonalHaar.Group E, u (rotate R a) * v (rotate R b) ∂haar E := by
  rw [← SphericalRotation.orbit_map_probability mu a]
  change (∫ x, u x * spherical a b v x ∂(haar E).map (orbit a)) = _
  rw [integral_map (orbit a).continuous.measurable.aemeasurable
      (show Continuous (fun x => u x * spherical a b v x) by fun_prop).aestronglyMeasurable]
  change (∫ R, u (rotate R a) * descend a (v.comp (orbit b)) (rotate R a) ∂haar E) = _
  simp_rw [descend_orbit]
  apply pairing a (v.comp (orbit b)) (u.comp (orbit a))
  intro R U
  change u (rotate (R * U.1) a) = u (rotate R a)
  rw [rotate_mul, AxisStabilizer.fixed]

end ShadowVerification.ConditionalAverage
#print axioms ShadowVerification.ConditionalAverage.average_apply
#print axioms ShadowVerification.ConditionalAverage.average_right
#print axioms ShadowVerification.ConditionalAverage.pairing
#print axioms ShadowVerification.ConditionalAverage.orbit_quotient
#print axioms ShadowVerification.ConditionalAverage.average_factors
#print axioms ShadowVerification.ConditionalAverage.descend_orbit
#print axioms ShadowVerification.ConditionalAverage.spherical_orbit
#print axioms ShadowVerification.ConditionalAverage.spherical_pairing

import LeanShadow.SphericalCaps
import LeanShadow.SmallShadowCaps
import LeanShadow.MomentComparison

/-! # Sharp axial second-moment comparison and its equality case -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Real
open scoped Topology ENNReal
namespace ShadowVerification.SphericalMomentBound
open Spherical SphericalCaps CapFunctions
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem cap_threshold (a : Sphere E) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi/2))
    (x : Sphere E) : x ∈ cap a r ↔ Real.cos r ^ 2 < (inner ℝ (a : E) (x : E)) ^ 2 := by
  have hc : 0 ≤ Real.cos r := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hr.1,Real.pi_pos],hr.2⟩
  change Real.cos r < |inner ℝ (a : E) (x : E)| ↔ _
  rw [← sq_abs (inner ℝ (a : E) (x : E))]
  exact (sq_lt_sq₀ hc (abs_nonneg _)).symm

theorem equal_cap_measure (hd : 1 < Module.finrank ℝ E) (a : Sphere E) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) (A : Set (Sphere E))
    (hmass : area mu A = capMass (Module.finrank ℝ E - 2) r) :
    probability mu A = probability mu (cap a r) := by
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact hmass.trans (cap_area mu hd a r hr).symm

theorem moment_maximal (hd : 1 < Module.finrank ℝ E) (a : Sphere E) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) (A : Set (Sphere E)) (hA : MeasurableSet A)
    (hmass : area mu A = capMass (Module.finrank ℝ E - 2) r) :
    (∫ x in A, (inner ℝ (a : E) (x : E)) ^ 2 ∂probability mu) ≤
      capMoment (Module.finrank ℝ E - 2) r := by
  rw [← cap_axial_moment mu hd a r hr]
  apply superlevel_integral_maximal (probability mu) A (cap a r)
    (fun x => (inner ℝ (a : E) (x : E)) ^ 2) (Real.cos r ^ 2) hA (cap_measurable a r)
    (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
    (equal_cap_measure mu hd a r hr A hmass)
  · intro x hx
    exact ((cap_threshold a r hr x).mp hx).le
  · intro x hx
    exact le_of_not_gt (fun h => hx ((cap_threshold a r hr x).mpr h))

theorem moment_equality (hd : 1 < Module.finrank ℝ E) (a : Sphere E) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) (A : Set (Sphere E)) (hA : MeasurableSet A)
    (hmass : area mu A = capMass (Module.finrank ℝ E - 2) r)
    (heq : (∫ x in A, (inner ℝ (a : E) (x : E)) ^ 2 ∂probability mu) =
      capMoment (Module.finrank ℝ E - 2) r) : A =ᵐ[probability mu] cap a r := by
  apply superlevel_equality_ae (probability mu) A (cap a r)
    (fun x => (inner ℝ (a : E) (x : E)) ^ 2) (Real.cos r ^ 2) hA (cap_measurable a r)
    (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
    (equal_cap_measure mu hd a r hr A hmass)
  · intro x hx
    exact ((cap_threshold a r hr x).mp hx).le
  · intro x hx
    exact le_of_not_gt (fun h => hx ((cap_threshold a r hr x).mpr h))
  · exact heq.trans (cap_axial_moment mu hd a r hr).symm
  · have hn := SmallShadowCaps.abs_latitude_null mu hd a (Real.cos r)
    have hae : ∀ᵐ x : Sphere E ∂probability mu, |inner ℝ (a : E) (x : E)| ≠ Real.cos r := by
      simpa only [ae_iff, not_not] using hn
    filter_upwards [hae] with x hx
    intro h
    apply hx
    have hc : 0 ≤ Real.cos r := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hr.1,Real.pi_pos],hr.2⟩
    nlinarith [sq_abs (inner ℝ (a : E) (x : E)),abs_nonneg (inner ℝ (a : E) (x : E))]

end ShadowVerification.SphericalMomentBound
#print axioms ShadowVerification.SphericalMomentBound.cap_threshold
#print axioms ShadowVerification.SphericalMomentBound.equal_cap_measure
#print axioms ShadowVerification.SphericalMomentBound.moment_maximal
#print axioms ShadowVerification.SphericalMomentBound.moment_equality

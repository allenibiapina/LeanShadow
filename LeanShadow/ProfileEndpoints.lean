import LeanShadow.ProfileConcavity
import LeanShadow.SmallShadowCaps

/-! # Endpoint continuity and the elementary lower profile bound

The incidence marginals imply that the masses of avoiding sets sum to at
most one. Consequently p ≤ f(p), including f(1)=1. The small-cap construction
handles continuity at zero; squeezing handles continuity at one.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.ProfileEndpoints
open Spherical Profile

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

theorem avoiding_mass_bound (hd : 1 < Module.finrank ℝ E)
    (A B : Set (Sphere E)) (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Avoids A B) :
    area mu A + area mu B ≤ 1 := by
  let I := OrthogonalIncidence.realization mu hd
  let nu := I.measure
  let : IsProbabilityMeasure nu := by
    dsimp [nu,I,OrthogonalIncidence.realization]
    infer_instance
  let S : Set (Sphere E × Sphere E) := Prod.fst ⁻¹' A
  let T : Set (Sphere E × Sphere E) := Prod.snd ⁻¹' B
  have hz : nu (S ∩ T) = 0 := IncidenceRounding.incidence_zero_of_avoids nu
    (fun x y : Sphere E => inner ℝ (x : E) (y : E) = 0) I.orthogonal A B hAB
  have hS : nu.real S = area mu A := I.firstMarginal.measureReal_preimage hA.nullMeasurableSet
  have hT : nu.real T = area mu B := I.secondMarginal.measureReal_preimage hB.nullMeasurableSet
  have he := measureReal_union_add_inter (μ := nu) (s := S) (hB.preimage measurable_snd)
  have hzero : nu.real (S ∩ T) = 0 := by simp only [measureReal_def,hz,ENNReal.toReal_zero]
  rw [hzero,add_zero,hS,hT] at he
  rw [← he]
  exact (measureReal_mono (subset_univ _)).trans_eq (by simp)

theorem mass_le_shadow (hd : 1 < Module.finrank ℝ E)
    (A : Set (Sphere E)) (hA : MeasurableSet A) : area mu A ≤ area mu (shadow A) := by
  have h := avoiding_mass_bound mu hd A (avoidingPartner mu A) hA
    (avoidingPartner_measurable mu A) (avoids_avoidingPartner mu A)
  rw [avoidingPartner_area mu A] at h
  linarith

theorem mass_le_profile (hd : 1 < Module.finrank ℝ E) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    p ≤ profile mu p := by
  apply le_csInf (ProfileSequence.shadowValues_nonempty mu hd p hp.1 hp.2)
  rintro q ⟨A,hA,_,hmA,hmS⟩
  simpa only [hmA,hmS] using mass_le_shadow mu hd A hA

theorem profile_one (hd : 1 < Module.finrank ℝ E) : profile mu 1 = 1 :=
  le_antisymm (ProfileSequence.profile_bounds mu hd 1 zero_le_one le_rfl).2
    (mass_le_profile mu hd 1 ⟨zero_le_one,le_rfl⟩)

theorem continuous_zero (hd : 1 < Module.finrank ℝ E) :
    ContinuousWithinAt (profile mu) (Icc 0 1) 0 := by
  have hzero : profile mu 0 = 0 := by
    have h := (Attainment.empty_optimizer mu).minimal
    simpa [shadow,area] using h.symm
  apply Metric.continuousWithinAt_iff.mpr
  intro eps heps
  obtain ⟨r,hr,hrp⟩ := SmallShadowCaps.profile_small_near_zero mu hd eps heps
  refine ⟨r,hr,fun p hp hdist => ?_⟩
  rw [hzero,Real.dist_eq,sub_zero,abs_of_nonneg (ProfileSequence.profile_bounds mu hd p hp.1 hp.2).1]
  apply hrp p hp.1
  have h : |p| < r := by simpa only [Real.dist_eq,sub_zero] using hdist
  exact (le_abs_self p).trans h.le

theorem continuous_one (hd : 1 < Module.finrank ℝ E) :
    ContinuousWithinAt (profile mu) (Icc 0 1) 1 := by
  apply Metric.continuousWithinAt_iff.mpr
  intro eps heps
  refine ⟨eps,heps,fun p hp hdist => ?_⟩
  rw [profile_one mu hd,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr
    (ProfileSequence.profile_bounds mu hd p hp.1 hp.2).2)]
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hp.2)] at hdist
  linarith [mass_le_profile mu hd p hp]

end ShadowVerification.ProfileEndpoints
#print axioms ShadowVerification.ProfileEndpoints.avoiding_mass_bound
#print axioms ShadowVerification.ProfileEndpoints.mass_le_shadow
#print axioms ShadowVerification.ProfileEndpoints.mass_le_profile
#print axioms ShadowVerification.ProfileEndpoints.profile_one
#print axioms ShadowVerification.ProfileEndpoints.continuous_zero
#print axioms ShadowVerification.ProfileEndpoints.continuous_one

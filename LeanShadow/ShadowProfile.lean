import LeanShadow.AntipodalGeometry
import LeanShadow.DualAreaRegularity
import Mathlib.MeasureTheory.Measure.Real

/-! # The actual projective shadow profile and optimal avoiding pairs

The admissible sets are Borel antipodal subsets of the actual sphere; their
normalized spherical measure is the projective normalization. The profile
is the infimum of their literal shadow outer measures at a fixed mass.
No formula, regularity, attainment, or differential inequality is built into
this definition. All uses of the infimum below have an actual competitor.

A Borel hull of the shadow has exactly its outer measure. Its complement
is a Borel avoiding partner of the complementary mass. Symmetrization makes
that partner antipodal; feasibility proves that its mass cannot increase.
Thus every given optimizer produces an actual optimal avoiding pair.
This does not assert existence of an optimizer at every mass.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace ShadowVerification.Profile
open Spherical Antipodal
open _root_.ShadowVerification.Dual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

def shadowValues (p : ℝ) : Set ℝ :=
  {q | ∃ A : Set (Sphere E), MeasurableSet A ∧ IsAntipodal A ∧
    area mu A = p ∧ area mu (shadow A) = q}

noncomputable def profile (p : ℝ) : ℝ := sInf (shadowValues mu p)

structure IsOptimizer (p : ℝ) (A : Set (Sphere E)) : Prop where
  measurable : MeasurableSet A
  antipodal : IsAntipodal A
  mass : area mu A = p
  minimal : area mu (shadow A) = profile mu p

structure IsOptimalPair (p : ℝ) (A B : Set (Sphere E)) : Prop where
  measurable_left : MeasurableSet A
  measurable_right : MeasurableSet B
  antipodal_left : IsAntipodal A
  antipodal_right : IsAntipodal B
  mass_left : area mu A = p
  avoids : Avoids A B
  mass_right : area mu B = 1 - profile mu p

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] [mu.IsAddHaarMeasure] in
theorem shadowValues_bddBelow (p : ℝ) : BddBelow (shadowValues mu p) := by
  refine ⟨0, ?_⟩
  rintro q ⟨A, _, _, _, rfl⟩
  exact area_nonneg mu (shadow A)

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] [mu.IsAddHaarMeasure] in
theorem shadow_mem_values (A : Set (Sphere E)) (hA : MeasurableSet A) (hanti : IsAntipodal A) :
    area mu (shadow A) ∈ shadowValues mu (area mu A) :=
  ⟨A, hA, hanti, rfl, rfl⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] [mu.IsAddHaarMeasure] in
theorem profile_le_shadow (A : Set (Sphere E)) (hA : MeasurableSet A) (hanti : IsAntipodal A) :
    profile mu (area mu A) ≤ area mu (shadow A) :=
  csInf_le (shadowValues_bddBelow mu _) (shadow_mem_values mu A hA hanti)

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] [mu.IsAddHaarMeasure] in
theorem profile_nonneg_at_competitor (A : Set (Sphere E))
    (hA : MeasurableSet A) (hanti : IsAntipodal A) : 0 ≤ profile mu (area mu A) := by
  apply le_csInf ⟨_, shadow_mem_values mu A hA hanti⟩
  rintro q ⟨D, _, _, _, rfl⟩
  exact area_nonneg mu (shadow D)

theorem profile_le_one_at_competitor (A : Set (Sphere E))
    (hA : MeasurableSet A) (hanti : IsAntipodal A) : profile mu (area mu A) ≤ 1 :=
  (profile_le_shadow mu A hA hanti).trans (area_le_one mu (shadow A))

/-- Only the second set must be measurable for this literal-shadow bound. -/
theorem avoiding_shadow_bound (A B : Set (Sphere E)) (hB : MeasurableSet B) (hAB : Avoids A B) :
    area mu B + area mu (shadow A) ≤ 1 := by
  have hsub : shadow A ⊆ Bᶜ := by
    rintro y ⟨x, hx, hxy⟩ hy
    exact hAB x hx y hy hxy
  have hh : area mu (shadow A) ≤ area mu Bᶜ := measureReal_mono hsub
  have hc : area mu Bᶜ = 1 - area mu B := by
    unfold area
    rw [measureReal_compl hB, probReal_univ]
  rw [hc] at hh
  linarith

/-- Every actual admissible pair lies below the defined optimal profile. -/
theorem feasible_profile_bound (A B : Set (Sphere E))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hanti : IsAntipodal A) (hAB : Avoids A B) :
    area mu B + profile mu (area mu A) ≤ 1 := by
  have hh := avoiding_shadow_bound mu A B hB hAB
  have hf := profile_le_shadow mu A hA hanti
  linarith

theorem transformed_feasible_bound (A B : Set (Sphere E))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hanti : IsAntipodal A) (hAB : Avoids A B)
    (T : E ≃L[ℝ] E) :
    transformedArea mu B (dualEquiv T) + profile mu (transformedArea mu A T) ≤ 1 :=
  feasible_profile_bound mu _ _ (measurable_action_image T A hA)
    (measurable_action_image (dualEquiv T) B hB) (antipodal_action_image T A hanti)
    (avoids_dual_images T A B hAB)

noncomputable def avoidanceCore (A : Set (Sphere E)) : Set (Sphere E) :=
  (toMeasurable (probability mu) (shadow A))ᶜ

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] [mu.IsAddHaarMeasure] in
theorem avoidanceCore_measurable (A : Set (Sphere E)) : MeasurableSet (avoidanceCore mu A) :=
  (measurableSet_toMeasurable _ _).compl

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] [mu.IsAddHaarMeasure] in
theorem avoids_avoidanceCore (A : Set (Sphere E)) : Avoids A (avoidanceCore mu A) := by
  intro x hx y hy hxy
  exact hy (subset_toMeasurable (probability mu) (shadow A) ⟨x, hx, hxy⟩)

theorem avoidanceCore_area (A : Set (Sphere E)) :
    area mu (avoidanceCore mu A) = 1 - area mu (shadow A) := by
  unfold avoidanceCore area
  rw [measureReal_compl (measurableSet_toMeasurable _ _), probReal_univ]
  simp only [measureReal_def, measure_toMeasurable]

noncomputable def avoidingPartner (A : Set (Sphere E)) : Set (Sphere E) :=
  symmetrize (avoidanceCore mu A)

omit [FiniteDimensional ℝ E] [Nontrivial E] [mu.IsAddHaarMeasure] in
theorem avoidingPartner_measurable (A : Set (Sphere E)) : MeasurableSet (avoidingPartner mu A) :=
  symmetrize_measurable _ (avoidanceCore_measurable mu A)

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] [mu.IsAddHaarMeasure] in
theorem avoidingPartner_antipodal (A : Set (Sphere E)) : IsAntipodal (avoidingPartner mu A) :=
  symmetrize_antipodal _

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] [mu.IsAddHaarMeasure] in
theorem avoids_avoidingPartner (A : Set (Sphere E)) : Avoids A (avoidingPartner mu A) :=
  avoids_symmetrize_right _ _ (avoids_avoidanceCore mu A)

theorem avoidingPartner_area (A : Set (Sphere E)) :
    area mu (avoidingPartner mu A) = 1 - area mu (shadow A) := by
  have hlo : area mu (avoidanceCore mu A) ≤ area mu (avoidingPartner mu A) :=
    measureReal_mono (subset_symmetrize _)
  rw [avoidanceCore_area mu A] at hlo
  have hhi := avoiding_shadow_bound mu A _ (avoidingPartner_measurable mu A)
    (avoids_avoidingPartner mu A)
  linarith

/-- The partner is constructed from a given optimizer, without an attainment axiom. -/
theorem optimalPair_of_optimizer (p : ℝ) (A : Set (Sphere E)) (hA : IsOptimizer mu p A) :
    IsOptimalPair mu p A (avoidingPartner mu A) where
  measurable_left := hA.measurable
  measurable_right := avoidingPartner_measurable mu A
  antipodal_left := hA.antipodal
  antipodal_right := avoidingPartner_antipodal mu A
  mass_left := hA.mass
  avoids := avoids_avoidingPartner mu A
  mass_right := by rw [avoidingPartner_area mu A, hA.minimal]

/-- Saturation of the profile budget implies actual shadow optimality. -/
theorem optimizer_of_optimalPair (p : ℝ) (A B : Set (Sphere E)) (h : IsOptimalPair mu p A B) :
    IsOptimizer mu p A := by
  refine ⟨h.measurable_left, h.antipodal_left, h.mass_left, ?_⟩
  have hlo := profile_le_shadow mu A h.measurable_left h.antipodal_left
  rw [h.mass_left] at hlo
  have hhi := avoiding_shadow_bound mu A B h.measurable_right h.avoids
  rw [h.mass_right] at hhi
  linarith

end ShadowVerification.Profile
#print axioms ShadowVerification.Profile.shadowValues_bddBelow
#print axioms ShadowVerification.Profile.shadow_mem_values
#print axioms ShadowVerification.Profile.profile_le_shadow
#print axioms ShadowVerification.Profile.profile_nonneg_at_competitor
#print axioms ShadowVerification.Profile.profile_le_one_at_competitor
#print axioms ShadowVerification.Profile.avoiding_shadow_bound
#print axioms ShadowVerification.Profile.feasible_profile_bound
#print axioms ShadowVerification.Profile.transformed_feasible_bound
#print axioms ShadowVerification.Profile.avoidanceCore_measurable
#print axioms ShadowVerification.Profile.avoids_avoidanceCore
#print axioms ShadowVerification.Profile.avoidanceCore_area
#print axioms ShadowVerification.Profile.avoidingPartner_measurable
#print axioms ShadowVerification.Profile.avoidingPartner_antipodal
#print axioms ShadowVerification.Profile.avoids_avoidingPartner
#print axioms ShadowVerification.Profile.avoidingPartner_area
#print axioms ShadowVerification.Profile.optimalPair_of_optimizer
#print axioms ShadowVerification.Profile.optimizer_of_optimalPair

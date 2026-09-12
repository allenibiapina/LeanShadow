import LeanShadow.ShadowRegularity

/-! # The sharp literal-shadow bound for completed-measurable representatives

Inner area is the supremum of measures of actual compact subsets. No
measurability of the literal shadow of the input set is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.SharpShadow
open Spherical Antipodal ShadowRegularity CapFunctions CapRadius CapModel

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]
  (hdim : 2 < Module.finrank ℝ (EuclideanSpace ℝ n))

include hdim

theorem shadow_inequality (A : Set (Sphere (EuclideanSpace ℝ n)))
    (hA : NullMeasurableSet A (probability mu)) (hanti : IsAntipodal A) :
    model (Fintype.card n - 2) (area mu A) ≤ innerArea mu (shadow A) := by
  obtain ⟨B,hBA,_,hB,hBanti,hBAe,hsh⟩ := exists_antipodal_core mu A hA hanti
  have hmass : area mu B = area mu A := congrArg ENNReal.toReal (measure_congr hBAe)
  have hlo := OptimizerRigidity.borel_shadow_bound mu hdim B hB hBanti
  rw [hmass] at hlo
  exact hlo.trans (measurable_area_le_innerArea mu hsh (shadow_mono hBA))

theorem shadow_equality (A : Set (Sphere (EuclideanSpace ℝ n)))
    (hA : NullMeasurableSet A (probability mu)) (hanti : IsAntipodal A)
    (hp : area mu A ∈ Ioo (0 : ℝ) 1)
    (heq : innerArea mu (shadow A) = model (Fintype.card n - 2) (area mu A)) :
    ∃ a : Sphere (EuclideanSpace ℝ n),
      A =ᵐ[probability mu] SphericalCaps.cap a (radius (Fintype.card n - 2) (area mu A)) := by
  obtain ⟨B,hBA,_,hB,hBanti,hBAe,hsh⟩ := exists_antipodal_core mu A hA hanti
  have hmass : area mu B = area mu A := congrArg ENNReal.toReal (measure_congr hBAe)
  have hbeq : area mu (shadow B) = model (Fintype.card n - 2) (area mu B) := by
    apply le_antisymm
    · rw [hmass,← heq]
      exact measurable_area_le_innerArea mu hsh (shadow_mono hBA)
    · exact OptimizerRigidity.borel_shadow_bound mu hdim B hB hBanti
  obtain ⟨a,ha⟩ := OptimizerRigidity.borel_shadow_equality mu hdim B hB hBanti (hmass ▸ hp) hbeq
  rw [hmass] at ha
  exact ⟨a,hBAe.symm.trans ha⟩

omit [DecidableEq n] in
theorem cap_attains (a : Sphere (EuclideanSpace ℝ n)) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) :
    innerArea mu (shadow (SphericalCaps.cap a r)) =
      model (Fintype.card n - 2) (area mu (SphericalCaps.cap a r)) := by
  rw [innerArea_eq_area mu _ (CapShadow.shadow_cap_measurable a r hr).nullMeasurableSet,
    CapShadow.shadow_cap_area mu (by omega) a r hr,SphericalCaps.cap_area mu (by omega) a r hr]
  simp only [finrank_euclideanSpace]
  exact (model_mass _ r hr).symm

theorem arbitrary_shadow_inequality (A : Set (Sphere (EuclideanSpace ℝ n)))
    (hA : NullMeasurableSet A (probability mu)) :
    model (Fintype.card n - 2) (area mu A) ≤ innerArea mu (shadow A) := by
  have hs := shadow_inequality mu hdim (symmetrize A) (symmetrize_nullMeasurable mu A hA)
    (symmetrize_antipodal A)
  rw [shadow_symmetrize] at hs
  have hm := (SharpProfile.model_strictMono (Fintype.card n - 2)).monotoneOn
    ⟨area_nonneg mu A,area_le_one mu A⟩
    ⟨area_nonneg mu (symmetrize A),area_le_one mu (symmetrize A)⟩
    (show area mu A ≤ area mu (symmetrize A) from measureReal_mono (subset_symmetrize A))
  exact hm.trans hs

theorem arbitrary_shadow_equality (A : Set (Sphere (EuclideanSpace ℝ n)))
    (hA : NullMeasurableSet A (probability mu)) (hp : area mu A ∈ Ioo (0 : ℝ) 1)
    (heq : innerArea mu (shadow A) = model (Fintype.card n - 2) (area mu A)) :
    ∃ a : Sphere (EuclideanSpace ℝ n),
      A =ᵐ[probability mu] SphericalCaps.cap a (radius (Fintype.card n - 2) (area mu A)) := by
  let B := symmetrize A
  have hB : NullMeasurableSet B (probability mu) := symmetrize_nullMeasurable mu A hA
  have hsh : shadow B = shadow A := shadow_symmetrize A
  have hmodel := shadow_inequality mu hdim B hB (symmetrize_antipodal A)
  rw [hsh,heq] at hmodel
  have hmass : area mu B = area mu A := by
    apply le_antisymm _ (measureReal_mono (subset_symmetrize A))
    by_contra! hlt
    exact (not_lt_of_ge hmodel) ((SharpProfile.model_strictMono (Fintype.card n - 2))
      ⟨hp.1.le,hp.2.le⟩ ⟨area_nonneg mu B,area_le_one mu B⟩ hlt)
  have hABe : A =ᵐ[probability mu] B := by
    apply ae_eq_of_subset_of_measure_ge (subset_symmetrize A) _ hA (measure_ne_top _ _)
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hmass.le
  obtain ⟨a,ha⟩ := shadow_equality mu hdim B hB (symmetrize_antipodal A)
    (hmass ▸ hp) (by rw [hsh,hmass]; exact heq)
  rw [hmass] at ha
  exact ⟨a,hABe.trans ha⟩

end ShadowVerification.SharpShadow
#print axioms ShadowVerification.SharpShadow.shadow_inequality
#print axioms ShadowVerification.SharpShadow.shadow_equality
#print axioms ShadowVerification.SharpShadow.cap_attains
#print axioms ShadowVerification.SharpShadow.arbitrary_shadow_inequality
#print axioms ShadowVerification.SharpShadow.arbitrary_shadow_equality

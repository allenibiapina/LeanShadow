import LeanShadow.CompactInnerMeasure
import LeanShadow.OptimizerRigidity

/-! # Compact literal shadows and inner approximation of representatives -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.ShadowRegularity
open Spherical Antipodal CompactInner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem shadow_mono {A B : Set (Sphere E)} (hAB : A ⊆ B) : shadow A ⊆ shadow B := by
  rintro y ⟨x,hx,hxy⟩
  exact ⟨x,hAB hx,hxy⟩

theorem shadow_iUnion {ι : Type*} (A : ι → Set (Sphere E)) :
    shadow (⋃ i, A i) = ⋃ i, shadow (A i) := by
  ext y
  simp only [shadow,mem_ofPred_eq,mem_iUnion]
  aesop

variable [FiniteDimensional ℝ E]

theorem shadow_compact (A : Set (Sphere E)) (hA : IsCompact A) : IsCompact (shadow A) := by
  let R : Set (Sphere E × Sphere E) := {q | inner ℝ (q.1 : E) (q.2 : E) = 0}
  have hR : IsClosed R := isClosed_eq (by fun_prop) continuous_const
  have he : shadow A = Prod.snd '' ((A ×ˢ univ) ∩ R) := by
    ext y
    constructor
    · rintro ⟨x,hx,hxy⟩
      exact ⟨(x,y),⟨⟨hx,mem_univ _⟩,hxy⟩,rfl⟩
    · rintro ⟨⟨x,z⟩,⟨⟨hx,_⟩,hxy⟩,rfl⟩
      exact ⟨x,hx,hxy⟩
  rw [he]
  exact ((hA.prod isCompact_univ).inter_right hR).image continuous_snd

theorem shadow_sigmaCompact (A : Set (Sphere E)) (hA : IsSigmaCompact A) :
    IsSigmaCompact (shadow A) := by
  obtain ⟨K,hK,rfl⟩ := hA
  rw [shadow_iUnion]
  exact ⟨fun n => shadow (K n),fun n => shadow_compact _ (hK n),rfl⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem symmetrize_sigmaCompact (A : Set (Sphere E)) (hA : IsSigmaCompact A) :
    IsSigmaCompact (symmetrize A) := by
  obtain ⟨K,hK,rfl⟩ := hA
  refine ⟨fun n => symmetrize (K n),fun n => (hK n).union ((hK n).image antipode_continuous),?_⟩
  simp only [symmetrize,image_iUnion,iUnion_union_distrib]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem antipode_image_eq_preimage (A : Set (Sphere E)) : antipode '' A = antipode ⁻¹' A := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa only [mem_preimage,antipode_twice] using hy
  · intro hx
    exact ⟨antipode x,hx,antipode_twice x⟩

variable [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

def innerArea (A : Set (Sphere E)) : ℝ := (innerMeasure (probability mu) A).toReal

theorem innerMeasure_ne_top (A : Set (Sphere E)) : innerMeasure (probability mu) A ≠ ∞ :=
  ne_top_of_le_ne_top (measure_ne_top _ _) (innerMeasure_le _ _)

theorem innerArea_mono {A B : Set (Sphere E)} (hAB : A ⊆ B) : innerArea mu A ≤ innerArea mu B :=
  ENNReal.toReal_mono (innerMeasure_ne_top mu B) (innerMeasure_mono _ hAB)

theorem innerArea_le_area (A : Set (Sphere E)) : innerArea mu A ≤ area mu A :=
  ENNReal.toReal_mono (measure_ne_top _ _) (innerMeasure_le _ _)

theorem innerArea_eq_area (A : Set (Sphere E)) (hA : NullMeasurableSet A (probability mu)) :
    innerArea mu A = area mu A := by
  rw [innerArea,innerMeasure_eq _ A hA]
  rfl

theorem measurable_area_le_innerArea {B A : Set (Sphere E)} (hB : MeasurableSet B) (hBA : B ⊆ A) :
    area mu B ≤ innerArea mu A := by
  rw [← innerArea_eq_area mu B hB.nullMeasurableSet]
  exact innerArea_mono mu hBA

theorem symmetrize_nullMeasurable (A : Set (Sphere E)) (hA : NullMeasurableSet A (probability mu)) :
    NullMeasurableSet (symmetrize A) (probability mu) := by
  unfold symmetrize
  rw [antipode_image_eq_preimage]
  exact hA.union (hA.preimage (SphericalCaps.measurePreserving_antipode mu).quasiMeasurePreserving)

theorem exists_antipodal_core (A : Set (Sphere E)) (hA : NullMeasurableSet A (probability mu))
    (hanti : IsAntipodal A) :
    ∃ B : Set (Sphere E), B ⊆ A ∧ IsSigmaCompact B ∧ MeasurableSet B ∧ IsAntipodal B ∧
      B =ᵐ[probability mu] A ∧ MeasurableSet (shadow B) := by
  obtain ⟨C,hCA,hC,hCAe⟩ := exists_sigmaCompact_subset_ae_eq (probability mu) A hA
  have hsub : symmetrize C ⊆ A := by
    rintro x (hx | ⟨y,hy,rfl⟩)
    · exact hCA hx
    · exact hanti y (hCA hy)
  have hB := symmetrize_sigmaCompact C hC
  refine ⟨symmetrize C,hsub,hB,sigmaCompact_measurable hB,symmetrize_antipodal C,?_,
    sigmaCompact_measurable (shadow_sigmaCompact _ hB)⟩
  filter_upwards [hCAe] with x hx
  exact propext ⟨fun h => hsub h,fun h => subset_symmetrize C (Eq.mp hx.symm h)⟩

end ShadowVerification.ShadowRegularity
#print axioms ShadowVerification.ShadowRegularity.shadow_mono
#print axioms ShadowVerification.ShadowRegularity.shadow_iUnion
#print axioms ShadowVerification.ShadowRegularity.shadow_compact
#print axioms ShadowVerification.ShadowRegularity.shadow_sigmaCompact
#print axioms ShadowVerification.ShadowRegularity.symmetrize_sigmaCompact
#print axioms ShadowVerification.ShadowRegularity.antipode_image_eq_preimage
#print axioms ShadowVerification.ShadowRegularity.innerMeasure_ne_top
#print axioms ShadowVerification.ShadowRegularity.innerArea_mono
#print axioms ShadowVerification.ShadowRegularity.innerArea_le_area
#print axioms ShadowVerification.ShadowRegularity.innerArea_eq_area
#print axioms ShadowVerification.ShadowRegularity.measurable_area_le_innerArea
#print axioms ShadowVerification.ShadowRegularity.symmetrize_nullMeasurable
#print axioms ShadowVerification.ShadowRegularity.exists_antipodal_core

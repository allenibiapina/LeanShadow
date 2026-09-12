import LeanShadow.DoubleCap
import Mathlib.Topology.Separation.Hausdorff

/-! # The antipodal projective quotient and its normalized measure -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Topology ENNReal
namespace ShadowVerification.ProjectiveQuotient
open Spherical Antipodal ShadowRegularity CompactInner

variable {E : Type*} [NormedAddCommGroup E]

def antipodalSetoid (E : Type*) [NormedAddCommGroup E] : Setoid (Sphere E) where
  r x y := x = y ∨ x = antipode y
  iseqv := by
    constructor
    · intro x; exact Or.inl rfl
    · intro x y h
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (by rw [h,antipode_twice])
    · intro x y z hxy hyz
      rcases hxy with rfl | hxy
      · exact hyz
      rcases hyz with rfl | hyz
      · exact Or.inr hxy
      · exact Or.inl (by rw [hxy,hyz,antipode_twice])

abbrev Space (E : Type*) [NormedAddCommGroup E] := Quotient (antipodalSetoid E)

def project (x : Sphere E) : Space E := Quotient.mk _ x

theorem project_eq_iff (x y : Sphere E) : project x = project y ↔ x = y ∨ x = antipode y :=
  Quotient.eq

theorem project_antipode (x : Sphere E) : project (antipode x) = project x :=
  (project_eq_iff _ _).mpr (Or.inr rfl)

theorem project_surjective : Function.Surjective (project (E := E)) := Quotient.mk_surjective

theorem project_continuous : Continuous (project (E := E)) := continuous_quotient_mk'

theorem project_preimage_image (A : Set (Sphere E)) : project ⁻¹' (project '' A) = symmetrize A := by
  ext x
  constructor
  · rintro ⟨y,hy,heq⟩
    rcases (project_eq_iff y x).mp heq with rfl | heq
    · exact Or.inl hy
    · exact Or.inr ⟨y,hy,by rw [heq,antipode_twice]⟩
  · rintro (hx | ⟨y,hy,rfl⟩)
    · exact ⟨x,hx,rfl⟩
    · exact ⟨y,hy,(project_antipode y).symm⟩

theorem project_isOpenMap : IsOpenMap (project (E := E)) := by
  intro U hU
  apply isQuotientMap_quotient_mk'.isCoinducing.isOpen_preimage.mp
  change IsOpen (project ⁻¹' (project '' U))
  rw [project_preimage_image]
  exact hU.union (antipodeHomeomorph.isOpenMap _ hU)

theorem project_openQuotient : IsOpenQuotientMap (project (E := E)) := by
  exact ⟨project_surjective,project_continuous,project_isOpenMap⟩

instance spaceT2 : T2Space (Space E) := by
  apply (t2Space_iff_of_isOpenQuotientMap project_openQuotient).mpr
  have he : {q : Sphere E × Sphere E | project q.1 = project q.2} =
      {q | q.1 = q.2} ∪ {q | q.1 = antipode q.2} := by
    ext q
    exact project_eq_iff _ _
  rw [he]
  exact (isClosed_eq continuous_fst continuous_snd).union
    (isClosed_eq continuous_fst (antipode_continuous.comp continuous_snd))

instance spaceMeasurable : MeasurableSpace (Space E) := borel (Space E)
instance spaceBorel : BorelSpace (Space E) := ⟨rfl⟩

theorem lift_antipodal (A : Set (Space E)) : IsAntipodal (project ⁻¹' A) := by
  intro x hx
  change project (antipode x) ∈ A
  rw [project_antipode]
  exact hx

variable [InnerProductSpace ℝ E]

def Orthogonal (p q : Space E) : Prop :=
  ∃ x y : Sphere E, project x = p ∧ project y = q ∧ inner ℝ (x : E) (y : E) = 0

def projectiveShadow (A : Set (Space E)) : Set (Space E) :=
  {q | ∃ p ∈ A, Orthogonal p q}

theorem orthogonal_project (x y : Sphere E) :
    Orthogonal (project x) (project y) ↔ inner ℝ (x : E) (y : E) = 0 := by
  constructor
  · rintro ⟨u,v,hu,hv,h⟩
    rcases (project_eq_iff u x).mp hu with rfl | rfl <;>
      rcases (project_eq_iff v y).mp hv with rfl | rfl <;>
      simpa only [antipode_coe,inner_neg_left,inner_neg_right,neg_eq_zero] using h
  · intro h
    exact ⟨x,y,rfl,rfl,h⟩

theorem lift_shadow (A : Set (Space E)) :
    project ⁻¹' projectiveShadow A = shadow (project ⁻¹' A) := by
  ext y
  constructor
  · rintro ⟨p,hp,h⟩
    obtain ⟨x,rfl⟩ := project_surjective p
    exact ⟨x,hp,(orthogonal_project x y).mp h⟩
  · rintro ⟨x,hx,hxy⟩
    exact ⟨project x,hx,(orthogonal_project x y).mpr hxy⟩

variable [MeasurableSpace E] [BorelSpace E] (mu : Measure E)

def volume : Measure (Space E) := (probability mu).map project

theorem project_measurePreserving : MeasurePreserving project (probability mu) (volume mu) :=
  ⟨project_continuous.measurable,rfl⟩

theorem lift_nullMeasurable (A : Set (Space E)) (hA : NullMeasurableSet A (volume mu)) :
    NullMeasurableSet (project ⁻¹' A) (probability mu) :=
  hA.preimage (project_measurePreserving mu).quasiMeasurePreserving

theorem volume_eq_lift (A : Set (Space E)) (hA : NullMeasurableSet A (volume mu)) :
    volume mu A = probability mu (project ⁻¹' A) :=
  Measure.map_apply₀ project_continuous.measurable.aemeasurable hA

theorem area_eq_lift (A : Set (Space E)) (hA : NullMeasurableSet A (volume mu)) :
    (volume mu).real A = area mu (project ⁻¹' A) := congrArg ENNReal.toReal (volume_eq_lift mu A hA)

variable [FiniteDimensional ℝ E]

theorem innerMeasure_eq_lift (A : Set (Space E)) :
    innerMeasure (volume mu) A = innerMeasure (probability mu) (project ⁻¹' A) := by
  apply le_antisymm
  · apply iSup_le
    intro K
    apply iSup_le
    intro hKA
    apply iSup_le
    intro hK
    rw [volume_eq_lift mu K hK.measurableSet.nullMeasurableSet]
    exact compact_le_innerMeasure _ (hK.isClosed.preimage project_continuous).isCompact
      (preimage_mono hKA)
  · apply iSup_le
    intro K
    apply iSup_le
    intro hKA
    apply iSup_le
    intro hK
    have hproj := hK.image project_continuous
    apply le_trans _ (compact_le_innerMeasure (volume mu) hproj (image_subset_iff.mpr hKA))
    rw [volume_eq_lift mu _ hproj.measurableSet.nullMeasurableSet]
    exact measure_mono (subset_preimage_image project K)

theorem innerArea_eq_lift (A : Set (Space E)) :
    (innerMeasure (volume mu) A).toReal = innerArea mu (project ⁻¹' A) :=
  congrArg ENNReal.toReal (innerMeasure_eq_lift mu A)

instance volumeProbability [Nontrivial E] [mu.IsAddHaarMeasure] : IsProbabilityMeasure (volume mu) :=
  Measure.isProbabilityMeasure_map project_continuous.measurable.aemeasurable

end ShadowVerification.ProjectiveQuotient
#print axioms ShadowVerification.ProjectiveQuotient.project_eq_iff
#print axioms ShadowVerification.ProjectiveQuotient.project_antipode
#print axioms ShadowVerification.ProjectiveQuotient.project_surjective
#print axioms ShadowVerification.ProjectiveQuotient.project_continuous
#print axioms ShadowVerification.ProjectiveQuotient.project_preimage_image
#print axioms ShadowVerification.ProjectiveQuotient.project_isOpenMap
#print axioms ShadowVerification.ProjectiveQuotient.project_openQuotient
#print axioms ShadowVerification.ProjectiveQuotient.lift_antipodal
#print axioms ShadowVerification.ProjectiveQuotient.orthogonal_project
#print axioms ShadowVerification.ProjectiveQuotient.lift_shadow
#print axioms ShadowVerification.ProjectiveQuotient.project_measurePreserving
#print axioms ShadowVerification.ProjectiveQuotient.lift_nullMeasurable
#print axioms ShadowVerification.ProjectiveQuotient.volume_eq_lift
#print axioms ShadowVerification.ProjectiveQuotient.area_eq_lift
#print axioms ShadowVerification.ProjectiveQuotient.innerMeasure_eq_lift
#print axioms ShadowVerification.ProjectiveQuotient.innerArea_eq_lift

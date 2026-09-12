import LeanShadow.ProjectiveQuotient
import LeanShadow.CapExtremizers

/-! # The sharp shadow theorem on the actual antipodal quotient

The projective measure is the pushforward of normalized spherical measure.
All sets in the main statements are measurable for its completion. The
shadow is the literal existential orthogonality shadow on the quotient.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.ProjectiveShadow
open Spherical Antipodal CompactInner ShadowRegularity ProjectiveQuotient
open CapFunctions CapRadius CapModel CapExtremizers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def cap (a : Sphere E) (r : ℝ) : Set (Space E) := project '' closedCap a r

theorem cap_lift (a : Sphere E) (r : ℝ) : project ⁻¹' cap a r = closedCap a r := by
  rw [cap,project_preimage_image]
  ext x
  constructor
  · rintro (hx | ⟨y,hy,rfl⟩)
    · exact hx
    · exact closedCap_antipodal a r y hy
  · exact fun hx => Or.inl hx

variable [FiniteDimensional ℝ E]

theorem cap_compact (a : Sphere E) (r : ℝ) : IsCompact (cap a r) :=
  (closedCap_closed a r).isCompact.image project_continuous

variable [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

theorem cap_mass (hd : 1 < Module.finrank ℝ E) (a : Sphere E) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) :
    (ProjectiveQuotient.volume mu).real (cap a r) = capMass (Module.finrank ℝ E - 2) r := by
  rw [area_eq_lift mu _ (cap_compact a r).measurableSet.nullMeasurableSet,cap_lift]
  exact closedCap_mass mu hd a r hr

omit [Nontrivial E] [mu.IsAddHaarMeasure] in
theorem cap_ae_of_lift (A : Set (Space E)) (hA : NullMeasurableSet A (ProjectiveQuotient.volume mu))
    (a : Sphere E) (r : ℝ)
    (heq : project ⁻¹' A =ᵐ[probability mu] closedCap a r) :
    A =ᵐ[ProjectiveQuotient.volume mu] cap a r := by
  have hcap := (cap_compact a r).measurableSet.nullMeasurableSet (μ := ProjectiveQuotient.volume mu)
  apply ae_eq_set.mpr
  constructor
  · rw [volume_eq_lift mu _ (hA.diff hcap),preimage_sdiff,cap_lift]
    exact (ae_eq_set.mp heq).1
  · rw [volume_eq_lift mu _ (hcap.diff hA),preimage_sdiff,cap_lift]
    exact (ae_eq_set.mp heq).2

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]

theorem sharp_shadow_inequality (nu : Measure (EuclideanSpace ℝ n)) [nu.IsAddHaarMeasure]
    (hdim : 2 < Module.finrank ℝ (EuclideanSpace ℝ n)) (A : Set (Space (EuclideanSpace ℝ n)))
    (hA : NullMeasurableSet A (ProjectiveQuotient.volume nu)) :
    model (Fintype.card n - 2) ((ProjectiveQuotient.volume nu).real A) ≤
      (innerMeasure (ProjectiveQuotient.volume nu) (projectiveShadow A)).toReal := by
  rw [area_eq_lift nu A hA,innerArea_eq_lift,lift_shadow]
  exact SharpShadow.shadow_inequality nu hdim _ (lift_nullMeasurable nu A hA) (lift_antipodal A)

theorem sharp_shadow_equality (nu : Measure (EuclideanSpace ℝ n)) [nu.IsAddHaarMeasure]
    (hdim : 2 < Module.finrank ℝ (EuclideanSpace ℝ n)) (A : Set (Space (EuclideanSpace ℝ n)))
    (hA : NullMeasurableSet A (ProjectiveQuotient.volume nu))
    (hp : (ProjectiveQuotient.volume nu).real A ∈ Ioo (0 : ℝ) 1)
    (heq : (innerMeasure (ProjectiveQuotient.volume nu) (projectiveShadow A)).toReal =
      model (Fintype.card n - 2) ((ProjectiveQuotient.volume nu).real A)) :
    ∃ a : Sphere (EuclideanSpace ℝ n), A =ᵐ[ProjectiveQuotient.volume nu]
      cap a (radius (Fintype.card n - 2) ((ProjectiveQuotient.volume nu).real A)) := by
  have hm := area_eq_lift nu A hA
  rw [hm] at hp heq ⊢
  rw [innerArea_eq_lift,lift_shadow] at heq
  obtain ⟨a,ha⟩ := SharpShadow.shadow_equality nu hdim _ (lift_nullMeasurable nu A hA)
    (lift_antipodal A) hp heq
  refine ⟨a,cap_ae_of_lift nu A hA a _ ?_⟩
  exact ha.trans (closedCap_ae_eq_open nu (by omega) a _).symm

theorem caps_attain (nu : Measure (EuclideanSpace ℝ n)) [nu.IsAddHaarMeasure]
    (hdim : 2 < Module.finrank ℝ (EuclideanSpace ℝ n))
    (a : Sphere (EuclideanSpace ℝ n)) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) :
    (innerMeasure (ProjectiveQuotient.volume nu) (projectiveShadow (cap a r))).toReal =
      model (Fintype.card n - 2) ((ProjectiveQuotient.volume nu).real (cap a r)) := by
  rw [innerArea_eq_lift,lift_shadow,cap_lift,
    area_eq_lift nu _ (cap_compact a r).measurableSet.nullMeasurableSet,cap_lift]
  exact closedCap_attains nu hdim a r hr

end ShadowVerification.ProjectiveShadow
#print axioms ShadowVerification.ProjectiveShadow.cap_lift
#print axioms ShadowVerification.ProjectiveShadow.cap_compact
#print axioms ShadowVerification.ProjectiveShadow.cap_mass
#print axioms ShadowVerification.ProjectiveShadow.cap_ae_of_lift
#print axioms ShadowVerification.ProjectiveShadow.sharp_shadow_inequality
#print axioms ShadowVerification.ProjectiveShadow.sharp_shadow_equality
#print axioms ShadowVerification.ProjectiveShadow.caps_attain

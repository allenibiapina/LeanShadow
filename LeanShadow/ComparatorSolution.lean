import LeanShadow.ComparatorDefinitions
import LeanShadow.ProjectiveShadow

/-! # Main results in explicit geometric form

The radius is supplied together with its defining area equation, so the
statements expose the angular integrals directly. The challenge module is
never imported here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology ENNReal
namespace LeanShadow.Comparator

universe u

variable {n : Type u} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]
  (hdim : 2 < Module.finrank ℝ (EuclideanSpace ℝ n))

include hdim

/-- The sharp spherical shadow bound at the area of caps of radius `r`. -/
theorem sharp_shadow_inequality (A : Set (Sphere (EuclideanSpace ℝ n)))
    (hA : NullMeasurableSet A (probability mu)) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hmass : area mu A = capMass (Fintype.card n - 2) r) :
    beltMass (Fintype.card n - 2) r ≤ innerArea mu (shadow A) := by
  have h := ShadowVerification.SharpShadow.arbitrary_shadow_inequality mu hdim A hA
  have hm : ShadowVerification.Spherical.area mu A =
      ShadowVerification.CapFunctions.capMass (Fintype.card n - 2) r := hmass
  rw [hm, ShadowVerification.CapModel.model_mass _ r hr] at h
  exact h

/-- Equality at an interior mass forces agreement with opposite caps almost everywhere. -/
theorem sharp_shadow_equality (A : Set (Sphere (EuclideanSpace ℝ n)))
    (hA : NullMeasurableSet A (probability mu)) (hp : area mu A ∈ Ioo (0 : ℝ) 1)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hmass : area mu A = capMass (Fintype.card n - 2) r)
    (heq : innerArea mu (shadow A) = beltMass (Fintype.card n - 2) r) :
    ∃ a : Sphere (EuclideanSpace ℝ n), A =ᵐ[probability mu] cap a r := by
  have hm : ShadowVerification.Spherical.area mu A =
      ShadowVerification.CapFunctions.capMass (Fintype.card n - 2) r := hmass
  have he : ShadowVerification.ShadowRegularity.innerArea mu (ShadowVerification.Spherical.shadow A) =
      ShadowVerification.CapModel.model (Fintype.card n - 2) (ShadowVerification.Spherical.area mu A) := by
    rw [hm, ShadowVerification.CapModel.model_mass _ r hr]
    exact heq
  obtain ⟨a, ha⟩ := ShadowVerification.SharpShadow.arbitrary_shadow_equality mu hdim A hA hp he
  rw [hm, ShadowVerification.CapRadius.radius_mass _ r hr] at ha
  exact ⟨a, ha⟩

omit [DecidableEq n] in
/-- Open opposite caps realize both angular area formulas. -/
theorem caps_attain (a : Sphere (EuclideanSpace ℝ n)) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    area mu (cap a r) = capMass (Fintype.card n - 2) r ∧
    innerArea mu (shadow (cap a r)) = beltMass (Fintype.card n - 2) r := by
  constructor
  · have h := ShadowVerification.SphericalCaps.cap_area mu (by omega) a r hr
    rw [finrank_euclideanSpace] at h
    exact h
  · have h := ShadowVerification.SharpShadow.cap_attains mu hdim a r hr
    rw [ShadowVerification.SphericalCaps.cap_area mu (by omega) a r hr,
      finrank_euclideanSpace, ShadowVerification.CapModel.model_mass _ r hr] at h
    exact h

/-- Every completed-measurable set with no orthogonal pair has mass at most the double-cap mass. -/
theorem double_cap_bound (A : Set (Sphere (EuclideanSpace ℝ n)))
    (hA : NullMeasurableSet A (probability mu)) (hind : Avoids A A) :
    area mu A ≤ delta (Fintype.card n - 2) := by
  exact ShadowVerification.DoubleCap.double_cap_bound mu hdim A hA hind

/-- Every independent set of maximal mass agrees almost everywhere with opposite 45-degree caps. -/
theorem double_cap_equality (A : Set (Sphere (EuclideanSpace ℝ n)))
    (hA : NullMeasurableSet A (probability mu)) (hind : Avoids A A)
    (heq : area mu A = delta (Fintype.card n - 2)) :
    ∃ a : Sphere (EuclideanSpace ℝ n), A =ᵐ[probability mu] cap a (Real.pi / 4) := by
  exact ShadowVerification.DoubleCap.double_cap_equality mu hdim A hA hind heq

omit [DecidableEq n] in
/-- The maximum independent mass is attained by a measurable set. -/
theorem double_cap_attainment :
    ∃ A : Set (Sphere (EuclideanSpace ℝ n)), MeasurableSet A ∧ Avoids A A ∧
      area mu A = delta (Fintype.card n - 2) := by
  exact ShadowVerification.DoubleCap.double_cap_attainment mu hdim

/-- The double-cap conjecture as a greatest-element statement. -/
theorem double_cap_conjecture : IsGreatest (independentMasses mu) (delta (Fintype.card n - 2)) := by
  exact ShadowVerification.CapExtremizers.double_cap_conjecture mu hdim

/-- The extremal value equals the double-cap mass. -/
theorem alpha_eq_delta : alpha mu = delta (Fintype.card n - 2) := by
  exact ShadowVerification.CapExtremizers.alpha_eq_delta mu hdim

/-- The projective orthogonality shadow bound for completed-measurable sets. -/
theorem projective_shadow_inequality (A : Set (ProjectiveSpace (EuclideanSpace ℝ n)))
    (hA : NullMeasurableSet A (projectiveVolume mu)) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hmass : (projectiveVolume mu).real A = capMass (Fintype.card n - 2) r) :
    beltMass (Fintype.card n - 2) r ≤ (innerMeasure (projectiveVolume mu) (projectiveShadow A)).toReal := by
  have h := ShadowVerification.ProjectiveShadow.sharp_shadow_inequality mu hdim A hA
  have hm : (ShadowVerification.ProjectiveQuotient.volume mu).real A =
      ShadowVerification.CapFunctions.capMass (Fintype.card n - 2) r := hmass
  rw [hm, ShadowVerification.CapModel.model_mass _ r hr] at h
  exact h

/-- Projective equality forces a projective cap almost everywhere. -/
theorem projective_shadow_equality (A : Set (ProjectiveSpace (EuclideanSpace ℝ n)))
    (hA : NullMeasurableSet A (projectiveVolume mu))
    (hp : (projectiveVolume mu).real A ∈ Ioo (0 : ℝ) 1)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hmass : (projectiveVolume mu).real A = capMass (Fintype.card n - 2) r)
    (heq : (innerMeasure (projectiveVolume mu) (projectiveShadow A)).toReal =
      beltMass (Fintype.card n - 2) r) :
    ∃ a : Sphere (EuclideanSpace ℝ n), A =ᵐ[projectiveVolume mu] projectiveCap a r := by
  have hm : (ShadowVerification.ProjectiveQuotient.volume mu).real A =
      ShadowVerification.CapFunctions.capMass (Fintype.card n - 2) r := hmass
  have he : (ShadowVerification.CompactInner.innerMeasure (ShadowVerification.ProjectiveQuotient.volume mu)
      (ShadowVerification.ProjectiveQuotient.projectiveShadow A)).toReal =
      ShadowVerification.CapModel.model (Fintype.card n - 2)
        ((ShadowVerification.ProjectiveQuotient.volume mu).real A) := by
    rw [hm, ShadowVerification.CapModel.model_mass _ r hr]
    exact heq
  obtain ⟨a, ha⟩ := ShadowVerification.ProjectiveShadow.sharp_shadow_equality mu hdim A hA hp he
  rw [hm, ShadowVerification.CapRadius.radius_mass _ r hr] at ha
  exact ⟨a, ha⟩

/-- Projective caps attain the sharp area and shadow formulas. -/
theorem projective_caps_attain (a : Sphere (EuclideanSpace ℝ n)) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (projectiveVolume mu).real (projectiveCap a r) = capMass (Fintype.card n - 2) r ∧
    (innerMeasure (projectiveVolume mu) (projectiveShadow (projectiveCap a r))).toReal =
      beltMass (Fintype.card n - 2) r := by
  constructor
  · have h := ShadowVerification.ProjectiveShadow.cap_mass mu (by omega) a r hr
    rw [finrank_euclideanSpace] at h
    exact h
  · have h := ShadowVerification.ProjectiveShadow.caps_attain mu hdim a r hr
    rw [ShadowVerification.ProjectiveShadow.cap_mass mu (by omega) a r hr,
      finrank_euclideanSpace, ShadowVerification.CapModel.model_mass _ r hr] at h
    exact h

omit hdim in
/-- On the ordinary sphere, the independent mass is at most `1 - sqrt 2 / 2`. -/
theorem s2_double_cap_bound (nu : Measure (EuclideanSpace ℝ (Fin 3))) [nu.IsAddHaarMeasure]
    (A : Set (Sphere (EuclideanSpace ℝ (Fin 3)))) (hA : NullMeasurableSet A (probability nu))
    (hind : Avoids A A) : area nu A ≤ 1 - Real.sqrt 2 / 2 := by
  exact ShadowVerification.CapExtremizers.s2_double_cap_bound nu A hA hind

end LeanShadow.Comparator
#print axioms LeanShadow.Comparator.sharp_shadow_inequality
#print axioms LeanShadow.Comparator.sharp_shadow_equality
#print axioms LeanShadow.Comparator.caps_attain
#print axioms LeanShadow.Comparator.double_cap_bound
#print axioms LeanShadow.Comparator.double_cap_equality
#print axioms LeanShadow.Comparator.double_cap_attainment
#print axioms LeanShadow.Comparator.double_cap_conjecture
#print axioms LeanShadow.Comparator.alpha_eq_delta
#print axioms LeanShadow.Comparator.projective_shadow_inequality
#print axioms LeanShadow.Comparator.projective_shadow_equality
#print axioms LeanShadow.Comparator.projective_caps_attain
#print axioms LeanShadow.Comparator.s2_double_cap_bound

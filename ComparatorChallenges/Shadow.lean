import Mathlib

/-! # Definitions for the independently stated shadow problems

Standalone reference for MAIN_STATEMENT.md, importing only Mathlib.
The theorem placeholders specify the challenge; they are not proofs.
Neither the proof entry point nor the submission imports this module.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Topology ENNReal
namespace LeanShadow.Comparator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Sphere (E : Type*) [NormedAddCommGroup E] := Metric.sphere (0 : E) 1

def shadow (A : Set (Sphere E)) : Set (Sphere E) :=
  {y | ∃ x ∈ A, inner ℝ (x : E) (y : E) = 0}

def Avoids (A B : Set (Sphere E)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, inner ℝ (x : E) (y : E) ≠ 0

def cap (a : Sphere E) (r : ℝ) : Set (Sphere E) :=
  {x | Real.cos r < |inner ℝ (a : E) (x : E)|}

def closedCap (a : Sphere E) (r : ℝ) : Set (Sphere E) :=
  {x | Real.cos r ≤ |inner ℝ (a : E) (x : E)|}

def antipode (x : Sphere E) : Sphere E :=
  ⟨-x, by simpa only [mem_sphere_zero_iff_norm, norm_neg] using x.property⟩

def antipodalSetoid (E : Type*) [NormedAddCommGroup E] : Setoid (Sphere E) where
  r x y := x = y ∨ x = antipode y
  iseqv := by
    have twice (x : Sphere E) : antipode (antipode x) = x := by
      apply Subtype.ext
      exact neg_neg (x : E)
    constructor
    · intro x; exact Or.inl rfl
    · intro x y h
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (by rw [h, twice])
    · intro x y z hxy hyz
      rcases hxy with rfl | hxy
      · exact hyz
      rcases hyz with rfl | hyz
      · exact Or.inr hxy
      · exact Or.inl (by rw [hxy, hyz, twice])

abbrev ProjectiveSpace (E : Type*) [NormedAddCommGroup E] := Quotient (antipodalSetoid E)

def project (x : Sphere E) : ProjectiveSpace E := Quotient.mk _ x

instance projectiveMeasurable : MeasurableSpace (ProjectiveSpace E) := borel (ProjectiveSpace E)

def Orthogonal (p q : ProjectiveSpace E) : Prop :=
  ∃ x y : Sphere E, project x = p ∧ project y = q ∧ inner ℝ (x : E) (y : E) = 0

def projectiveShadow (A : Set (ProjectiveSpace E)) : Set (ProjectiveSpace E) :=
  {q | ∃ p ∈ A, Orthogonal p q}

def projectiveCap (a : Sphere E) (r : ℝ) : Set (ProjectiveSpace E) := project '' closedCap a r

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def probability (mu : Measure E) : Measure (Sphere E) :=
  (mu.toSphere Set.univ)⁻¹ • mu.toSphere

def area (mu : Measure E) (A : Set (Sphere E)) : ℝ := (probability mu).real A

def projectiveVolume (mu : Measure E) : Measure (ProjectiveSpace E) :=
  (probability mu).map project

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

def innerMeasure (nu : Measure X) (A : Set X) : ℝ≥0∞ :=
  ⨆ (K : Set X) (_ : K ⊆ A) (_ : IsCompact K), nu K

def innerArea (mu : Measure E) (A : Set (Sphere E)) : ℝ :=
  (innerMeasure (probability mu) A).toReal

def sinPrimitive (m : ℕ) (r : ℝ) : ℝ := ∫ t in 0..r, Real.sin t ^ m
def cosPrimitive (m : ℕ) (r : ℝ) : ℝ := ∫ t in 0..r, Real.cos t ^ m
def normalizer (m : ℕ) : ℝ := (sinPrimitive m (Real.pi / 2))⁻¹
def capMass (m : ℕ) (r : ℝ) : ℝ := normalizer m * sinPrimitive m r
def beltMass (m : ℕ) (r : ℝ) : ℝ := normalizer m * cosPrimitive m r
def delta (m : ℕ) : ℝ := capMass m (Real.pi / 4)

def independentMasses (mu : Measure E) : Set ℝ :=
  {p | ∃ A : Set (Sphere E), NullMeasurableSet A (probability mu) ∧ Avoids A A ∧ area mu A = p}

def alpha (mu : Measure E) : ℝ := sSup (independentMasses mu)


universe u

variable {n : Type u} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]
  (hdim : 2 < Module.finrank ℝ (EuclideanSpace ℝ n))

include hdim

theorem sharp_shadow_inequality (A : Set (Sphere (EuclideanSpace ℝ n)))
    (hA : NullMeasurableSet A (probability mu)) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hmass : area mu A = capMass (Fintype.card n - 2) r) :
    beltMass (Fintype.card n - 2) r ≤ innerArea mu (shadow A) := by
  sorry

theorem sharp_shadow_equality (A : Set (Sphere (EuclideanSpace ℝ n)))
    (hA : NullMeasurableSet A (probability mu)) (hp : area mu A ∈ Ioo (0 : ℝ) 1)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hmass : area mu A = capMass (Fintype.card n - 2) r)
    (heq : innerArea mu (shadow A) = beltMass (Fintype.card n - 2) r) :
    ∃ a : Sphere (EuclideanSpace ℝ n), A =ᵐ[probability mu] cap a r := by
  sorry

omit [DecidableEq n] in
theorem caps_attain (a : Sphere (EuclideanSpace ℝ n)) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    area mu (cap a r) = capMass (Fintype.card n - 2) r ∧
    innerArea mu (shadow (cap a r)) = beltMass (Fintype.card n - 2) r := by
  sorry

theorem double_cap_bound (A : Set (Sphere (EuclideanSpace ℝ n)))
    (hA : NullMeasurableSet A (probability mu)) (hind : Avoids A A) :
    area mu A ≤ delta (Fintype.card n - 2) := by
  sorry

theorem double_cap_equality (A : Set (Sphere (EuclideanSpace ℝ n)))
    (hA : NullMeasurableSet A (probability mu)) (hind : Avoids A A)
    (heq : area mu A = delta (Fintype.card n - 2)) :
    ∃ a : Sphere (EuclideanSpace ℝ n), A =ᵐ[probability mu] cap a (Real.pi / 4) := by
  sorry

omit [DecidableEq n] in
theorem double_cap_attainment :
    ∃ A : Set (Sphere (EuclideanSpace ℝ n)), MeasurableSet A ∧ Avoids A A ∧
      area mu A = delta (Fintype.card n - 2) := by
  sorry

theorem double_cap_conjecture : IsGreatest (independentMasses mu) (delta (Fintype.card n - 2)) := by
  sorry

theorem alpha_eq_delta : alpha mu = delta (Fintype.card n - 2) := by
  sorry

theorem projective_shadow_inequality (A : Set (ProjectiveSpace (EuclideanSpace ℝ n)))
    (hA : NullMeasurableSet A (projectiveVolume mu)) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hmass : (projectiveVolume mu).real A = capMass (Fintype.card n - 2) r) :
    beltMass (Fintype.card n - 2) r ≤ (innerMeasure (projectiveVolume mu) (projectiveShadow A)).toReal := by
  sorry

theorem projective_shadow_equality (A : Set (ProjectiveSpace (EuclideanSpace ℝ n)))
    (hA : NullMeasurableSet A (projectiveVolume mu))
    (hp : (projectiveVolume mu).real A ∈ Ioo (0 : ℝ) 1)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hmass : (projectiveVolume mu).real A = capMass (Fintype.card n - 2) r)
    (heq : (innerMeasure (projectiveVolume mu) (projectiveShadow A)).toReal =
      beltMass (Fintype.card n - 2) r) :
    ∃ a : Sphere (EuclideanSpace ℝ n), A =ᵐ[projectiveVolume mu] projectiveCap a r := by
  sorry

theorem projective_caps_attain (a : Sphere (EuclideanSpace ℝ n)) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (projectiveVolume mu).real (projectiveCap a r) = capMass (Fintype.card n - 2) r ∧
    (innerMeasure (projectiveVolume mu) (projectiveShadow (projectiveCap a r))).toReal =
      beltMass (Fintype.card n - 2) r := by
  sorry

omit hdim in
theorem s2_double_cap_bound (nu : Measure (EuclideanSpace ℝ (Fin 3))) [nu.IsAddHaarMeasure]
    (A : Set (Sphere (EuclideanSpace ℝ (Fin 3)))) (hA : NullMeasurableSet A (probability nu))
    (hind : Avoids A A) : area nu A ≤ 1 - Real.sqrt 2 / 2 := by
  sorry

end LeanShadow.Comparator

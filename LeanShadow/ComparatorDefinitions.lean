import Mathlib

/-! # Definitions for the independently stated shadow problems

These definitions use only Mathlib. The Comparator challenge has its own copy,
so the proof never imports the challenge or its theorem placeholders.
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

end LeanShadow.Comparator

import LeanShadow.AreaContraction
import LeanShadow.FrobeniusBasis

/-! # Vanishing sum of the actual symmetric projective second variations

The trace-zero identity for the polarized area matrix becomes a statement
about an explicit sum of second derivatives of actual transformed measures.
The basis is constructed, not assumed to exist.

This is the symmetric-direction part of the manuscript's harmonicity
calculation, at the identity and for every Borel spherical set. Passing to
an operator on a neighbourhood of an arbitrary projective transformation
still requires the geometric composition and regularity results.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open Matrix MeasureTheory Set Module

namespace ShadowVerification.Harmonicity
open Spherical Projective Coordinates Integrated AreaContraction
open _root_.ShadowVerification.Frame

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]
  (A : Set (UnitSphere n))

/-- Diagonal polarization recovers the actual second variation. -/
theorem polarizedAreaMatrix_diagonal {ι : Type*} [Fintype ι]
    (hA : MeasurableSet A) (H : ι → Matrix n n ℝ)
    (hH : ∀ i, (H i).IsSymm) (ht : ∀ i, (H i).trace = 0) (i : ι) :
    polarizedAreaMatrix mu A H i i = secondArea mu A (H i) := by
  rw [polarizedAreaMatrix_eq_integrated mu A hA H hH ht, integratedKernel_entry,
    secondArea_integral mu A hA (H i) (hH i) (ht i)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change pointwiseKernel H ⇑(x : EuclideanSpace ℝ n) i i =
    quadraticDensity (H i) ⇑(x : EuclideanSpace ℝ n)
  rw [pointwiseKernel_apply]
  unfold quadraticDensity
  ring

/-- The trace identity is a vanishing sum of genuine second derivatives. -/
theorem sum_secondArea_eq_zero {ι : Type*} [Fintype ι]
    (hA : MeasurableSet A) (b : Basis ι ℝ (symZero (n := n)))
    (hb : IsOrthonormal b) :
    (∑ i, secondArea mu A (frame b i)) = 0 := by
  have h := area_trace_zero mu A hA b hb
  unfold Matrix.trace at h
  simpa only [Matrix.diag,
    polarizedAreaMatrix_diagonal mu A hA (frame b)
      (fun i => (b i).property.1) (fun i => (b i).property.2)] using h

/-- The symmetric harmonicity sum with the explicitly constructed Frobenius basis. -/
theorem canonical_sum_second_deriv_eq_zero (hA : MeasurableSet A) :
    (∑ i : FrobeniusIndex n,
      deriv (deriv (fun t => transformedArea mu A
        (flowEquiv (operator (frame (frobeniusBasis (n := n)) i)) t))) 0) = 0 := by
  exact sum_secondArea_eq_zero mu A hA frobeniusBasis frobeniusBasis_orthonormal

end ShadowVerification.Harmonicity

#print axioms ShadowVerification.Harmonicity.polarizedAreaMatrix_diagonal
#print axioms ShadowVerification.Harmonicity.sum_secondArea_eq_zero
#print axioms ShadowVerification.Harmonicity.canonical_sum_second_deriv_eq_zero

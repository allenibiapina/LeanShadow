import LeanShadow.NormalizedVariations
import LeanShadow.PointwiseContraction
import Mathlib.Analysis.Matrix.Hermitian

/-! # Matrices as the actual operators in spherical area variations

The coordinate map is mathlib's `Matrix.toEuclideanLin`, made continuous by
finite dimensionality. Symmetry, trace, and the density formulas are proved
compatible with this map. No image-measure identity is assumed here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix
open Matrix MeasureTheory Set
namespace ShadowVerification.Coordinates
open Spherical Projective

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def operator (H : Matrix n n ℝ) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n := H.toEuclideanLin.toContinuousLinearMap

theorem operator_apply (H : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    ⇑(operator H x) = H *ᵥ ⇑x := rfl

theorem operator_symmetric (H : Matrix n n ℝ) (hH : H.IsSymm) :
    (operator H : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n).IsSymmetric := by
  change H.toEuclideanLin.IsSymmetric
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  simpa using hH

theorem operator_trace (H : Matrix n n ℝ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ n) (operator H : _ →ₗ[ℝ] _) = H.trace := by
  change LinearMap.trace ℝ (EuclideanSpace ℝ n) H.toEuclideanLin = H.trace
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]

theorem inner_operator (H : Matrix n n ℝ) (x y : EuclideanSpace ℝ n) :
    inner ℝ x (operator H y) = ⇑x ⬝ᵥ (H *ᵥ ⇑y) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, operator_apply]
  exact dotProduct_comm _ _

theorem inner_operator_twice (H : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    inner ℝ x (operator H (operator H x)) = ⇑x ⬝ᵥ (H *ᵥ (H *ᵥ ⇑x)) := by
  rw [inner_operator, operator_apply]

omit [DecidableEq n] in
theorem sphere_dot_self (x : Sphere (EuclideanSpace ℝ n)) :
    ⇑(x : EuclideanSpace ℝ n) ⬝ᵥ ⇑(x : EuclideanSpace ℝ n) = 1 := by
  have hx : ‖(x : EuclideanSpace ℝ n)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  have h : inner ℝ (x : EuclideanSpace ℝ n) (x : EuclideanSpace ℝ n) = 1 := by
    simp [inner_self_eq_norm_sq_to_K, hx]
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using h

variable [Nonempty n] [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]

/-- The first matrix-coordinate variation is a derivative of actual image area. -/
theorem area_first_matrix (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]
    (H : Matrix n n ℝ) (hH : H.IsSymm) (ht : H.trace = 0)
    (A : Set (Sphere (EuclideanSpace ℝ n))) (hA : MeasurableSet A) :
    HasDerivAt (fun t => transformedArea mu A (flowEquiv (operator H) t))
      (∫ x in A, -(Fintype.card n : ℝ) *
        (⇑(x : EuclideanSpace ℝ n) ⬝ᵥ (H *ᵥ ⇑(x : EuclideanSpace ℝ n))) ∂probability mu) 0 := by
  have h := area_hasDeriv_trace_free mu (operator H) (operator_symmetric H hH)
    (by rw [operator_trace, ht]) A hA
  simpa only [finrank_euclideanSpace, inner_operator] using h

/-- The second matrix-coordinate variation is the second derivative of image area. -/
theorem area_second_matrix (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]
    (H : Matrix n n ℝ) (hH : H.IsSymm) (ht : H.trace = 0)
    (A : Set (Sphere (EuclideanSpace ℝ n))) (hA : MeasurableSet A) :
    deriv (deriv (fun t => transformedArea mu A (flowEquiv (operator H) t))) 0 =
      ∫ x in A, (Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2) *
        (⇑(x : EuclideanSpace ℝ n) ⬝ᵥ (H *ᵥ ⇑(x : EuclideanSpace ℝ n))) ^ 2 -
        2 * (Fintype.card n : ℝ) *
          (⇑(x : EuclideanSpace ℝ n) ⬝ᵥ (H *ᵥ (H *ᵥ ⇑(x : EuclideanSpace ℝ n))))
        ∂probability mu := by
  have h := area_second_deriv_trace_free mu (operator H) (operator_symmetric H hH)
    (by rw [operator_trace, ht]) A hA
  simpa only [finrank_euclideanSpace, inner_operator, operator_apply] using h

end ShadowVerification.Coordinates
#print axioms ShadowVerification.Coordinates.operator_apply
#print axioms ShadowVerification.Coordinates.operator_symmetric
#print axioms ShadowVerification.Coordinates.operator_trace
#print axioms ShadowVerification.Coordinates.inner_operator
#print axioms ShadowVerification.Coordinates.inner_operator_twice
#print axioms ShadowVerification.Coordinates.sphere_dot_self
#print axioms ShadowVerification.Coordinates.area_first_matrix
#print axioms ShadowVerification.Coordinates.area_second_matrix

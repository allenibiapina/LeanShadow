import LeanShadow.FrobeniusBasis
import LeanShadow.WeightedEllipticity
import Mathlib.LinearAlgebra.Matrix.StdBasis

/-! # A full frame in ambient matrix coordinates

We work in all invertible matrices near the identity. Alongside the symmetric
trace-free generators we include skew generators and the scalar generator.
The scalar direction is needed in these ambient coordinates; a frame only on
SL(n) would miss it. The skew family may be redundant, which is harmless for
ellipticity. Spanning is proved directly, not assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators
namespace ShadowVerification.FullFrame
open _root_.ShadowVerification.Frame

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev Ambient (n : Type*) := EuclideanSpace ℝ (n × n)
abbrev ExtraIndex (n : Type*) := (n × n) ⊕ Unit
abbrev FullIndex (n : Type*) [Fintype n] := (FrobeniusIndex n) ⊕ ExtraIndex n

noncomputable def skewGenerator (i j : n) : Matrix n n ℝ :=
  Matrix.single i j 1 - Matrix.single j i 1

noncomputable def generator : FullIndex n → Matrix n n ℝ :=
  Sum.elim (frame (frobeniusBasis (n := n)))
    (Sum.elim (fun p => skewGenerator p.1 p.2) (fun _ => 1))

noncomputable def leftField (H : Matrix n n ℝ) : Ambient n →L[ℝ] Ambient n :=
  ((flatten : Matrix n n ℝ ≃ₗ[ℝ] Ambient n).toLinearMap.comp
    ((LinearMap.mulLeft ℝ H).comp
      (flatten : Matrix n n ℝ ≃ₗ[ℝ] Ambient n).symm.toLinearMap)).toContinuousLinearMap

noncomputable def base : Ambient n := flatten (1 : Matrix n n ℝ)

/-- These are the actual left-multiplication fields of the matrix action. -/
theorem leftField_apply (H : Matrix n n ℝ) (x : Ambient n) :
    leftField H x = flatten (H * flatten.symm x) := rfl

/-- Every constructed field is continuous in the full matrix coordinate. -/
theorem continuous_field (i : FullIndex n) : Continuous (leftField (generator i)) :=
  (leftField (generator i)).continuous

theorem field_at_base (H : Matrix n n ℝ) : leftField H (base (n := n)) = flatten H := by
  rw [leftField_apply, base, LinearEquiv.symm_apply_apply, Matrix.mul_one]

/-- The skew generator tests exactly the antisymmetric part of a matrix. -/
theorem pairing_skew (X : Matrix n n ℝ) (i j : n) :
    pairing X (skewGenerator i j) = X i j - X j i := by
  unfold skewGenerator
  rw [pairing_sub_right]
  simp [pairing, Matrix.single_apply, ite_and]

/-- A matrix annihilating the symmetric trace-free, skew, and scalar
components is zero. -/
theorem matrix_separation [Nonempty n] (X : Matrix n n ℝ)
    (h : ∀ i : FullIndex n, pairing X (generator i) = 0) : X = 0 := by
  have ht : X.trace = 0 := by
    simpa only [generator, Sum.elim_inr, pairing_one] using h (.inr (.inr ()))
  have hsym : X.IsSymm := by
    ext i j
    have hp : X i j - X j i = 0 := by
      simpa only [generator, Sum.elim_inr, Sum.elim_inl, pairing_skew] using
        h (.inr (.inl (i, j)))
    exact (sub_eq_zero.mp hp).symm
  have hp : projection X = 0 := by
    rw [← frame_reconstruction (frobeniusBasis (n := n)) frobeniusBasis_orthonormal X]
    apply Finset.sum_eq_zero
    intro i _
    have hi : pairing (frame (frobeniusBasis (n := n)) i) X = 0 := by
      rw [pairing_comm]
      exact h (.inl i)
    rw [hi, zero_smul]
  have heq : projection X = X := by
    simp only [projection, hsym.eq, ht, zero_div, zero_smul, sub_zero]
    module
  rwa [heq] at hp

/-- The actual full field family separates every covector at the identity. -/
theorem fields_separate_at_base [Nonempty n] (v : Ambient n)
    (h : ∀ i : FullIndex n, inner ℝ v (leftField (generator i) base) = 0) : v = 0 := by
  have hz : (flatten : Matrix n n ℝ ≃ₗ[ℝ] Ambient n).symm v = 0 := by
    apply matrix_separation
    intro i
    have hi := h i
    rw [field_at_base] at hi
    have heq : v = flatten (flatten.symm v) := (LinearEquiv.apply_symm_apply _ v).symm
    rw [heq, flatten_pairing] at hi
    exact hi
  apply (flatten : Matrix n n ℝ ≃ₗ[ℝ] Ambient n).symm.injective
  simpa only [map_zero] using hz

end ShadowVerification.FullFrame
#print axioms ShadowVerification.FullFrame.leftField_apply
#print axioms ShadowVerification.FullFrame.continuous_field
#print axioms ShadowVerification.FullFrame.field_at_base
#print axioms ShadowVerification.FullFrame.pairing_skew
#print axioms ShadowVerification.FullFrame.matrix_separation
#print axioms ShadowVerification.FullFrame.fields_separate_at_base

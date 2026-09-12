import LeanShadow.ShadowVerification
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Reconstruction in a genuine symmetric trace-free matrix basis

The basis spans the actual submodule of symmetric trace-free matrices.
Orthonormality is expressed using the Frobenius pairing. The projection and
reconstruction identity are proved rather than added as assumptions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix
open Module
namespace ShadowVerification.Frame

variable {n : Type*} [Fintype n] [DecidableEq n]

def symZero : Submodule ℝ (Matrix n n ℝ) where
  carrier := {A | A.IsSymm ∧ A.trace = 0}
  zero_mem' := ⟨Matrix.isSymm_zero, by simp⟩
  add_mem' ha hb := ⟨ha.1.add hb.1, by simp [Matrix.trace_add, ha.2, hb.2]⟩
  smul_mem' c A hA := ⟨hA.1.smul c, by simp [Matrix.trace_smul, hA.2]⟩

noncomputable def pairing (A B : Matrix n n ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

omit [DecidableEq n] in
theorem pairing_comm (A B : Matrix n n ℝ) : pairing A B = pairing B A := by
  simp only [pairing, mul_comm]

omit [DecidableEq n] in
theorem pairing_add_right (A B C : Matrix n n ℝ) :
    pairing A (B + C) = pairing A B + pairing A C := by
  simp only [pairing, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

omit [DecidableEq n] in
theorem pairing_sub_right (A B C : Matrix n n ℝ) :
    pairing A (B - C) = pairing A B - pairing A C := by
  simp only [pairing, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

omit [DecidableEq n] in
theorem pairing_smul_right (A B : Matrix n n ℝ) (c : ℝ) :
    pairing A (c • B) = c * pairing A B := by
  simp only [pairing, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq n] in
theorem pairing_sum_right {ι : Type*} [Fintype ι] (A : Matrix n n ℝ)
    (B : ι → Matrix n n ℝ) : pairing A (∑ i, B i) = ∑ i, pairing A (B i) := by
  simp only [pairing, Matrix.sum_apply, Finset.mul_sum]
  calc
    (∑ r, ∑ s, ∑ i, A r s * B i r s) = ∑ r, ∑ i, ∑ s, A r s * B i r s := by
      apply Finset.sum_congr rfl
      intro r _
      exact Finset.sum_comm
    _ = ∑ i, ∑ r, ∑ s, A r s * B i r s := Finset.sum_comm

theorem pairing_one (A : Matrix n n ℝ) : pairing A 1 = A.trace := by
  simp [pairing, Matrix.one_apply, Matrix.trace, Matrix.diag]

omit [DecidableEq n] in
theorem pairing_transpose_right (A B : Matrix n n ℝ) (hA : A.IsSymm) :
    pairing A Bᵀ = pairing A B := by
  unfold pairing
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hA.apply j i]

noncomputable def projection (A : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (A + Aᵀ) - (A.trace / (Fintype.card n : ℝ)) • 1

theorem projection_symm (A : Matrix n n ℝ) : (projection A).IsSymm := by
  change (projection A)ᵀ = projection A
  simp only [projection, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_add, Matrix.transpose_transpose, Matrix.transpose_one]
  rw [add_comm Aᵀ A]

theorem projection_trace [Nonempty n] (A : Matrix n n ℝ) : (projection A).trace = 0 := by
  have hn : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [projection, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_transpose, Matrix.trace_one, smul_eq_mul]
  field_simp
  ring

theorem pairing_projection (A B : Matrix n n ℝ) (hA : A.IsSymm) (ht : A.trace = 0) :
    pairing A (projection B) = pairing A B := by
  rw [projection, pairing_sub_right, pairing_smul_right, pairing_smul_right,
    pairing_add_right, pairing_transpose_right A B hA, pairing_one, ht]
  ring

variable {ι : Type*} [Fintype ι]

noncomputable def frame (b : Basis ι ℝ (symZero (n := n))) (i : ι) : Matrix n n ℝ := (b i).val

def IsOrthonormal (b : Basis ι ℝ (symZero (n := n))) : Prop := by
  classical
  exact ∀ i j, pairing (frame b i) (frame b j) = if i = j then 1 else 0

omit [DecidableEq n] in
/-- Basis coefficients are the actual Frobenius pairings. -/
theorem basis_coefficient (b : Basis ι ℝ (symZero (n := n))) (hb : IsOrthonormal b)
    (A : symZero (n := n)) (i : ι) : b.repr A i = pairing (frame b i) A.val := by
  classical
  unfold IsOrthonormal at hb
  have h := congrArg (fun X : symZero (n := n) => pairing (frame b i) X.val) (b.sum_repr A)
  simp only [Submodule.coe_sum, Submodule.coe_smul, pairing_sum_right,
    pairing_smul_right] at h
  change (∑ j, b.repr A j * pairing (frame b i) (frame b j)) = pairing (frame b i) A.val at h
  simpa [hb] using h

/-- Reconstruction of the orthogonal projection, for every matrix. -/
theorem frame_reconstruction [Nonempty n]
    (b : Basis ι ℝ (symZero (n := n))) (hb : IsOrthonormal b) (A : Matrix n n ℝ) :
    (∑ i, pairing (frame b i) A • frame b i) = projection A := by
  let P : symZero (n := n) := ⟨projection A, projection_symm A, projection_trace A⟩
  have h := congrArg (fun X : symZero (n := n) => X.val) (b.sum_repr P)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  change (∑ i, b.repr P i • frame b i) = projection A at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [basis_coefficient b hb]
  exact (pairing_projection (frame b i) A (b i).property.1 (b i).property.2).symm

end ShadowVerification.Frame
#print axioms ShadowVerification.Frame.pairing_comm
#print axioms ShadowVerification.Frame.pairing_add_right
#print axioms ShadowVerification.Frame.pairing_sub_right
#print axioms ShadowVerification.Frame.pairing_smul_right
#print axioms ShadowVerification.Frame.pairing_sum_right
#print axioms ShadowVerification.Frame.pairing_one
#print axioms ShadowVerification.Frame.pairing_transpose_right
#print axioms ShadowVerification.Frame.projection_symm
#print axioms ShadowVerification.Frame.projection_trace
#print axioms ShadowVerification.Frame.pairing_projection
#print axioms ShadowVerification.Frame.basis_coefficient
#print axioms ShadowVerification.Frame.frame_reconstruction

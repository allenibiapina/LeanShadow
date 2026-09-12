import LeanShadow.FrameProjection
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Existence of a genuine Frobenius orthonormal trace-free basis

Flattening a matrix identifies its Frobenius pairing with the ordinary
Euclidean inner product. We transport the actual symmetric trace-free
subspace into that Euclidean space, choose a standard orthonormal basis
there, and transport it back. No additional inner product is postulated.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix
open Matrix Module
namespace ShadowVerification.Frame

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def flatten : Matrix n n ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (n × n) where
  toFun A := WithLp.toLp 2 (fun p => A p.1 p.2)
  invFun x := fun i j => x (i, j)
  left_inv A := rfl
  right_inv x := by ext p; rfl
  map_add' A B := rfl
  map_smul' r A := rfl

omit [DecidableEq n] in
theorem flatten_pairing (A B : Matrix n n ℝ) :
    inner ℝ (flatten A) (flatten B) = pairing A B := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
    flatten, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Fintype.sum_prod_type, pairing]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

noncomputable def frobeniusSubspace : Submodule ℝ (EuclideanSpace ℝ (n × n)) :=
  (symZero (n := n)).map (flatten : Matrix n n ℝ ≃ₗ[ℝ] _).toLinearMap

noncomputable def frobeniusSubspaceEquiv : symZero (n := n) ≃ₗ[ℝ] frobeniusSubspace (n := n) :=
  Submodule.equivMapOfInjective (flatten : Matrix n n ℝ ≃ₗ[ℝ] _).toLinearMap
    flatten.injective symZero

abbrev FrobeniusIndex (n : Type*) [Fintype n] :=
  Fin (Module.finrank ℝ (frobeniusSubspace (n := n)))

noncomputable def frobeniusBasis : Basis (FrobeniusIndex n) ℝ (symZero (n := n)) :=
  (stdOrthonormalBasis ℝ (frobeniusSubspace (n := n))).toBasis.map frobeniusSubspaceEquiv.symm

omit [DecidableEq n] in
theorem flatten_frobeniusBasis (i : FrobeniusIndex n) :
    flatten (frame (frobeniusBasis (n := n)) i) =
      (stdOrthonormalBasis ℝ (frobeniusSubspace (n := n)) i).val := by
  change flatten ((frobeniusSubspaceEquiv (n := n)).symm
    (stdOrthonormalBasis ℝ (frobeniusSubspace (n := n)) i)).val = _
  exact Submodule.map_equivMapOfInjective_symm_apply _ _ _ _

omit [DecidableEq n] in
/-- An actual orthonormal basis for the exact Frobenius pairing used in the contraction. -/
theorem frobeniusBasis_orthonormal : IsOrthonormal (frobeniusBasis (n := n)) := by
  classical
  unfold IsOrthonormal
  intro i j
  rw [← flatten_pairing, flatten_frobeniusBasis, flatten_frobeniusBasis]
  have h := (stdOrthonormalBasis ℝ (frobeniusSubspace (n := n))).inner_eq_ite i j
  by_cases hij : i = j
  · simpa only [Submodule.coe_inner, if_pos hij] using h
  · simpa only [Submodule.coe_inner, if_neg hij] using h

end ShadowVerification.Frame
#print axioms ShadowVerification.Frame.flatten_pairing
#print axioms ShadowVerification.Frame.flatten_frobeniusBasis
#print axioms ShadowVerification.Frame.frobeniusBasis_orthonormal

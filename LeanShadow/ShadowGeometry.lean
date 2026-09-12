import LeanShadow.ShadowVerification

/-! # Orthogonality and covariance on vector representatives

These are statements about actual real vectors and their dot product. They
provide the homogeneous-coordinate part of projective covariance. Projective
quotients and spherical measures are not constructed in this module.
-/
set_option autoImplicit false
open scoped Matrix

namespace ShadowVerification

variable {n : Type*} [Fintype n]

def vectorShadow (A : Set (n → ℝ)) : Set (n → ℝ) :=
  {y | ∃ x ∈ A, x ⬝ᵥ y = 0}

def Avoids (A B : Set (n → ℝ)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, x ⬝ᵥ y ≠ 0

theorem avoids_iff_disjoint_shadow (A B : Set (n → ℝ)) :
    Avoids A B ↔ Disjoint B (vectorShadow A) := by
  rw [Set.disjoint_left]
  constructor
  · intro h y hy hs
    obtain ⟨x, hx, hxy⟩ := hs
    exact h x hx y hy hxy
  · intro h x hx y hy hxy
    exact h hy ⟨x, hx, hxy⟩

theorem orthogonal_scaling_iff (x y : n → ℝ) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (a • x) ⬝ᵥ (b • y) = 0 ↔ x ⬝ᵥ y = 0 := by
  simp [smul_dotProduct, dotProduct_smul, smul_eq_mul, ha, hb]

variable [DecidableEq n]

theorem dual_pairing (T U : Matrix n n ℝ) (hTU : Tᵀ * U = 1)
    (x y : n → ℝ) : (T *ᵥ x) ⬝ᵥ (U *ᵥ y) = x ⬝ᵥ y := by
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec,
    Matrix.mulVec_mulVec, hTU, Matrix.one_mulVec]

theorem avoids_dual_images (A B : Set (n → ℝ)) (T U : Matrix n n ℝ)
    (hTU : Tᵀ * U = 1) (h : Avoids A B) :
    Avoids ((fun x => T *ᵥ x) '' A) ((fun y => U *ᵥ y) '' B) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [dual_pairing T U hTU]
  exact h x hx y hy

theorem vectorShadow_covariance (A : Set (n → ℝ)) (T U : Matrix n n ℝ)
    (hTU : Tᵀ * U = 1) (hUT : U * Tᵀ = 1) :
    vectorShadow ((fun x => T *ᵥ x) '' A) =
      (fun y => U *ᵥ y) '' vectorShadow A := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
    refine ⟨Tᵀ *ᵥ y, ⟨x, hx, ?_⟩, ?_⟩
    · rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
      exact hxy
    · change U *ᵥ (Tᵀ *ᵥ y) = y
      rw [Matrix.mulVec_mulVec, hUT, Matrix.one_mulVec]
  · rintro ⟨z, ⟨x, hx, hxz⟩, rfl⟩
    refine ⟨T *ᵥ x, ⟨x, hx, rfl⟩, ?_⟩
    rw [dual_pairing T U hTU]
    exact hxz

theorem vectorShadow_inverse_transpose (A : Set (n → ℝ))
    (T : (Matrix n n ℝ)ˣ) :
    vectorShadow ((fun x => (T : Matrix n n ℝ) *ᵥ x) '' A) =
      (fun y => ((↑(T⁻¹) : Matrix n n ℝ)ᵀ) *ᵥ y) '' vectorShadow A := by
  apply vectorShadow_covariance
  · rw [← Matrix.transpose_mul]
    simp
  · rw [← Matrix.transpose_mul]
    simp

end ShadowVerification

#print axioms ShadowVerification.avoids_iff_disjoint_shadow
#print axioms ShadowVerification.orthogonal_scaling_iff
#print axioms ShadowVerification.dual_pairing
#print axioms ShadowVerification.avoids_dual_images
#print axioms ShadowVerification.vectorShadow_covariance
#print axioms ShadowVerification.vectorShadow_inverse_transpose

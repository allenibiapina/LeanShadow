import LeanShadow.OrthogonalIncidence

/-! # Transitivity on orthonormal pairs and the invariant group metric -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.OrthogonalFrame
open Spherical OrthogonalHaar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Right multiplication preserves the operator-norm metric on the orthogonal group. -/
theorem dist_mul_right (R S U : OrthogonalHaar.Group E) : dist (R * U) (S * U) = dist R S := by
  simp only [Subtype.dist_eq, dist_eq_norm]
  change ‖(R : E →L[ℝ] E) * U - (S : E →L[ℝ] E) * U‖ =
    ‖(R : E →L[ℝ] E) - (S : E →L[ℝ] E)‖
  rw [← sub_mul, CStarRing.norm_mul_coe_unitary]

/-- A reflection exchanging two vectors orthogonal to an axis fixes that axis. -/
theorem exists_exchange_fix (x y z : Sphere E)
    (hxy : inner ℝ (x : E) (y : E) = 0)
    (hxz : inner ℝ (x : E) (z : E) = 0) :
    ∃ R : OrthogonalHaar.Group E, rotate R x = x ∧ rotate R y = z := by
  let L := (ℝ ∙ ((y : E) - (z : E)))ᗮ.reflection
  let R : OrthogonalHaar.Group E := Unitary.linearIsometryEquiv.symm L
  have hn : ‖(y : E)‖ = ‖(z : E)‖ := by
    rw [mem_sphere_zero_iff_norm.mp y.property, mem_sphere_zero_iff_norm.mp z.property]
  refine ⟨R, Subtype.ext ?_, Subtype.ext (Submodule.reflection_sub hn)⟩
  apply Submodule.reflection_mem_subspace_eq_self
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
  simp [inner_sub_right, hxy, hxz]

/-- Any two ordered orthonormal pairs are related by an actual orthogonal map. -/
theorem exists_pair (a b x y : Sphere E)
    (hab : inner ℝ (a : E) (b : E) = 0)
    (hxy : inner ℝ (x : E) (y : E) = 0) :
    ∃ R : OrthogonalHaar.Group E, rotate R a = x ∧ rotate R b = y := by
  obtain ⟨S, hS, _⟩ := exists_exchange a x
  have hxb : inner ℝ (x : E) (rotate S b : E) = 0 := by
    rw [← hS, rotate_inner, hab]
  obtain ⟨U, hUx, hUb⟩ := exists_exchange_fix x (rotate S b) y hxb hxy
  exact ⟨U * S, by rw [rotate_mul, hS, hUx], by rw [rotate_mul, hUb]⟩

/-- The stabilizer of an axis is transitive on each signed latitude. -/
theorem exists_exchange_latitude (x y z : Sphere E)
    (h : inner ℝ (x : E) (y : E) = inner ℝ (x : E) (z : E)) :
    ∃ R : OrthogonalHaar.Group E, rotate R x = x ∧ rotate R y = z := by
  let L := (ℝ ∙ ((y : E) - (z : E)))ᗮ.reflection
  let R : OrthogonalHaar.Group E := Unitary.linearIsometryEquiv.symm L
  have hn : ‖(y : E)‖ = ‖(z : E)‖ := by
    rw [mem_sphere_zero_iff_norm.mp y.property, mem_sphere_zero_iff_norm.mp z.property]
  refine ⟨R, Subtype.ext ?_, Subtype.ext (Submodule.reflection_sub hn)⟩
  apply Submodule.reflection_mem_subspace_eq_self
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right, h, sub_self]

/-- Equal Gram matrices characterize the orbits of ordered spherical pairs. -/
theorem exists_pair_of_inner_eq (a b x y : Sphere E)
    (h : inner ℝ (a : E) (b : E) = inner ℝ (x : E) (y : E)) :
    ∃ R : OrthogonalHaar.Group E, rotate R a = x ∧ rotate R b = y := by
  obtain ⟨S, hS, _⟩ := exists_exchange a x
  have hi : inner ℝ (x : E) (rotate S b : E) = inner ℝ (x : E) (y : E) := by
    rw [← hS, rotate_inner, h, hS]
  obtain ⟨U, hUx, hUb⟩ := exists_exchange_latitude x (rotate S b) y hi
  exact ⟨U * S, by rw [rotate_mul, hS, hUx], by rw [rotate_mul, hUb]⟩

end ShadowVerification.OrthogonalFrame
#print axioms ShadowVerification.OrthogonalFrame.dist_mul_right
#print axioms ShadowVerification.OrthogonalFrame.exists_exchange_fix
#print axioms ShadowVerification.OrthogonalFrame.exists_pair
#print axioms ShadowVerification.OrthogonalFrame.exists_exchange_latitude
#print axioms ShadowVerification.OrthogonalFrame.exists_pair_of_inner_eq

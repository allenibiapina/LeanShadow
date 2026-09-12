import LeanShadow.SphericalProjective

/-! # Antipodal representatives of projective spherical sets

The projective profile will be defined using Borel antipodal subsets of the
actual sphere, with normalized spherical measure. These lemmas verify that
the projective transformations preserve this class and that an avoiding
partner can be made antipodal without introducing orthogonal pairs.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace ShadowVerification.Antipodal
open Spherical

variable {E : Type*} [NormedAddCommGroup E]

noncomputable def antipode (x : Sphere E) : Sphere E :=
  ⟨-x, by simpa only [mem_sphere_zero_iff_norm, norm_neg] using x.property⟩

theorem antipode_coe (x : Sphere E) : (antipode x : E) = -(x : E) := rfl

theorem antipode_twice (x : Sphere E) : antipode (antipode x) = x := by
  apply Subtype.ext
  exact neg_neg (x : E)

theorem antipode_continuous : Continuous (antipode (E := E)) :=
  Continuous.subtype_mk continuous_subtype_val.neg _

noncomputable def antipodeHomeomorph : Sphere E ≃ₜ Sphere E where
  toFun := antipode
  invFun := antipode
  left_inv := antipode_twice
  right_inv := antipode_twice
  continuous_toFun := antipode_continuous
  continuous_invFun := antipode_continuous

def IsAntipodal (A : Set (Sphere E)) : Prop := ∀ x ∈ A, antipode x ∈ A

def symmetrize (A : Set (Sphere E)) : Set (Sphere E) := A ∪ antipode '' A

theorem subset_symmetrize (A : Set (Sphere E)) : A ⊆ symmetrize A := subset_union_left

theorem symmetrize_antipodal (A : Set (Sphere E)) : IsAntipodal (symmetrize A) := by
  rintro x (hx | ⟨y, hy, rfl⟩)
  · exact Or.inr ⟨x, hx, rfl⟩
  · exact Or.inl (by simpa only [antipode_twice] using hy)

variable [InnerProductSpace ℝ E]

theorem action_antipode (T : E ≃L[ℝ] E) (x : Sphere E) :
    action T (antipode x) = antipode (action T x) := by
  apply Subtype.ext
  change NormedSpace.normalize (T (-(x : E))) = -NormedSpace.normalize (T x)
  rw [map_neg, NormedSpace.normalize_neg]

theorem antipodal_action_image (T : E ≃L[ℝ] E) (A : Set (Sphere E))
    (hA : IsAntipodal A) : IsAntipodal (action T '' A) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨antipode x, hA x hx, action_antipode T x⟩

theorem shadow_antipodal (A : Set (Sphere E)) : IsAntipodal (shadow A) := by
  rintro y ⟨x, hx, hxy⟩
  refine ⟨x, hx, ?_⟩
  change inner ℝ (x : E) (-(y : E)) = 0
  rw [inner_neg_right, hxy, neg_zero]

theorem avoids_symmetrize_right (A B : Set (Sphere E)) (hAB : Avoids A B) :
    Avoids A (symmetrize B) := by
  rintro x hx y (hy | ⟨z, hz, rfl⟩)
  · exact hAB x hx y hy
  · change inner ℝ (x : E) (-(z : E)) ≠ 0
    rw [inner_neg_right, neg_ne_zero]
    exact hAB x hx z hz

theorem shadow_symmetrize (A : Set (Sphere E)) : shadow (symmetrize A) = shadow A := by
  ext y
  constructor
  · rintro ⟨x, hx | ⟨z, hz, rfl⟩, hxy⟩
    · exact ⟨x, hx, hxy⟩
    · refine ⟨z, hz, ?_⟩
      change inner ℝ (-(z : E)) (y : E) = 0 at hxy
      simpa only [inner_neg_left, neg_eq_zero] using hxy
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, Or.inl hx, hxy⟩

variable [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] in
theorem symmetrize_measurable (A : Set (Sphere E)) (hA : MeasurableSet A) :
    MeasurableSet (symmetrize A) := by
  apply hA.union
  exact antipodeHomeomorph.measurableEmbedding.measurableSet_image.mpr hA

end ShadowVerification.Antipodal
#print axioms ShadowVerification.Antipodal.antipode_coe
#print axioms ShadowVerification.Antipodal.antipode_twice
#print axioms ShadowVerification.Antipodal.antipode_continuous
#print axioms ShadowVerification.Antipodal.subset_symmetrize
#print axioms ShadowVerification.Antipodal.symmetrize_antipodal
#print axioms ShadowVerification.Antipodal.action_antipode
#print axioms ShadowVerification.Antipodal.antipodal_action_image
#print axioms ShadowVerification.Antipodal.shadow_antipodal
#print axioms ShadowVerification.Antipodal.avoids_symmetrize_right
#print axioms ShadowVerification.Antipodal.shadow_symmetrize
#print axioms ShadowVerification.Antipodal.symmetrize_measurable

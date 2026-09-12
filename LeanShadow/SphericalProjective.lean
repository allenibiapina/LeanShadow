import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! # Spherical representatives, their measure, and projective actions

The measure is the normalized measure induced by additive Haar measure on the
ambient finite-dimensional real space. The shadow is defined by existence of
an actually orthogonal unit vector, and transformed area is the measure of an
actual image set. No Jacobian formula is used in these definitions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.Spherical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Sphere (E : Type*) [NormedAddCommGroup E] := Metric.sphere (0 : E) 1

omit [InnerProductSpace ℝ E] in
theorem unit_ne_zero (x : Sphere E) : (x : E) ≠ 0 := by
  exact ne_of_mem_sphere x.property one_ne_zero

noncomputable def action (T : E ≃L[ℝ] E) (x : Sphere E) : Sphere E :=
  ⟨NormedSpace.normalize (T x), by
    rw [mem_sphere_zero_iff_norm]
    apply NormedSpace.norm_normalize
    exact (by simpa only [map_zero] using T.injective.ne (unit_ne_zero x))⟩

theorem action_coe (T : E ≃L[ℝ] E) (x : Sphere E) :
    (action T x : E) = ‖T x‖⁻¹ • T x := rfl

theorem action_symm_action (T : E ≃L[ℝ] E) (x : Sphere E) :
    action T.symm (action T x) = x := by
  apply Subtype.ext
  change NormedSpace.normalize (T.symm (‖T x‖⁻¹ • T x)) = (x : E)
  rw [map_smul, T.symm_apply_apply,
    NormedSpace.normalize_smul_of_pos (by
      apply inv_pos.mpr
      exact norm_pos_iff.mpr ((by simpa only [map_zero] using T.injective.ne (unit_ne_zero x)))),
    NormedSpace.normalize_eq_self_of_norm_eq_one]
  exact mem_sphere_zero_iff_norm.mp x.property

theorem action_continuous (T : E ≃L[ℝ] E) : Continuous (action T) := by
  apply Continuous.subtype_mk
  change Continuous (fun x : Sphere E => ‖T x‖⁻¹ • T x)
  apply Continuous.smul
  · apply Continuous.inv₀
    · fun_prop
    · intro x
      exact norm_ne_zero_iff.mpr ((by simpa only [map_zero] using T.injective.ne (unit_ne_zero x)))
  · fun_prop

noncomputable def actionHomeomorph (T : E ≃L[ℝ] E) : Sphere E ≃ₜ Sphere E where
  toFun := action T
  invFun := action T.symm
  left_inv := action_symm_action T
  right_inv := action_symm_action T.symm
  continuous_toFun := action_continuous T
  continuous_invFun := action_continuous T.symm

def shadow (A : Set (Sphere E)) : Set (Sphere E) :=
  {y | ∃ x ∈ A, inner ℝ (x : E) (y : E) = 0}

def Avoids (A B : Set (Sphere E)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, inner ℝ (x : E) (y : E) ≠ 0

theorem avoids_iff_disjoint_shadow (A B : Set (Sphere E)) :
    Avoids A B ↔ Disjoint B (shadow A) := by
  rw [Set.disjoint_left]
  constructor
  · intro h y hy hs
    obtain ⟨x, hx, hxy⟩ := hs
    exact h x hx y hy hxy
  · intro h x hx y hy hxy
    exact h hy ⟨x, hx, hxy⟩

theorem action_orthogonal_iff (T U : E ≃L[ℝ] E)
    (hdual : ∀ x y : E, inner ℝ (T x) (U y) = inner ℝ x y)
    (x y : Sphere E) :
    inner ℝ (action T x : E) (action U y : E) = 0 ↔ inner ℝ (x : E) (y : E) = 0 := by
  rw [action_coe, action_coe, real_inner_smul_left, real_inner_smul_right, hdual]
  have hx : ‖T x‖ ≠ 0 := norm_ne_zero_iff.mpr ((by simpa only [map_zero] using T.injective.ne (unit_ne_zero x)))
  have hy : ‖U y‖ ≠ 0 := norm_ne_zero_iff.mpr ((by simpa only [map_zero] using U.injective.ne (unit_ne_zero y)))
  simp [hx, hy]

theorem shadow_covariance (T U : E ≃L[ℝ] E)
    (hdual : ∀ x y : E, inner ℝ (T x) (U y) = inner ℝ x y) (A : Set (Sphere E)) :
    shadow (action T '' A) = action U '' shadow A := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
    let z := action U.symm y
    have hz : action U z = y := action_symm_action U.symm y
    refine ⟨z, ⟨x, hx, ?_⟩, hz⟩
    apply (action_orthogonal_iff T U hdual x z).mp
    simpa only [hz] using hxy
  · rintro ⟨z, ⟨x, hx, hxz⟩, rfl⟩
    exact ⟨action T x, ⟨x, hx, rfl⟩, (action_orthogonal_iff T U hdual x z).mpr hxz⟩

section Measure
variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

noncomputable def probability (mu : Measure E) : Measure (Sphere E) :=
  (mu.toSphere Set.univ)⁻¹ • mu.toSphere

variable (mu : Measure E) [mu.IsAddHaarMeasure]

theorem probability_univ : probability mu Set.univ = 1 := by
  unfold probability
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by intro h; exact mu.toSphere_ne_zero (Measure.measure_univ_eq_zero.mp h)) (measure_ne_top _ _)

instance probability_isProbabilityMeasure : IsProbabilityMeasure (probability mu) :=
  ⟨probability_univ mu⟩

noncomputable def area (A : Set (Sphere E)) : ℝ := (probability mu).real A
noncomputable def transformedArea (A : Set (Sphere E)) (T : E ≃L[ℝ] E) : ℝ :=
  area mu (action T '' A)

omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [mu.IsAddHaarMeasure] in
theorem area_nonneg (A : Set (Sphere E)) : 0 ≤ area mu A := ENNReal.toReal_nonneg

theorem area_le_one (A : Set (Sphere E)) : area mu A ≤ 1 := by
  exact (measureReal_mono (subset_univ A)).trans_eq (by simp)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem measurable_action_image (T : E ≃L[ℝ] E) (A : Set (Sphere E))
    (hA : MeasurableSet A) : MeasurableSet (action T '' A) :=
  (actionHomeomorph T).measurableEmbedding.measurableSet_image.mpr hA

end Measure
end ShadowVerification.Spherical
#print axioms ShadowVerification.Spherical.unit_ne_zero
#print axioms ShadowVerification.Spherical.action_coe
#print axioms ShadowVerification.Spherical.action_symm_action
#print axioms ShadowVerification.Spherical.action_continuous
#print axioms ShadowVerification.Spherical.avoids_iff_disjoint_shadow
#print axioms ShadowVerification.Spherical.action_orthogonal_iff
#print axioms ShadowVerification.Spherical.shadow_covariance
#print axioms ShadowVerification.Spherical.probability_univ
#print axioms ShadowVerification.Spherical.area_nonneg
#print axioms ShadowVerification.Spherical.area_le_one
#print axioms ShadowVerification.Spherical.measurable_action_image

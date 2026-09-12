import LeanShadow.SphericalDirectionNull
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # Splitting an ambient vector into its axial and perpendicular coordinates -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.AxisCoordinates
open Spherical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def perpendicular (a : Sphere E) : Submodule ℝ E := (ℝ ∙ (a : E))ᗮ

def equivalence (a : Sphere E) : (ℝ × perpendicular a) ≃ₗ[ℝ] E :=
  ((LinearEquiv.toSpanNonzeroSingleton ℝ E (a : E) (unit_ne_zero a)).prodCongr
    (LinearEquiv.refl ℝ (perpendicular a))).trans
    ((ℝ ∙ (a : E)).prodEquivOfIsCompl (perpendicular a) (ℝ ∙ (a : E)).isCompl_orthogonal)

omit [FiniteDimensional ℝ E] in
theorem equivalence_apply (a : Sphere E) (t : ℝ) (v : perpendicular a) :
    equivalence a (t,v) = t • (a : E) + (v : E) := rfl

omit [FiniteDimensional ℝ E] in
theorem inner_perpendicular (a : Sphere E) (v : perpendicular a) :
    inner ℝ (a : E) (v : E) = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.property

omit [FiniteDimensional ℝ E] in
theorem inner_equivalence (a : Sphere E) (t : ℝ) (v : perpendicular a) :
    inner ℝ (a : E) (equivalence a (t,v)) = t := by
  rw [equivalence_apply, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    mem_sphere_zero_iff_norm.mp a.property, inner_perpendicular]
  simp

omit [FiniteDimensional ℝ E] in
theorem norm_equivalence_sq (a : Sphere E) (t : ℝ) (v : perpendicular a) :
    ‖equivalence a (t,v)‖ ^ 2 = t ^ 2 + ‖v‖ ^ 2 := by
  rw [equivalence_apply, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    mem_sphere_zero_iff_norm.mp a.property, inner_smul_left, inner_perpendicular]
  simp [sq_abs]

omit [FiniteDimensional ℝ E] in
theorem ratio_equivalence (a : Sphere E) (t : ℝ) (v : perpendicular a) :
    DirectionNull.ratio a (equivalence a (t,v)) = t / Real.sqrt (t ^ 2 + ‖v‖ ^ 2) := by
  unfold DirectionNull.ratio
  rw [inner_equivalence, ← norm_equivalence_sq, Real.sqrt_sq (norm_nonneg _)]

theorem perpendicular_finrank (a : Sphere E) :
    Module.finrank ℝ (perpendicular a) + 1 = Module.finrank ℝ E := by
  have h := (ℝ ∙ (a : E)).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton (unit_ne_zero a)] at h
  change 1 + Module.finrank ℝ (perpendicular a) = Module.finrank ℝ E at h
  omega

theorem perpendicular_nontrivial (a : Sphere E) (hd : 1 < Module.finrank ℝ E) :
    Nontrivial (perpendicular a) := by
  have h : 0 < Module.finrank ℝ (perpendicular a) := by
    have he := perpendicular_finrank a
    omega
  exact Module.finrank_pos_iff.mp h

variable [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

/-- Haar disintegration identifies the null events in these actual linear coordinates. -/
theorem ambient_null_iff (a : Sphere E) (S : Set E) (hS : MeasurableSet S) :
    mu S = 0 ↔
      (volume.prod (Measure.addHaar : Measure (perpendicular a))) ((equivalence a) ⁻¹' S) = 0 := by
  have h := ae_comp_linearMap_mem_iff (equivalence a).toLinearMap
    (volume.prod (Measure.addHaar : Measure (perpendicular a))) mu
    (equivalence a).surjective hS.compl
  simpa only [ae_iff, mem_compl_iff, not_not, ofPred_mem_eq, LinearEquiv.coe_coe, preimage] using h.symm

end ShadowVerification.AxisCoordinates
#print axioms ShadowVerification.AxisCoordinates.equivalence_apply
#print axioms ShadowVerification.AxisCoordinates.inner_perpendicular
#print axioms ShadowVerification.AxisCoordinates.inner_equivalence
#print axioms ShadowVerification.AxisCoordinates.norm_equivalence_sq
#print axioms ShadowVerification.AxisCoordinates.ratio_equivalence
#print axioms ShadowVerification.AxisCoordinates.perpendicular_finrank
#print axioms ShadowVerification.AxisCoordinates.perpendicular_nontrivial
#print axioms ShadowVerification.AxisCoordinates.ambient_null_iff

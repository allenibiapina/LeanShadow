import LeanShadow.SphericalNullSets
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Null sets under the one-dimensional latitude coordinate

The map t ↦ t/sqrt(t²+r²), for r>0, is a smooth parametrization of
(-1,1) with a smooth inverse. Thus it has exactly the Lebesgue-null
preimages expected of a latitude coordinate. No density formula is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.LatitudeCoordinate

/-- A differentiable bijection with differentiable inverse preserves null sets in both directions. -/
theorem null_preimage_iff_of_inverse (f g : ℝ → ℝ) (S : Set ℝ)
    (hf : Differentiable ℝ f) (hg : DifferentiableOn ℝ g S)
    (hmap : ∀ t, f t ∈ S) (hgf : ∀ t, g (f t) = t)
    (hfg : ∀ t ∈ S, f (g t) = t) (N : Set ℝ) :
    volume (f ⁻¹' N) = 0 ↔ volume (N ∩ S) = 0 := by
  have he : f '' (f ⁻¹' N) = N ∩ S := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨hs, hmap s⟩
    · intro ht
      exact ⟨g t, by simpa only [mem_preimage, hfg t ht.2] using ht.1, hfg t ht.2⟩
  have hi : g '' (N ∩ S) = f ⁻¹' N := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa only [mem_preimage, hfg s hs.2] using hs.1
    · intro ht
      exact ⟨f t, ⟨ht, hmap t⟩, hgf t⟩
  constructor
  · intro h
    rw [← he]
    exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hf.differentiableOn h
  · intro h
    rw [← hi]
    exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (hg.mono inter_subset_right) h

def squeeze (t : ℝ) : ℝ := OpenPartialHomeomorph.univUnitBall t
def unsqueeze (t : ℝ) : ℝ := OpenPartialHomeomorph.univUnitBall.symm t

theorem squeeze_formula (t : ℝ) : squeeze t = t / Real.sqrt (1 + t ^ 2) := by
  simp only [squeeze, OpenPartialHomeomorph.univUnitBall_apply, Real.norm_eq_abs,
    sq_abs, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem normalized_formula (r t : ℝ) (hr : 0 < r) :
    squeeze (t / r) = t / Real.sqrt (t ^ 2 + r ^ 2) := by
  rw [squeeze_formula]
  have hb : 1 + (t / r) ^ 2 = (t ^ 2 + r ^ 2) / r ^ 2 := by field_simp; ring
  rw [hb, Real.sqrt_div (by positivity), Real.sqrt_sq hr.le]
  field_simp

theorem squeeze_mem (t : ℝ) : squeeze t ∈ ball (0 : ℝ) 1 :=
  OpenPartialHomeomorph.univUnitBall.map_source (mem_univ t)

theorem unsqueeze_squeeze (t : ℝ) : unsqueeze (squeeze t) = t :=
  OpenPartialHomeomorph.univUnitBall.left_inv (mem_univ t)

theorem squeeze_unsqueeze (t : ℝ) (ht : t ∈ ball (0 : ℝ) 1) : squeeze (unsqueeze t) = t :=
  OpenPartialHomeomorph.univUnitBall.right_inv ht

/-- This equivalence is valid for arbitrary sets; measurability is not required. -/
theorem normalized_null_iff (r : ℝ) (hr : 0 < r) (N : Set ℝ) :
    volume ((fun t => t / Real.sqrt (t ^ 2 + r ^ 2)) ⁻¹' N) = 0 ↔
      volume (N ∩ Ioo (-1) 1) = 0 := by
  have hf : Differentiable ℝ (fun t => squeeze (t / r)) :=
    (OpenPartialHomeomorph.contDiff_univUnitBall (n := 1)).differentiable (by norm_num) |>.comp
      (differentiable_id.div_const r)
  have hg : DifferentiableOn ℝ (fun t => r * unsqueeze t) (ball (0 : ℝ) 1) :=
    ((OpenPartialHomeomorph.contDiffOn_univUnitBall_symm (n := 1)).differentiableOn (by norm_num)).const_mul r
  have h := null_preimage_iff_of_inverse (fun t => squeeze (t / r)) (fun t => r * unsqueeze t)
    (ball (0 : ℝ) 1) hf hg (fun t => squeeze_mem (t / r))
    (fun t => by rw [unsqueeze_squeeze]; field_simp)
    (fun t ht => by rw [mul_div_cancel_left₀ _ hr.ne', squeeze_unsqueeze t ht]) N
  simpa only [normalized_formula r _ hr, Real.ball_eq_Ioo, zero_sub, zero_add] using h

end ShadowVerification.LatitudeCoordinate
#print axioms ShadowVerification.LatitudeCoordinate.null_preimage_iff_of_inverse
#print axioms ShadowVerification.LatitudeCoordinate.squeeze_formula
#print axioms ShadowVerification.LatitudeCoordinate.normalized_formula
#print axioms ShadowVerification.LatitudeCoordinate.squeeze_mem
#print axioms ShadowVerification.LatitudeCoordinate.unsqueeze_squeeze
#print axioms ShadowVerification.LatitudeCoordinate.squeeze_unsqueeze
#print axioms ShadowVerification.LatitudeCoordinate.normalized_null_iff

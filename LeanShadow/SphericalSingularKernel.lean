import LeanShadow.SphericalKernelTruncation
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Domination and convergence of the spherical kernel regularization

The singular kernel is given value zero at the two parallel points, as
real division by zero does in Lean. The regularization has the same value
there. It converges everywhere and is dominated everywhere by the kernel.
Integrability of one row remains an explicit geometric input.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.SingularKernel
open Spherical OrthogonalHaar SphericalKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def kernel (beta : ℝ) (z : Sphere E × Sphere E) : ℝ := beta / Real.sqrt (gap z)

/-- On unit vectors the maximum in the definition is redundant, giving the manuscript's kernel. -/
theorem kernel_formula (beta : ℝ) (z : Sphere E × Sphere E) :
    kernel beta z = beta / Real.sqrt (1 - (inner ℝ (z.1 : E) (z.2 : E)) ^ 2) := by
  have h := abs_real_inner_le_norm (z.1 : E) (z.2 : E)
  rw [mem_sphere_zero_iff_norm.mp z.1.property,
    mem_sphere_zero_iff_norm.mp z.2.property, mul_one] at h
  have hs : 0 ≤ 1 - (inner ℝ (z.1 : E) (z.2 : E)) ^ 2 := by
    nlinarith [abs_nonneg (inner ℝ (z.1 : E) (z.2 : E)),
      sq_abs (inner ℝ (z.1 : E) (z.2 : E))]
  rw [kernel, gap, max_eq_right hs]

theorem nonneg (beta : ℝ) (hb : 0 ≤ beta) (z : Sphere E × Sphere E) :
    0 ≤ kernel beta z := div_nonneg hb (Real.sqrt_nonneg _)

theorem symmetric (beta : ℝ) (x y : Sphere E) : kernel beta (x,y) = kernel beta (y,x) := by
  simp only [kernel, gap, real_inner_comm (x : E) (y : E)]

theorem cutoff_le (beta delta : ℝ) (hb : 0 ≤ beta) (hd : 0 < delta)
    (z : Sphere E × Sphere E) : cutoff beta delta z ≤ kernel beta z := by
  have hs : 0 ≤ gap z := le_max_left _ _
  rcases eq_or_lt_of_le hs with hz | hz
  · simp [cutoff, kernel, ← hz]
  · have hp : 0 < Real.sqrt (gap z) := Real.sqrt_pos.mpr hz
    rw [cutoff, kernel, div_le_div_iff₀ (by positivity) hp]
    calc
      beta * Real.sqrt (gap z) * Real.sqrt (gap z) = beta * gap z := by
        rw [mul_assoc, Real.mul_self_sqrt hs]
      _ ≤ beta * (gap z + delta) := mul_le_mul_of_nonneg_left (by linarith) hb

def scale (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

theorem scale_pos (j : ℕ) : 0 < scale j := by unfold scale; positivity

theorem scale_tendsto : Tendsto scale atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

theorem cutoff_tendsto (beta : ℝ) (z : Sphere E × Sphere E) :
    Tendsto (fun j => cutoff beta (scale j) z) atTop (𝓝 (kernel beta z)) := by
  have hs : 0 ≤ gap z := le_max_left _ _
  rcases eq_or_lt_of_le hs with hz | hz
  · simp [cutoff, kernel, ← hz]
  · have he : beta * Real.sqrt (gap z) / gap z = kernel beta z := by
      rw [kernel]
      apply (div_eq_div_iff hz.ne' (Real.sqrt_pos.mpr hz).ne').mpr
      rw [mul_assoc, Real.mul_self_sqrt hs]
    have h := (tendsto_const_nhds (x := beta * Real.sqrt (gap z))).div
      (tendsto_const_nhds.add scale_tendsto)
      (show gap z + 0 ≠ 0 by simpa using hz.ne')
    change Tendsto (fun j => beta * Real.sqrt (gap z) / (gap z + scale j))
      atTop (𝓝 (beta * Real.sqrt (gap z) / (gap z + 0))) at h
    simpa only [cutoff, add_zero, he] using h

variable [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

omit [Nontrivial E] in
theorem measurable (beta : ℝ) : Measurable (kernel (E := E) beta) := by
  have hg : Continuous (gap (E := E)) := by unfold gap; fun_prop
  exact measurable_const.div (Real.continuous_sqrt.measurable.comp hg.measurable)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem invariant (beta : ℝ) (R : OrthogonalHaar.Group E) (x y : Sphere E) :
    kernel beta (rotate R x, rotate R y) = kernel beta (x,y) := by
  simp only [kernel, gap, rotate_inner]

theorem rows_integrable (beta : ℝ) (x : Sphere E)
    (hi : Integrable (fun y => kernel beta (x,y)) (probability mu)) (z : Sphere E) :
    Integrable (fun y => kernel beta (z,y)) (probability mu) :=
  SphericalKernel.row_integrable mu _ (invariant beta) x hi z

theorem product_integrable (beta : ℝ) (hb : 0 ≤ beta) (x : Sphere E)
    (hi : Integrable (fun y => kernel beta (x,y)) (probability mu))
    (u v : Lp ℝ 2 (probability mu)) :
    Integrable (fun z : Sphere E × Sphere E => kernel beta z * (u z.1 * v z.2))
      ((probability mu).prod (probability mu)) := by
  apply KernelMeasure.product_integrable (probability mu) (kernel beta)
    (measurable beta) (nonneg beta hb) (∫ y, kernel beta (x,y) ∂probability mu)
    (integral_nonneg fun y => nonneg beta hb (x,y)) (rows_integrable mu beta x hi)
  · intro y
    simp_rw [symmetric beta _ y]
    exact rows_integrable mu beta x hi y
  · intro z
    exact row_integral_eq mu _ (measurable beta) (invariant beta) z x
  · intro z
    simp_rw [symmetric beta _ z]
    exact row_integral_eq mu _ (measurable beta) (invariant beta) z x

omit [Nontrivial E] [mu.IsAddHaarMeasure] in
/-- Dominated convergence makes the common row mass of the error tend to zero. -/
theorem row_error_tendsto (beta : ℝ) (hb : 0 ≤ beta) (x : Sphere E)
    (hi : Integrable (fun y => kernel beta (x,y)) (probability mu)) :
    Tendsto (fun j => ∫ y, kernel beta (x,y) - cutoff beta (scale j) (x,y)
      ∂probability mu) atTop (𝓝 0) := by
  have ht : Tendsto (fun j => ∫ y, kernel beta (x,y) - cutoff beta (scale j) (x,y)
      ∂probability mu) atTop (𝓝 (∫ _y : Sphere E, (0 : ℝ) ∂probability mu)) := by
    apply tendsto_integral_of_dominated_convergence (fun y => kernel beta (x,y))
    · intro j
      exact (((measurable beta).sub (cutoff_continuous beta (scale j) (scale_pos j)).measurable).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · exact hi
    · intro j
      exact Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (cutoff_le beta (scale j) hb (scale_pos j) (x,y)))]
        linarith [cutoff_nonneg beta (scale j) hb (scale_pos j) (x,y)]
    · exact Eventually.of_forall fun y => by
        simpa only [sub_self] using (tendsto_const_nhds (x := kernel beta (x,y))).sub (cutoff_tendsto beta (x,y))
  simpa only [integral_zero] using ht

end ShadowVerification.SingularKernel
#print axioms ShadowVerification.SingularKernel.nonneg
#print axioms ShadowVerification.SingularKernel.symmetric
#print axioms ShadowVerification.SingularKernel.cutoff_le
#print axioms ShadowVerification.SingularKernel.scale_pos
#print axioms ShadowVerification.SingularKernel.scale_tendsto
#print axioms ShadowVerification.SingularKernel.cutoff_tendsto
#print axioms ShadowVerification.SingularKernel.measurable
#print axioms ShadowVerification.SingularKernel.invariant
#print axioms ShadowVerification.SingularKernel.rows_integrable
#print axioms ShadowVerification.SingularKernel.product_integrable
#print axioms ShadowVerification.SingularKernel.row_error_tendsto
#print axioms ShadowVerification.SingularKernel.kernel_formula

import LeanShadow.ConstantMarginalBound
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # From kernel row integrals to an operator-norm bound

These lemmas construct the positive joint measure associated with a kernel.
Tonelli computes its marginals. The constant-marginal bound then controls
the operator, including unbounded kernels with finite row integrals.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.KernelMeasure

variable {X : Type*} [MeasurableSpace X]
  (sigma : Measure X) [IsFiniteMeasure sigma]

def joint (k : X × X → ℝ) : Measure (X × X) :=
  (sigma.prod sigma).withDensity (fun z => ENNReal.ofReal (k z))

theorem first_marginal (f : X × X → ℝ≥0∞) (hf : Measurable f) (c : ℝ≥0∞)
    (hr : ∀ x, (∫⁻ y, f (x,y) ∂sigma) = c) :
    ((sigma.prod sigma).withDensity f).map Prod.fst = c • sigma := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_fst hA, withDensity_apply _ (hA.preimage measurable_fst)]
  have he : Prod.fst ⁻¹' A = A ×ˢ (univ : Set X) := by ext z; simp
  rw [he, setLIntegral_prod _ hf.aemeasurable.restrict]
  simp [hr]

theorem second_marginal (f : X × X → ℝ≥0∞) (hf : Measurable f) (c : ℝ≥0∞)
    (hc : ∀ y, (∫⁻ x, f (x,y) ∂sigma) = c) :
    ((sigma.prod sigma).withDensity f).map Prod.snd = c • sigma := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_snd hA, withDensity_apply _ (hA.preimage measurable_snd)]
  have he : Prod.snd ⁻¹' A = (univ : Set X) ×ˢ A := by ext z; simp
  rw [he, setLIntegral_prod_symm _ hf.aemeasurable.restrict]
  simp [hc]

omit [IsFiniteMeasure sigma] in
theorem pairing (k : X × X → ℝ) (hk : Measurable k) (h0 : ∀ z, 0 ≤ k z)
    (u v : X → ℝ) :
    (∫ z : X × X, u z.1 * v z.2 ∂joint sigma k) =
      ∫ z : X × X, k z * (u z.1 * v z.2) ∂sigma.prod sigma := by
  rw [joint, integral_withDensity_eq_integral_toReal_smul hk.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (h0 _), smul_eq_mul]

/-- Exact constant row and column integrals give the sharp L² bound. -/
theorem norm_le (k : X × X → ℝ) (hk : Measurable k) (h0 : ∀ z, 0 ≤ k z)
    (c : ℝ) (hc : 0 ≤ c)
    (hir : ∀ x, Integrable (fun y => k (x,y)) sigma)
    (hic : ∀ y, Integrable (fun x => k (x,y)) sigma)
    (hr : ∀ x, (∫ y, k (x,y) ∂sigma) = c)
    (hcol : ∀ y, (∫ x, k (x,y) ∂sigma) = c)
    (T : Lp ℝ 2 sigma →L[ℝ] Lp ℝ 2 sigma)
    (hp : ∀ u v, inner ℝ u (T v) =
      ∫ z : X × X, k z * (u z.1 * v z.2) ∂sigma.prod sigma) : ‖T‖ ≤ c := by
  apply ConstantMarginal.norm_le sigma (joint sigma k) T c hc
  · apply first_marginal sigma _ hk.ennreal_ofReal
    intro x
    rw [← ofReal_integral_eq_lintegral_ofReal (hir x) (Eventually.of_forall fun y => h0 (x,y)), hr]
  · apply second_marginal sigma _ hk.ennreal_ofReal
    intro y
    rw [← ofReal_integral_eq_lintegral_ofReal (hic y) (Eventually.of_forall fun x => h0 (x,y)), hcol]
  · intro u v
    rw [pairing sigma k hk h0]
    exact hp u v

/-- Finite constant row and column integrals make the weighted L² product integrable. -/
theorem product_integrable (k : X × X → ℝ) (hk : Measurable k) (h0 : ∀ z, 0 ≤ k z)
    (c : ℝ) (hc : 0 ≤ c)
    (hir : ∀ x, Integrable (fun y => k (x,y)) sigma)
    (hic : ∀ y, Integrable (fun x => k (x,y)) sigma)
    (hr : ∀ x, (∫ y, k (x,y) ∂sigma) = c)
    (hcol : ∀ y, (∫ x, k (x,y) ∂sigma) = c)
    (u v : Lp ℝ 2 sigma) :
    Integrable (fun z : X × X => k z * (u z.1 * v z.2)) (sigma.prod sigma) := by
  have hfst : (joint sigma k).map Prod.fst = ENNReal.ofReal c • sigma := by
    apply first_marginal sigma _ hk.ennreal_ofReal
    intro x
    rw [← ofReal_integral_eq_lintegral_ofReal (hir x) (Eventually.of_forall fun y => h0 (x,y)), hr]
  have hsnd : (joint sigma k).map Prod.snd = ENNReal.ofReal c • sigma := by
    apply second_marginal sigma _ hk.ennreal_ofReal
    intro y
    rw [← ofReal_integral_eq_lintegral_ofReal (hic y) (Eventually.of_forall fun x => h0 (x,y)), hcol]
  have hi := ConstantMarginal.product_integrable sigma (joint sigma k) c hc hfst hsnd u v
  have h := (integrable_withDensity_iff_integrable_smul' hk.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hi
  simpa only [ENNReal.toReal_ofReal (h0 _), smul_eq_mul] using h

end ShadowVerification.KernelMeasure
#print axioms ShadowVerification.KernelMeasure.first_marginal
#print axioms ShadowVerification.KernelMeasure.second_marginal
#print axioms ShadowVerification.KernelMeasure.pairing
#print axioms ShadowVerification.KernelMeasure.norm_le
#print axioms ShadowVerification.KernelMeasure.product_integrable

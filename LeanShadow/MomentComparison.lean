import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Fixed-measure comparison with a superlevel set

The measure-theoretic comparison behind the manuscript's moment estimate.
This module does not compute spherical cap measures or latitude integrals.
-/

set_option autoImplicit false
open MeasureTheory

namespace ShadowVerification

variable {X : Type*}

theorem threshold_indicator_le (A C : Set X) (w : X → ℝ) (τ : ℝ)
    (hinside : ∀ x ∈ C, τ ≤ w x) (houtside : ∀ x ∉ C, w x ≤ τ) :
    A.indicator (fun x => w x - τ) ≤ C.indicator (fun x => w x - τ) := by
  classical
  intro x
  by_cases ha : x ∈ A <;> by_cases hc : x ∈ C
  · simp [ha, hc]
  · simpa [ha, hc] using sub_nonpos.mpr (houtside x hc)
  · simpa [ha, hc] using sub_nonneg.mpr (hinside x hc)
  · simp [ha, hc]

variable [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- Among measurable sets of a prescribed measure, a superlevel set maximizes
the integral of an integrable real weight. -/
theorem superlevel_integral_maximal (A C : Set X) (w : X → ℝ) (τ : ℝ)
    (hA : MeasurableSet A) (hC : MeasurableSet C) (hw : Integrable w μ)
    (hmass : μ A = μ C)
    (hinside : ∀ x ∈ C, τ ≤ w x) (houtside : ∀ x ∉ C, w x ≤ τ) :
    (∫ x in A, w x ∂μ) ≤ ∫ x in C, w x ∂μ := by
  have hf : Integrable (fun x => w x - τ) μ := hw.sub (integrable_const τ)
  have hi := integral_mono (hf.indicator hA) (hf.indicator hC)
    (threshold_indicator_le A C w τ hinside houtside)
  rw [integral_indicator hA, integral_indicator hC] at hi
  rw [integral_sub hw.integrableOn (integrable_const τ),
    integral_sub hw.integrableOn (integrable_const τ)] at hi
  simpa only [setIntegral_const, measureReal_def, hmass, sub_le_sub_iff_right] using hi

/-- Equality identifies the maximizing set almost everywhere away from the
threshold level. A null threshold level therefore gives a.e. uniqueness. -/
theorem superlevel_equality_off_threshold (A C : Set X) (w : X → ℝ) (τ : ℝ)
    (hA : MeasurableSet A) (hC : MeasurableSet C) (hw : Integrable w μ)
    (hmass : μ A = μ C)
    (hinside : ∀ x ∈ C, τ ≤ w x) (houtside : ∀ x ∉ C, w x ≤ τ)
    (heq : (∫ x in A, w x ∂μ) = ∫ x in C, w x ∂μ) :
    ∀ᵐ x ∂μ, w x ≠ τ → (x ∈ A ↔ x ∈ C) := by
  classical
  have hf : Integrable (fun x => w x - τ) μ := hw.sub (integrable_const τ)
  have hint : (∫ x, A.indicator (fun x => w x - τ) x ∂μ) =
      ∫ x, C.indicator (fun x => w x - τ) x ∂μ := by
    rw [integral_indicator hA, integral_indicator hC,
      integral_sub hw.integrableOn (integrable_const τ),
      integral_sub hw.integrableOn (integrable_const τ)]
    simp only [setIntegral_const, measureReal_def, hmass, heq]
  have hae := (integral_eq_iff_of_ae_le (hf.indicator hA) (hf.indicator hC)
    (Filter.Eventually.of_forall (threshold_indicator_le A C w τ hinside houtside))).mp hint
  filter_upwards [hae] with x hx
  intro hne
  by_cases ha : x ∈ A
  · by_cases hc : x ∈ C
    · simp [ha, hc]
    · have hzero : w x - τ = 0 := by simpa [ha, hc] using hx
      exact False.elim (hne (sub_eq_zero.mp hzero))
  · by_cases hc : x ∈ C
    · have hzero : w x - τ = 0 := by simpa [ha, hc] using hx.symm
      exact False.elim (hne (sub_eq_zero.mp hzero))
    · simp [ha, hc]

theorem superlevel_equality_ae (A C : Set X) (w : X → ℝ) (τ : ℝ)
    (hA : MeasurableSet A) (hC : MeasurableSet C) (hw : Integrable w μ)
    (hmass : μ A = μ C)
    (hinside : ∀ x ∈ C, τ ≤ w x) (houtside : ∀ x ∉ C, w x ≤ τ)
    (heq : (∫ x in A, w x ∂μ) = ∫ x in C, w x ∂μ)
    (hlevel : ∀ᵐ x ∂μ, w x ≠ τ) : A =ᵐ[μ] C := by
  have h := superlevel_equality_off_threshold μ A C w τ hA hC hw hmass hinside houtside heq
  filter_upwards [h, hlevel] with x hx hxlevel
  exact propext (hx hxlevel)

end ShadowVerification

#print axioms ShadowVerification.threshold_indicator_le
#print axioms ShadowVerification.superlevel_integral_maximal
#print axioms ShadowVerification.superlevel_equality_off_threshold
#print axioms ShadowVerification.superlevel_equality_ae

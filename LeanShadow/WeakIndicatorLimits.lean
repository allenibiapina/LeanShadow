import LeanShadow.HilbertWeakCompactness
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! # Weak limits of indicator functions

The limits need not be indicators. Testing against indicators proves that
they lie between zero and one almost everywhere; testing against the constant
one function preserves the prescribed masses. Their positive supports are
Borel sets with at least those masses.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.WeakIndicators

variable {X : Type*} [MeasurableSpace X] (nu : Measure X) [IsFiniteMeasure nu]

noncomputable def indicator (A : Set X) (hA : MeasurableSet A) : Lp ℝ 2 nu :=
  indicatorConstLp 2 hA (measure_ne_top _ _) 1

theorem indicator_ae (A : Set X) (hA : MeasurableSet A) :
    (indicator nu A hA : X → ℝ) =ᵐ[nu] A.indicator (fun _ => 1) :=
  indicatorConstLp_coeFn

theorem indicator_inner (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    inner ℝ (indicator nu A hA) (indicator nu B hB) = nu.real (A ∩ B) :=
  L2.real_inner_indicatorConstLp_one_indicatorConstLp_one hA hB

theorem integral_eq_inner (u : Lp ℝ 2 nu) (S : Set X) (hS : MeasurableSet S) :
    (∫ x in S, u x ∂nu) = inner ℝ u (indicator nu S hS) := by
  rw [real_inner_comm]
  exact (L2.inner_indicatorConstLp_one hS (measure_ne_top _ _) u).symm

theorem integrable (u : Lp ℝ 2 nu) : Integrable u nu := by
  have h := integrableOn_Lp_of_measure_ne_top (s := univ) u (by norm_num) (measure_ne_top nu univ)
  simpa only [integrableOn_univ] using h

/-- Every measurable test set has the expected limiting integral. -/
theorem setIntegral_tendsto (A : ℕ → Set X) (hA : ∀ j, MeasurableSet (A j))
    (u : Lp ℝ 2 nu) (hu : HilbertWeak.Converges (fun j => indicator nu (A j) (hA j)) u)
    (S : Set X) (hS : MeasurableSet S) :
    Tendsto (fun j => nu.real (A j ∩ S)) atTop (𝓝 (∫ x in S, u x ∂nu)) := by
  simpa only [indicator_inner, integral_eq_inner nu u S hS] using hu (indicator nu S hS)

/-- Fractional weak limits still satisfy the indicator lower bound. -/
theorem nonneg_ae (A : ℕ → Set X) (hA : ∀ j, MeasurableSet (A j))
    (u : Lp ℝ 2 nu) (hu : HilbertWeak.Converges (fun j => indicator nu (A j) (hA j)) u) :
    ∀ᵐ x ∂nu, 0 ≤ u x := by
  apply ae_nonneg_of_forall_setIntegral_nonneg (integrable nu u)
  intro S hS _
  exact ge_of_tendsto (setIntegral_tendsto nu A hA u hu S hS)
    (Filter.Eventually.of_forall fun _ => measureReal_nonneg)

/-- The upper bound follows by testing against every indicator as well. -/
theorem le_one_ae (A : ℕ → Set X) (hA : ∀ j, MeasurableSet (A j))
    (u : Lp ℝ 2 nu) (hu : HilbertWeak.Converges (fun j => indicator nu (A j) (hA j)) u) :
    ∀ᵐ x ∂nu, u x ≤ 1 := by
  apply ae_le_of_forall_setIntegral_le (integrable nu u) (integrable_const (1 : ℝ))
  intro S hS _
  have h := le_of_tendsto (setIntegral_tendsto nu A hA u hu S hS)
    (Filter.Eventually.of_forall fun j => measureReal_mono (inter_subset_right : A j ∩ S ⊆ S))
  simpa using h

/-- Weak convergence preserves the limiting mass, not just an inequality. -/
theorem integral_eq_mass (A : ℕ → Set X) (hA : ∀ j, MeasurableSet (A j))
    (u : Lp ℝ 2 nu) (hu : HilbertWeak.Converges (fun j => indicator nu (A j) (hA j)) u)
    (p : ℝ) (hp : Tendsto (fun j => nu.real (A j)) atTop (𝓝 p)) :
    (∫ x, u x ∂nu) = p := by
  have h := setIntegral_tendsto nu A hA u hu univ MeasurableSet.univ
  simp only [inter_univ, setIntegral_univ] at h
  exact tendsto_nhds_unique h hp

omit [IsFiniteMeasure nu] in
/-- The positive support of an L² representative is Borel measurable. -/
theorem positiveSupport_measurable (u : Lp ℝ 2 nu) : MeasurableSet {x | 0 < u x} :=
  measurableSet_lt measurable_const (Lp.stronglyMeasurable u).measurable

/-- A fractional density bounded by one has enough mass in its positive support. -/
theorem integral_le_positiveSupport (u : Lp ℝ 2 nu)
    (hu0 : ∀ᵐ x ∂nu, 0 ≤ u x) (hu1 : ∀ᵐ x ∂nu, u x ≤ 1) :
    (∫ x, u x ∂nu) ≤ nu.real {x | 0 < u x} := by
  classical
  let S := {x | 0 < u x}
  have hS : MeasurableSet S := positiveSupport_measurable nu u
  rw [← integral_indicator_one hS]
  apply integral_mono_ae (integrable nu u) ((integrable_const (1 : ℝ)).indicator hS)
  filter_upwards [hu0, hu1] with x hx0 hx1
  by_cases hx : x ∈ S
  · simpa only [Set.indicator_of_mem hx] using hx1
  · rw [Set.indicator_of_notMem hx]
    exact le_of_not_gt hx

/-- Unit-measure indicator functions are bounded in L² by one. -/
theorem indicator_norm_le_one [IsProbabilityMeasure nu] (A : Set X) (hA : MeasurableSet A) :
    ‖indicator nu A hA‖ ≤ 1 := by
  have hsq : ‖indicator nu A hA‖ ^ 2 = nu.real A := by
    rw [← real_inner_self_eq_norm_sq, indicator_inner, inter_self]
  have harea : nu.real A ≤ 1 := by
    apply (measureReal_mono (subset_univ A)).trans_eq
    simp
  nlinarith [norm_nonneg (indicator nu A hA)]

set_option maxHeartbeats 800000 in
/-- The abstract weak compactness theorem applies to the actual L² spaces of
separable probability measures and to both indicator sequences simultaneously. -/
theorem exists_pair_weak_limits [IsProbabilityMeasure nu] [IsSeparable nu]
    (A B : ℕ → Set X) (hA : ∀ j, MeasurableSet (A j)) (hB : ∀ j, MeasurableSet (B j)) :
    ∃ u v : Lp ℝ 2 nu, ∃ s : ℕ → ℕ, StrictMono s ∧
      HilbertWeak.Converges (fun j => indicator nu (A (s j)) (hA (s j))) u ∧
      HilbertWeak.Converges (fun j => indicator nu (B (s j)) (hB (s j))) v :=
    by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  exact HilbertWeak.exists_pair_weak_subsequence _ _ 1 1
    (fun j => indicator_norm_le_one nu (A j) (hA j))
    (fun j => indicator_norm_le_one nu (B j) (hB j))

end ShadowVerification.WeakIndicators
#print axioms ShadowVerification.WeakIndicators.indicator_ae
#print axioms ShadowVerification.WeakIndicators.indicator_inner
#print axioms ShadowVerification.WeakIndicators.integral_eq_inner
#print axioms ShadowVerification.WeakIndicators.integrable
#print axioms ShadowVerification.WeakIndicators.setIntegral_tendsto
#print axioms ShadowVerification.WeakIndicators.nonneg_ae
#print axioms ShadowVerification.WeakIndicators.le_one_ae
#print axioms ShadowVerification.WeakIndicators.integral_eq_mass
#print axioms ShadowVerification.WeakIndicators.positiveSupport_measurable
#print axioms ShadowVerification.WeakIndicators.integral_le_positiveSupport
#print axioms ShadowVerification.WeakIndicators.indicator_norm_le_one
#print axioms ShadowVerification.WeakIndicators.exists_pair_weak_limits

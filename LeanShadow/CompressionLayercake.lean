import LeanShadow.CompressionTail
import Mathlib.MeasureTheory.Integral.Layercake

/-! # The density comparison for high values of a concentrating kernel

Pointwise convergence away from an axis is insufficient: the kernel becomes
unbounded near the axis. Layer cake converts relative mass bounds on its
high superlevel sets into an integral bound. This module proves that analytic
estimate independently of the spherical description of those level sets.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.CompressionLayercake

variable {X : Type*} [MeasurableSpace X]

/-- Domination of all superlevel masses gives domination of integrals. -/
theorem lintegral_le_of_superlevel_domination (nu eta : Measure X) (f : X → ℝ)
    (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (hlevel : ∀ t > 0, eta {x | t ≤ f x} ≤ c * nu {x | t ≤ f x}) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂eta ≤ c * ∫⁻ x, ENNReal.ofReal (f x) ∂nu := by
  rw [lintegral_eq_lintegral_meas_le eta (Eventually.of_forall hpos) hf.aemeasurable,
    lintegral_eq_lintegral_meas_le nu (Eventually.of_forall hpos) hf.aemeasurable,
    ← lintegral_const_mul' c _ hc]
  apply lintegral_mono_ae
  exact (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => hlevel t ht)

theorem integral_le_of_superlevel_domination (nu eta : Measure X) (f : X → ℝ)
    (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x) (hnu : Integrable f nu) (heta : Integrable f eta)
    (c : ℝ) (hc : 0 ≤ c)
    (hlevel : ∀ t > 0, eta {x | t ≤ f x} ≤ ENNReal.ofReal c * nu {x | t ≤ f x}) :
    ∫ x, f x ∂eta ≤ c * ∫ x, f x ∂nu := by
  have h := lintegral_le_of_superlevel_domination nu eta f hf hpos (ENNReal.ofReal c)
    ENNReal.ofReal_ne_top hlevel
  rw [← ofReal_integral_eq_lintegral_ofReal heta (Eventually.of_forall hpos),
    ← ofReal_integral_eq_lintegral_ofReal hnu (Eventually.of_forall hpos),
    ← ENNReal.ofReal_mul hc] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc (integral_nonneg hpos))).mp h

omit [MeasurableSpace X] in
/-- Truncation shifts a positive superlevel by exactly the truncation height. -/
theorem positive_part_superlevel (q : X → ℝ) (M t : ℝ) (ht : 0 < t) :
    {x | t ≤ max (q x - M) 0} = {x | t + M ≤ q x} := by
  ext x
  simp only [mem_ofPred_eq, le_max_iff]
  constructor
  · intro h
    rcases h with h | h <;> linarith
  · intro h
    exact Or.inl (by linarith)

/-- If all superlevel sets above M contain at most an epsilon fraction of A,
then the total kernel integral over A is at most epsilon + M. The kernel is
normalized, but may be arbitrarily large near its concentration point. -/
theorem integral_le_of_high_level_density (nu : Measure X) [IsProbabilityMeasure nu]
    (A : Set X) (q : X → ℝ) (hq : Measurable q)
    (hqi : Integrable q nu) (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∫ x, q x ∂nu = 1)
    (eps M : ℝ) (heps : 0 ≤ eps) (hM : 0 ≤ M)
    (hlevel : ∀ t > M, nu (A ∩ {x | t ≤ q x}) ≤ ENNReal.ofReal eps * nu {x | t ≤ q x}) :
    ∫ x in A, q x ∂nu ≤ eps + M := by
  let f : X → ℝ := fun x => max (q x - M) 0
  have hf : Measurable f := (hq.sub measurable_const).max measurable_const
  have hfi : Integrable f nu := (hqi.sub (integrable_const M)).pos_part
  have hf0 (x : X) : 0 ≤ f x := le_max_right _ _
  have hfq (x : X) : f x ≤ q x := max_le (by linarith) (hq0 x)
  have hshift : ∫ x in A, f x ∂nu ≤ eps * ∫ x, f x ∂nu := by
    apply integral_le_of_superlevel_domination nu (nu.restrict A) f hf hf0 hfi hfi.integrableOn eps heps
    intro t ht
    rw [show {x | t ≤ f x} = {x | t + M ≤ q x} from positive_part_superlevel q M t ht,
      Measure.restrict_apply (measurableSet_le measurable_const hq), inter_comm]
    exact hlevel (t + M) (by linarith)
  have hwhole : ∫ x, f x ∂nu ≤ 1 := by
    rw [← hq1]
    exact integral_mono hfi hqi hfq
  have ha : nu.real A ≤ 1 := by
    exact measureReal_le_one
  calc
    (∫ x in A, q x ∂nu) ≤ ∫ x in A, f x + M ∂nu := by
      apply integral_mono hqi.integrableOn (hfi.integrableOn.add (integrable_const M))
      intro x
      have := le_max_left (q x - M) 0
      dsimp [f]
      linarith
    _ = (∫ x in A, f x ∂nu) + nu.real A * M := by
      rw [integral_add hfi.integrableOn (integrable_const M)]
      simp [measureReal_def]
    _ ≤ eps * (∫ x, f x ∂nu) + nu.real A * M := by linarith
    _ ≤ eps + M := by nlinarith

end ShadowVerification.CompressionLayercake
#print axioms ShadowVerification.CompressionLayercake.lintegral_le_of_superlevel_domination
#print axioms ShadowVerification.CompressionLayercake.integral_le_of_superlevel_domination
#print axioms ShadowVerification.CompressionLayercake.positive_part_superlevel
#print axioms ShadowVerification.CompressionLayercake.integral_le_of_high_level_density

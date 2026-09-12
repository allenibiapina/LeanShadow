import LeanShadow.CompactFeatureOperator
import LeanShadow.WeakIndicatorLimits
import Mathlib.MeasureTheory.Integral.Prod

/-! # Actual integral operators with continuous kernels on compact spaces

Kernel sections are converted to genuine L² vectors, then passed to the
compact feature operator. The resulting map has the expected pointwise
integral and bilinear pairing; compactness is proved, not a hypothesis.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.ContinuousKernel

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (mu : Measure X) (nu : Measure Y) [IsFiniteMeasure mu] [IsFiniteMeasure nu]

def sections (k : C(X × Y,ℝ)) : C(X,Lp ℝ 2 nu) :=
  ⟨fun x => ContinuousMap.toLp 2 nu ℝ (k.curry x),
    (ContinuousMap.toLp 2 nu ℝ).continuous.comp k.curry.continuous⟩

def operator (k : C(X × Y,ℝ)) : Lp ℝ 2 nu →L[ℝ] Lp ℝ 2 mu :=
  CompactFeature.operator mu (sections nu k)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem section_pairing (k : C(X × Y,ℝ)) (v : Lp ℝ 2 nu) (x : X) :
    inner ℝ v (sections nu k x) = ∫ y, k (x,y) * v y ∂nu := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) nu (k.curry x)] with y hy
  change inner ℝ (v y) (ContinuousMap.toLp 2 nu ℝ (k.curry x) y) = _
  rw [hy]
  simp only [RCLike.inner_apply, conj_trivial, ContinuousMap.curry_apply, mul_comm]

theorem coe_ae (k : C(X × Y,ℝ)) (v : Lp ℝ 2 nu) :
    (operator mu nu k v : X → ℝ) =ᵐ[mu] (fun x => ∫ y, k (x,y) * v y ∂nu) := by
  filter_upwards [CompactFeature.coe_ae mu (sections nu k) v] with x hx
  exact hx.trans (section_pairing nu k v x)

variable [OpensMeasurableSpace (X × Y)]

omit [BorelSpace X] [BorelSpace Y] in
theorem product_integrable (k : C(X × Y,ℝ)) (u : Lp ℝ 2 mu) (v : Lp ℝ 2 nu) :
    Integrable (fun z : X × Y => k z * (u z.1 * v z.2)) (mu.prod nu) :=
  ((WeakIndicators.integrable mu u).mul_prod (WeakIndicators.integrable nu v)).bdd_mul
    k.continuous.aestronglyMeasurable
    (Eventually.of_forall fun z => k.norm_coe_le_norm z)

/-- The bilinear pairing uses the product measure and the literal kernel. -/
theorem pairing (k : C(X × Y,ℝ)) (u : Lp ℝ 2 mu) (v : Lp ℝ 2 nu) :
    inner ℝ u (operator mu nu k v) =
      ∫ z : X × Y, k z * (u z.1 * v z.2) ∂mu.prod nu := by
  rw [L2.inner_def, integral_prod _ (product_integrable mu nu k u v)]
  apply integral_congr_ae
  filter_upwards [coe_ae mu nu k v] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [← integral_mul_const]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by ring

omit [OpensMeasurableSpace (X × Y)] in
/-- Every continuous kernel on these compact finite measure spaces gives a compact operator. -/
theorem compact [IsSeparable nu] (k : C(X × Y,ℝ)) :
    IsCompactOperator (operator mu nu k) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  exact CompactFeature.compact mu (sections nu k)

end ShadowVerification.ContinuousKernel
#print axioms ShadowVerification.ContinuousKernel.section_pairing
#print axioms ShadowVerification.ContinuousKernel.coe_ae
#print axioms ShadowVerification.ContinuousKernel.product_integrable
#print axioms ShadowVerification.ContinuousKernel.pairing
#print axioms ShadowVerification.ContinuousKernel.compact

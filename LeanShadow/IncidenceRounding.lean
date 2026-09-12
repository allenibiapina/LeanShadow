import LeanShadow.WeakIndicatorLimits
import Mathlib.MeasureTheory.Measure.Prod

/-! # Rounding a fractional pair with zero incidence

The incidence measure is a measure on pairs with the prescribed marginals.
These lemmas do not assume that it is the product measure. The marginal
identities justify all changes of representatives and provide integrability
of products of L² functions. Nonnegativity then turns a zero bilinear
integral into zero incidence between positive supports.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.IncidenceRounding

variable {X : Type*} [MeasurableSpace X] (nu : Measure X) [IsFiniteMeasure nu]
  (rho : Measure (X × X))
  (hfst : MeasurePreserving Prod.fst rho nu)
  (hsnd : MeasurePreserving Prod.snd rho nu)

include hfst hsnd

omit [IsFiniteMeasure nu] in
theorem product_integrable (u v : Lp ℝ 2 nu) :
    Integrable (fun z : X × X => u z.1 * v z.2) rho :=
  ((Lp.memLp u).comp_measurePreserving hfst).integrable_mul
    ((Lp.memLp v).comp_measurePreserving hsnd)

omit [IsFiniteMeasure nu] in
theorem product_nonneg (u v : Lp ℝ 2 nu)
    (hu : ∀ᵐ x ∂nu, 0 ≤ u x) (hv : ∀ᵐ y ∂nu, 0 ≤ v y) :
    ∀ᵐ z ∂rho, 0 ≤ u z.1 * v z.2 := by
  filter_upwards [hfst.quasiMeasurePreserving.ae hu, hsnd.quasiMeasurePreserving.ae hv] with z hz hw
  exact mul_nonneg hz hw

omit [IsFiniteMeasure nu] in
/-- Zero bilinear integral implies zero incidence between positive supports. -/
theorem positiveSupports_incidence_zero (u v : Lp ℝ 2 nu)
    (hu : ∀ᵐ x ∂nu, 0 ≤ u x) (hv : ∀ᵐ y ∂nu, 0 ≤ v y)
    (hz : (∫ z, u z.1 * v z.2 ∂rho) = 0) :
    rho ({x | 0 < u x} ×ˢ {y | 0 < v y}) = 0 := by
  have he := (integral_eq_zero_iff_of_nonneg_ae (product_nonneg nu rho hfst hsnd u v hu hv)
    (product_integrable nu rho hfst hsnd u v)).mp hz
  have hn : ∀ᵐ z ∂rho, z ∉ ({x | 0 < u x} ×ˢ {y | 0 < v y}) := by
    filter_upwards [he] with z hz hmem
    have hp : 0 < u z.1 * v z.2 := mul_pos hmem.1 hmem.2
    exact (ne_of_gt hp) hz
  simpa only [not_not, ofPred_mem_eq] using (ae_iff.mp hn)

/-- The L² indicators compute the literal measurable product incidence. -/
theorem indicator_product_integral (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫ z : X × X, WeakIndicators.indicator nu A hA z.1 *
      WeakIndicators.indicator nu B hB z.2 ∂rho) = rho.real (A ×ˢ B) := by
  classical
  rw [← integral_indicator_one (hA.prod hB)]
  apply integral_congr_ae
  filter_upwards [hfst.quasiMeasurePreserving.ae (WeakIndicators.indicator_ae nu A hA),
    hsnd.quasiMeasurePreserving.ae (WeakIndicators.indicator_ae nu B hB)] with z hz hw
  rw [hz, hw]
  by_cases hx : z.1 ∈ A <;> by_cases hy : z.2 ∈ B <;> simp [hx, hy]

omit hfst hsnd in
/-- If incidence is supported on a forbidden relation, an avoiding pair has
zero incidence. This uses literal avoidance, not an a.e. substitute. -/
theorem incidence_zero_of_avoids (R : X → X → Prop)
    (hR : ∀ᵐ z ∂rho, R z.1 z.2) (A B : Set X)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, ¬R x y) : rho (A ×ˢ B) = 0 := by
  have hn : ∀ᵐ z ∂rho, z ∉ A ×ˢ B := by
    filter_upwards [hR] with z hz hmem
    exact hAB z.1 hmem.1 z.2 hmem.2 hz
  simpa only [not_not, ofPred_mem_eq] using (ae_iff.mp hn)

end ShadowVerification.IncidenceRounding
#print axioms ShadowVerification.IncidenceRounding.product_integrable
#print axioms ShadowVerification.IncidenceRounding.product_nonneg
#print axioms ShadowVerification.IncidenceRounding.positiveSupports_incidence_zero
#print axioms ShadowVerification.IncidenceRounding.indicator_product_integral
#print axioms ShadowVerification.IncidenceRounding.incidence_zero_of_avoids

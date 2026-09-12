import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-! # Differentiation over a compact measured parameter space

Compactness supplies the uniform domination needed to differentiate an
integral. There is no assumption that the desired integral identity holds.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Metric
open scoped Topology
namespace ShadowVerification.Parametric

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Joint continuity of the integrand and its actual parameter derivative
allows differentiation against any finite measure on a compact space. -/
theorem hasDerivAt_integral_compact (mu : Measure X) [IsFiniteMeasure mu]
    (F D : ℝ → X → ℝ) (t₀ : ℝ)
    (hF : Continuous (fun p : ℝ × X => F p.1 p.2))
    (hD : Continuous (fun p : ℝ × X => D p.1 p.2))
    (hd : ∀ t x, HasDerivAt (fun s => F s x) (D t x) t) :
    HasDerivAt (fun t => ∫ x, F t x ∂mu) (∫ x, D t₀ x ∂mu) t₀ := by
  have hFt : ∀ t, Continuous (F t) := fun t => hF.comp (continuous_const.prodMk continuous_id)
  have hDt : ∀ t, Continuous (D t) := fun t => hD.comp (continuous_const.prodMk continuous_id)
  have hK : IsCompact ((closedBall t₀ 1) ×ˢ (univ : Set X)) :=
    (isCompact_closedBall t₀ 1).prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.bddAbove_image hD.norm.continuousOn
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := ball t₀ 1) (bound := fun _ => C) (ball_mem_nhds t₀ (by norm_num))
    (Filter.Eventually.of_forall (fun t => (hFt t).aestronglyMeasurable))
    ((hFt t₀).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hDt t₀).aestronglyMeasurable _ (integrable_const C) _).2
  · apply Filter.Eventually.of_forall
    intro x t ht
    exact hC ⟨(t, x), ⟨mem_closedBall.mpr (mem_ball.mp ht).le, mem_univ x⟩, rfl⟩
  · exact Filter.Eventually.of_forall (fun x t _ => hd t x)

/-- The same result for the second derivative, using the proved first-order
formula as an equality of derivative functions. -/
theorem second_deriv_integral_compact (mu : Measure X) [IsFiniteMeasure mu]
    (F D DD : ℝ → X → ℝ) (t₀ : ℝ)
    (hF : Continuous (fun p : ℝ × X => F p.1 p.2))
    (hD : Continuous (fun p : ℝ × X => D p.1 p.2))
    (hDD : Continuous (fun p : ℝ × X => DD p.1 p.2))
    (hd : ∀ t x, HasDerivAt (fun s => F s x) (D t x) t)
    (hdd : ∀ t x, HasDerivAt (fun s => D s x) (DD t x) t) :
    deriv (deriv (fun t => ∫ x, F t x ∂mu)) t₀ = ∫ x, DD t₀ x ∂mu := by
  have heq : deriv (fun t => ∫ x, F t x ∂mu) = fun t => ∫ x, D t x ∂mu :=
    funext (fun t => (hasDerivAt_integral_compact mu F D t hF hD hd).deriv)
  rw [heq]
  exact (hasDerivAt_integral_compact mu D DD t₀ hD hDD hdd).deriv

end ShadowVerification.Parametric
#print axioms ShadowVerification.Parametric.hasDerivAt_integral_compact
#print axioms ShadowVerification.Parametric.second_deriv_integral_compact

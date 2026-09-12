import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.Topology.Order.IntermediateValue

/-! # Exact cuts by a measurable real coordinate with null levels

This elementary form of nonatomic trimming uses dominated convergence and
the intermediate value theorem. The coordinate need not be continuous.
It will be chosen invariant under the antipodal map in the spherical application.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.Trimming

variable {X : Type*} [MeasurableSpace X] (nu : Measure X) [IsFiniteMeasure nu]
  (c : X → ℝ) (hc : Measurable c)

noncomputable def cutMass (t : ℝ) : ℝ := nu.real {x | c x ≤ t}

include hc

omit [IsFiniteMeasure nu] in
theorem cutMass_integral (t : ℝ) :
    cutMass nu c t = ∫ x, (if c x ≤ t then 1 else 0 : ℝ) ∂nu := by
  classical
  symm
  exact integral_indicator_one (measurableSet_le hc measurable_const)

/-- Null level sets remove the sole discontinuity of each pointwise indicator. -/
theorem cutMass_continuous (hnull : ∀ t, nu {x | c x = t} = 0) :
    Continuous (cutMass nu c) := by
  classical
  rw [continuous_iff_continuousAt]
  intro t
  change ContinuousAt (fun s => cutMass nu c s) t
  simp_rw [cutMass_integral nu c hc]
  apply continuousAt_of_dominated (bound := fun _ => (1 : ℝ))
  · exact Filter.Eventually.of_forall fun s =>
      ((measurable_const.ite (measurableSet_le hc measurable_const)
        measurable_const) : Measurable (fun x => if c x ≤ s then (1 : ℝ) else 0)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun _ => Filter.Eventually.of_forall fun _ => by
      split_ifs <;> norm_num
  · exact integrable_const 1
  · have he : ∀ᵐ x ∂nu, c x ≠ t := by
      simpa only [ae_iff, not_not] using hnull t
    filter_upwards [he] with x hx
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · apply (continuousAt_const (y := (1 : ℝ))).congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds hlt] with s hs
      simp [hs.le]
    · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [eventually_lt_nhds hgt] with s hs
      simp [not_le.mpr hs]

theorem cutMass_tendsto_atBot : Tendsto (cutMass nu c) atBot (𝓝 0) := by
  classical
  change Tendsto (fun s => cutMass nu c s) _ _
  simp_rw [cutMass_integral nu c hc]
  have h := tendsto_integral_filter_of_dominated_convergence (μ := nu) (l := atBot)
    (F := fun t x => if c x ≤ t then (1 : ℝ) else 0) (f := fun _ => (0 : ℝ))
    (fun _ => (1 : ℝ))
    (Filter.Eventually.of_forall fun _ =>
      (measurable_const.ite (measurableSet_le hc measurable_const)
        measurable_const).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => Filter.Eventually.of_forall fun _ => by
      split_ifs <;> norm_num)
    (integrable_const 1) ?_
  · simpa using h
  · exact Filter.Eventually.of_forall fun x => tendsto_const_nhds.congr'
      (by filter_upwards [eventually_lt_atBot (c x)] with t ht; simp [not_le.mpr ht])

theorem cutMass_tendsto_atTop :
    Tendsto (cutMass nu c) atTop (𝓝 (nu.real univ)) := by
  classical
  change Tendsto (fun s => cutMass nu c s) _ _
  simp_rw [cutMass_integral nu c hc]
  have h := tendsto_integral_filter_of_dominated_convergence (μ := nu) (l := atTop)
    (F := fun t x => if c x ≤ t then (1 : ℝ) else 0) (f := fun _ => (1 : ℝ))
    (fun _ => (1 : ℝ))
    (Filter.Eventually.of_forall fun _ =>
      (measurable_const.ite (measurableSet_le hc measurable_const)
        measurable_const).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => Filter.Eventually.of_forall fun _ => by
      split_ifs <;> norm_num)
    (integrable_const 1) ?_
  · simpa using h
  · exact Filter.Eventually.of_forall fun x => tendsto_const_nhds.congr'
      (by filter_upwards [eventually_ge_atTop (c x)] with t ht; simp [ht])

/-- Every strictly intermediate mass is realized by a threshold cut. -/
theorem exists_cutMass_eq (hnull : ∀ t, nu {x | c x = t} = 0)
    (p : ℝ) (hp : 0 < p) (hp1 : p < nu.real univ) :
    ∃ t, cutMass nu c t = p := by
  have h := isPreconnected_univ.intermediate_value_Ioo
    (l₁ := atBot) (l₂ := atTop) (by simp) (by simp)
    (cutMass_continuous nu c hc hnull).continuousOn
    (cutMass_tendsto_atBot nu c hc) (cutMass_tendsto_atTop nu c hc) ⟨hp, hp1⟩
  obtain ⟨t, _, ht⟩ := h
  exact ⟨t, ht⟩

end ShadowVerification.Trimming
#print axioms ShadowVerification.Trimming.cutMass_integral
#print axioms ShadowVerification.Trimming.cutMass_continuous
#print axioms ShadowVerification.Trimming.cutMass_tendsto_atBot
#print axioms ShadowVerification.Trimming.cutMass_tendsto_atTop
#print axioms ShadowVerification.Trimming.exists_cutMass_eq

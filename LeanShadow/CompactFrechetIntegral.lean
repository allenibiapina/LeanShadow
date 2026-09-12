import LeanShadow.CompactParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Local Fréchet differentiation of integrals over compact spaces

The parameter may range over an arbitrary proper real normed space. All
bounds are obtained on a compact neighbourhood, so the hypotheses only
concern an open parameter domain. This is needed for invertible operators:
the density need not be regular at singular operators outside that domain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Metric
open scoped Topology

namespace ShadowVerification.Parametric

variable {P X F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ P] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedSpace ℝ F] in
/-- A jointly continuous family on an open domain has a single bound on
a sufficiently small parameter ball times the entire compact fibre. -/
theorem local_uniform_bound (U : Set P) (hU : IsOpen U) (F₀ : P → X → F)
    (hF : ContinuousOn (fun z : P × X => F₀ z.1 z.2) (U ×ˢ univ))
    (p : P) (hp : p ∈ U) :
    ∃ r > 0, ball p r ⊆ U ∧ ∃ C : ℝ,
      ∀ q ∈ ball p r, ∀ x : X, ‖F₀ q x‖ ≤ C := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  have hr : 0 < ε / 2 := half_pos hε
  have hclosed : closedBall p (ε / 2) ⊆ U := by
    intro q hq
    exact hsub (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hq) (by linarith)))
  have hK : IsCompact (closedBall p (ε / 2) ×ˢ (univ : Set X)) :=
    (isCompact_closedBall p (ε / 2)).prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.bddAbove_image (hF.norm.mono (by
    intro z hz
    exact ⟨hclosed hz.1, hz.2⟩))
  refine ⟨ε / 2, hr, fun q hq => hclosed (ball_subset_closedBall hq), C, ?_⟩
  intro q hq x
  exact hC ⟨(q, x), ⟨ball_subset_closedBall hq, mem_univ x⟩, rfl⟩

omit [NormedSpace ℝ P] [ProperSpace P] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [NormedSpace ℝ F] in
/-- Joint continuity implies continuity of every compact-fibre slice. -/
theorem continuous_fibre (U : Set P) (F₀ : P → X → F)
    (hF : ContinuousOn (fun z : P × X => F₀ z.1 z.2) (U ×ˢ univ))
    (p : P) (hp : p ∈ U) : Continuous (F₀ p) := by
  simpa only [Function.comp_def, id_eq] using! hF.comp_continuous
    (continuous_const.prodMk continuous_id) (fun x => ⟨hp, mem_univ x⟩)

omit [NormedSpace ℝ P] in
/-- Continuity of the integral is local in the parameter, with domination
proved using the compact fibre and a compact parameter neighbourhood. -/
theorem continuousAt_integral_compact_on (mu : Measure X) [IsFiniteMeasure mu]
    (U : Set P) (hU : IsOpen U) (F₀ : P → X → F)
    (hF : ContinuousOn (fun z : P × X => F₀ z.1 z.2) (U ×ˢ univ))
    (p : P) (hp : p ∈ U) : ContinuousAt (fun q => ∫ x, F₀ q x ∂mu) p := by
  obtain ⟨r, hr, hsub, C, hC⟩ := local_uniform_bound U hU F₀ hF p hp
  apply continuousAt_of_dominated (bound := fun _ => C)
  · filter_upwards [hU.mem_nhds hp] with q hq
    exact (continuous_fibre U F₀ hF q hq).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds p hr] with q hq
    exact Filter.Eventually.of_forall (hC q hq)
  · exact integrable_const C
  · apply Filter.Eventually.of_forall
    intro x
    have hc := hF.continuousAt ((hU.prod (isOpen_univ : IsOpen (univ : Set X))).mem_nhds
      (show (p, x) ∈ U ×ˢ (univ : Set X) from ⟨hp, mem_univ x⟩))
    simpa only [Function.comp_def] using
      hc.comp (f := fun q : P => (q, x)) (continuousAt_id.prodMk continuousAt_const)

/-- The derivative is the integral of the actual Fréchet derivatives. -/
theorem hasFDerivAt_integral_compact_on (mu : Measure X) [IsFiniteMeasure mu]
    (U : Set P) (hU : IsOpen U) (F₀ : P → X → F) (D : P → X → P →L[ℝ] F)
    (hF : ContinuousOn (fun z : P × X => F₀ z.1 z.2) (U ×ˢ univ))
    (hD : ContinuousOn (fun z : P × X => D z.1 z.2) (U ×ˢ univ))
    (hd : ∀ q ∈ U, ∀ x, HasFDerivAt (fun t => F₀ t x) (D q x) q)
    (p : P) (hp : p ∈ U) :
    HasFDerivAt (fun q => ∫ x, F₀ q x ∂mu) (∫ x, D p x ∂mu) p := by
  obtain ⟨r, hr, hsub, C, hC⟩ := local_uniform_bound U hU D hD p hp
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball p r) (bound := fun _ => C) (ball_mem_nhds p hr)
  · filter_upwards [hU.mem_nhds hp] with q hq
    exact (continuous_fibre U F₀ hF q hq).aestronglyMeasurable
  · exact (continuous_fibre U F₀ hF p hp).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (continuous_fibre U D hD p hp).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x q hq => hC q hq x)
  · exact integrable_const C
  · exact Filter.Eventually.of_forall (fun x q hq => hd q (hsub hq) x)

/-- Two continuous derivative families give genuine joint `C²` regularity
of the integral, not just differentiability along selected curves. -/
theorem contDiffOn_two_integral_compact (mu : Measure X) [IsFiniteMeasure mu]
    (U : Set P) (hU : IsOpen U) (F₀ : P → X → F)
    (D : P → X → P →L[ℝ] F) (DD : P → X → P →L[ℝ] P →L[ℝ] F)
    (hF : ContinuousOn (fun z : P × X => F₀ z.1 z.2) (U ×ˢ univ))
    (hD : ContinuousOn (fun z : P × X => D z.1 z.2) (U ×ˢ univ))
    (hDD : ContinuousOn (fun z : P × X => DD z.1 z.2) (U ×ˢ univ))
    (hd : ∀ q ∈ U, ∀ x, HasFDerivAt (fun t => F₀ t x) (D q x) q)
    (hdd : ∀ q ∈ U, ∀ x, HasFDerivAt (fun t => D t x) (DD q x) q) :
    ContDiffOn ℝ 2 (fun q => ∫ x, F₀ q x ∂mu) U := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  apply (contDiffAt_succ_iff_hasFDerivAt (n := 1)).mpr
  refine ⟨fun q => ∫ x, D q x ∂mu, ⟨U, hU.mem_nhds hp, ?_⟩, ?_⟩
  · exact fun q hq => hasFDerivAt_integral_compact_on mu U hU F₀ D hF hD hd q hq
  · apply (contDiffAt_succ_iff_hasFDerivAt (n := 0)).mpr
    refine ⟨fun q => ∫ x, DD q x ∂mu, ⟨U, hU.mem_nhds hp, ?_⟩, ?_⟩
    · exact fun q hq => hasFDerivAt_integral_compact_on mu U hU D DD hD hDD hdd q hq
    · have hc : ContinuousOn (fun q => ∫ x, DD q x ∂mu) U :=
        fun q hq => (continuousAt_integral_compact_on mu U hU DD hDD q hq).continuousWithinAt
      exact (contDiffOn_zero.mpr hc).contDiffAt (hU.mem_nhds hp)

end ShadowVerification.Parametric

#print axioms ShadowVerification.Parametric.local_uniform_bound
#print axioms ShadowVerification.Parametric.continuous_fibre
#print axioms ShadowVerification.Parametric.continuousAt_integral_compact_on
#print axioms ShadowVerification.Parametric.hasFDerivAt_integral_compact_on
#print axioms ShadowVerification.Parametric.contDiffOn_two_integral_compact

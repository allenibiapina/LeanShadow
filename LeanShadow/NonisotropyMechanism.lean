import LeanShadow.EllipticMaximum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Analytic.Uniqueness

/-! # The analytic mechanism in the nonisotropy proof

These are conditional theorems about actual differential operators, analytic
functions, and derivatives. They do not define the measure of a projectively
transformed set. The geometric application must construct those functions and
prove each displayed hypothesis; that application is not yet formalized.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace ShadowVerification.Nonisotropy
open Elliptic

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E] [NormedAddCommGroup F] [Fintype ι]

/-- The positive source term vanishes near an interior maximum. This invokes
the proved strong maximum principle, rather than assuming local constancy. -/
theorem source_zero_near_maximum
    (V : ι → E → E) (b : E → E) (u : E → ℝ) (G : E → F) (x₀ : E)
    (R lam C B c : ℝ) (hR : 0 < R) (hlam : 0 < lam)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hcpos : 0 < c) (hu : Continuous u)
    (hmax : ∀ x, ‖x - x₀‖ < R → u x ≤ u x₀)
    (hsmooth : ∀ x, ‖x - x₀‖ < R → ∀ v : E,
      ContDiffAt ℝ 2 (fun t : ℝ => u (x + t • v)) 0)
    (hsource : ∀ x, ‖x - x₀‖ < R → c * ‖G x‖ ^ 2 ≤ frameOp V b u x)
    (hell : ∀ x, ‖x - x₀‖ < R → ∀ v : E,
      lam * ‖v‖ ^ 2 ≤ ∑ i, (inner ℝ v (V i x)) ^ 2)
    (htrace : ∀ x, ‖x - x₀‖ < R → (∑ i, ‖V i x‖ ^ 2) ≤ C)
    (hdrift : ∀ x, ‖x - x₀‖ < R → ‖b x‖ ≤ B) :
    ∀ x, ‖x - x₀‖ < R / 4 → u x = u x₀ ∧ G x = 0 := by
  have hsub : ∀ x, ‖x - x₀‖ < R → 0 ≤ frameOp V b u x :=
    fun x hx => (mul_nonneg hcpos.le (sq_nonneg _)).trans (hsource x hx)
  have hconst := local_strong_maximum V b u x₀ R lam C B hR hlam hC hB
    hu hmax hsmooth hsub hell htrace hdrift
  intro x hx
  refine ⟨hconst x hx, ?_⟩
  have hxR : ‖x - x₀‖ < R := by linarith
  have hm : IsLocalMax u x := by
    have hopen : IsOpen {y : E | ‖y - x₀‖ < R} :=
      isOpen_lt (show Continuous (fun y : E => ‖y - x₀‖) by fun_prop) continuous_const
    filter_upwards [hopen.mem_nhds hxR] with y hy
    change u y ≤ u x
    rw [hconst x hx]
    exact hmax y hy
  have hnonpos := frameOp_nonpos_at_max V b hu.continuousAt hm
  have hsq : ‖G x‖ ^ 2 ≤ 0 := by
    by_contra! hp
    have hp' := mul_pos hcpos hp
    have hn := (hsource x hxR).trans hnonpos
    linarith
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (G x)])

omit [ProperSpace E] in
/-- Zero Fréchet derivative on a ball implies local constancy. The derivative
is mathlib's actual Fréchet derivative, not a formal gradient variable. -/
theorem locally_constant_of_derivative_zero
    (a : E → ℝ) (x₀ : E) (r : ℝ) (hr : 0 < r)
    (ha : DifferentiableOn ℝ a (Metric.ball x₀ r))
    (hd : ∀ x ∈ Metric.ball x₀ r, fderiv ℝ a x = 0) :
    a =ᶠ[𝓝 x₀] (fun _ => a x₀) := by
  filter_upwards [Metric.ball_mem_nhds x₀ hr] with x hx
  exact Metric.isOpen_ball.is_const_of_fderiv_eq_zero
    (convex_ball x₀ r).isPreconnected ha (fun y hy => hd y hy)
    hx (Metric.mem_ball_self hr)

/-- The complete analytic contradiction used after constructing the elliptic
operator. The missing geometric application must supply its coefficient
bounds, its source inequality, and the relation between `G` and the derivative
of the transformed-area function `a`. Analyticity and nonconstancy are explicit
premises, and no nonisotropy conclusion is assumed. -/
theorem elliptic_analytic_contradiction
    (V : ι → E → E) (b : E → E) (u a : E → ℝ) (G : E → F) (x₀ : E)
    (R lam C B c : ℝ) (hR : 0 < R) (hlam : 0 < lam)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hcpos : 0 < c) (hu : Continuous u)
    (hmax : ∀ x, ‖x - x₀‖ < R → u x ≤ u x₀)
    (hsmooth : ∀ x, ‖x - x₀‖ < R → ∀ v : E,
      ContDiffAt ℝ 2 (fun t : ℝ => u (x + t • v)) 0)
    (hsource : ∀ x, ‖x - x₀‖ < R → c * ‖G x‖ ^ 2 ≤ frameOp V b u x)
    (hell : ∀ x, ‖x - x₀‖ < R → ∀ v : E,
      lam * ‖v‖ ^ 2 ≤ ∑ i, (inner ℝ v (V i x)) ^ 2)
    (htrace : ∀ x, ‖x - x₀‖ < R → (∑ i, ‖V i x‖ ^ 2) ≤ C)
    (hdrift : ∀ x, ‖x - x₀‖ < R → ‖b x‖ ≤ B)
    (ha : AnalyticOnNhd ℝ a univ)
    (hgradient : ∀ x, ‖x - x₀‖ < R → G x = 0 → fderiv ℝ a x = 0)
    (hnonconstant : ∃ y, a y ≠ a x₀) : False := by
  have hz := source_zero_near_maximum V b u G x₀ R lam C B c hR hlam hC hB
    hcpos hu hmax hsmooth hsource hell htrace hdrift
  have hdiff : DifferentiableOn ℝ a (Metric.ball x₀ (R / 4)) := by
    intro x _
    exact (ha x (mem_univ x)).differentiableAt.differentiableWithinAt
  have hd : ∀ x ∈ Metric.ball x₀ (R / 4), fderiv ℝ a x = 0 := by
    intro x hx
    have hx' : ‖x - x₀‖ < R / 4 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    exact hgradient x (by linarith) (hz x hx').2
  have hevent := locally_constant_of_derivative_zero a x₀ (R / 4) (by positivity) hdiff hd
  have heq : a = fun _ => a x₀ := ha.eq_of_eventuallyEq
    (show AnalyticOnNhd ℝ (fun _ : E => a x₀) univ from fun _ _ => analyticAt_const) hevent
  obtain ⟨y, hy⟩ := hnonconstant
  exact hy (congrFun heq y)

omit [ProperSpace E] [InnerProductSpace ℝ E] in
/-- Analytic continuation along the actual compression parameter is enough;
no analyticity on an entire coordinate space is needed. -/
theorem analytic_compression_contradiction
    (a : E → ℝ) (x₀ : E) (path : ℝ → E)
    (hlocal : a =ᶠ[𝓝 x₀] (fun _ => a x₀))
    (hpath : ContinuousAt path 1) (hbase : path 1 = x₀)
    (hanalytic : AnalyticOnNhd ℝ (a ∘ path) (Ioi 0))
    (hlimit : Tendsto (a ∘ path) atTop (𝓝 0))
    (hpositive : 0 < a x₀) : False := by
  have hp : Tendsto path (𝓝 1) (𝓝 x₀) := by simpa only [hbase] using hpath.tendsto
  have hnear : a ∘ path =ᶠ[𝓝 1] (fun _ => a x₀) := hp.eventually hlocal
  have heq : EqOn (a ∘ path) (fun _ => a x₀) (Ioi 0) :=
    hanalytic.eqOn_of_preconnected_of_eventuallyEq
      (fun _ _ => analyticAt_const) (convex_Ioi (0 : ℝ)).isPreconnected
      (by norm_num : (1 : ℝ) ∈ Ioi 0) hnear
  have hevent : (a ∘ path) =ᶠ[atTop] (fun _ => a x₀) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact heq ht
  have hconst : Tendsto (a ∘ path) atTop (𝓝 (a x₀)) :=
    tendsto_const_nhds.congr' hevent.symm
  have hz : a x₀ = 0 := tendsto_nhds_unique hconst hlimit
  exact (ne_of_gt hpositive) hz

/-- The local PDE-to-compression implication in the manuscript, with all
unformalized geometric inputs exposed in the theorem type. -/
theorem elliptic_compression_contradiction
    (V : ι → E → E) (b : E → E) (u a : E → ℝ) (G : E → F) (x₀ : E)
    (R lam C B c : ℝ) (hR : 0 < R) (hlam : 0 < lam)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hcpos : 0 < c) (hu : Continuous u)
    (hmax : ∀ x, ‖x - x₀‖ < R → u x ≤ u x₀)
    (hsmooth : ∀ x, ‖x - x₀‖ < R → ∀ v : E,
      ContDiffAt ℝ 2 (fun t : ℝ => u (x + t • v)) 0)
    (hsource : ∀ x, ‖x - x₀‖ < R → c * ‖G x‖ ^ 2 ≤ frameOp V b u x)
    (hell : ∀ x, ‖x - x₀‖ < R → ∀ v : E,
      lam * ‖v‖ ^ 2 ≤ ∑ i, (inner ℝ v (V i x)) ^ 2)
    (htrace : ∀ x, ‖x - x₀‖ < R → (∑ i, ‖V i x‖ ^ 2) ≤ C)
    (hdrift : ∀ x, ‖x - x₀‖ < R → ‖b x‖ ≤ B)
    (ha : DifferentiableOn ℝ a (Metric.ball x₀ R))
    (hgradient : ∀ x, ‖x - x₀‖ < R → G x = 0 → fderiv ℝ a x = 0)
    (path : ℝ → E) (hpath : ContinuousAt path 1) (hbase : path 1 = x₀)
    (hanalytic : AnalyticOnNhd ℝ (a ∘ path) (Ioi 0))
    (hlimit : Tendsto (a ∘ path) atTop (𝓝 0)) (hpositive : 0 < a x₀) : False := by
  have hz := source_zero_near_maximum V b u G x₀ R lam C B c hR hlam hC hB
    hcpos hu hmax hsmooth hsource hell htrace hdrift
  have hdiff : DifferentiableOn ℝ a (Metric.ball x₀ (R / 4)) :=
    ha.mono (Metric.ball_subset_ball (by linarith))
  have hd : ∀ x ∈ Metric.ball x₀ (R / 4), fderiv ℝ a x = 0 := by
    intro x hx
    have hx' : ‖x - x₀‖ < R / 4 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    exact hgradient x (by linarith) (hz x hx').2
  exact analytic_compression_contradiction a x₀ path
    (locally_constant_of_derivative_zero a x₀ (R / 4) (by positivity) hdiff hd)
    hpath hbase hanalytic hlimit hpositive


end ShadowVerification.Nonisotropy

#print axioms ShadowVerification.Nonisotropy.source_zero_near_maximum
#print axioms ShadowVerification.Nonisotropy.locally_constant_of_derivative_zero
#print axioms ShadowVerification.Nonisotropy.elliptic_analytic_contradiction

#print axioms ShadowVerification.Nonisotropy.analytic_compression_contradiction
#print axioms ShadowVerification.Nonisotropy.elliptic_compression_contradiction

import LeanShadow.WeightedLocalMaximum
import Mathlib.Topology.TietzeExtension

/-! # A local-domain interface for the weighted maximum principle

The geometric area ratio is only continuous on invertible matrices. Tietze
extension on a smaller closed ball gives a globally continuous function
agreeing with it near the base point. Derivatives and the local maximum
are preserved by that local equality. Thus the maximum-principle application
requires no regularity at singular matrices.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Filter Set
open scoped BigOperators Topology
namespace ShadowVerification.WeightedOpen
open WeightedFrame

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem continuous_extension_near (u : E → ℝ) (x₀ : E)
    (hu : ∀ᶠ x in 𝓝 x₀, ContinuousAt u x) :
    ∃ v : E → ℝ, Continuous v ∧ v =ᶠ[𝓝 x₀] u := by
  obtain ⟨R, hR, hr⟩ := Metric.eventually_nhds_iff.mp hu
  let s := Metric.closedBall x₀ (R / 2)
  have hc : ContinuousOn u s := by
    intro x hx
    have hxR : dist x x₀ < R := by
      have hh : dist x x₀ ≤ R / 2 := hx
      linarith
    exact (hr hxR).continuousWithinAt
  let f : C(s, ℝ) := ⟨fun x => u x, hc.domRestrict⟩
  obtain ⟨v, hv⟩ := f.exists_restrict_eq Metric.isClosed_closedBall
  refine ⟨v, v.continuous, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x₀ (half_pos hR)] with x hx
  have hxs : x ∈ s := Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx).le
  exact congrArg (fun g : C(s, ℝ) => g ⟨x, hxs⟩) hv

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [ProperSpace E] [Nontrivial E]

/-- The weighted source vanishes locally with only local C² regularity. -/
theorem source_zero_near_local_maximum {F : Type*} [NormedAddCommGroup F]
    (A : E → Matrix ι ι ℝ) (V : ι → E → E) (b : E → E)
    (u : E → ℝ) (G : E → F) (x₀ : E) (c : ℝ) (hc : 0 < c)
    (hA : ∀ i j, ContinuousAt (fun x => A x i j) x₀)
    (hV : ∀ i, ContinuousAt (V i) x₀) (hb : ContinuousAt b x₀)
    (hpos : (A x₀).PosDef)
    (hspan : ∀ v : E, (∀ i, inner ℝ v (V i x₀) = 0) → v = 0)
    (hmax : IsLocalMax u x₀)
    (hnear : ∀ᶠ x in 𝓝 x₀, ContDiffAt ℝ 2 u x ∧ (A x).PosSemidef ∧
      c * ‖G x‖ ^ 2 ≤ op A V b u x) :
    ∀ᶠ x in 𝓝 x₀, u x = u x₀ ∧ G x = 0 := by
  obtain ⟨v, hv, heq⟩ := continuous_extension_near u x₀
    (hnear.mono fun x hx => hx.1.continuousAt)
  have hnearV : ∀ᶠ x in 𝓝 x₀, ContDiffAt ℝ 2 v x ∧ (A x).PosSemidef ∧
      c * ‖G x‖ ^ 2 ≤ op A V b v x := by
    filter_upwards [hnear, heq.eventuallyEq_nhds] with x hx he
    refine ⟨hx.1.congr_of_eventuallyEq he, hx.2.1, ?_⟩
    have hop : op A V b v x = op A V b u x := by
      unfold op
      rw [he.fderiv_eq, he.fderiv.fderiv_eq]
    rw [hop]
    exact hx.2.2
  obtain ⟨r, hr, hrv⟩ := WeightedLocal.source_zero_near_maximum
    A V b v G x₀ c hc hA hV hb hpos hspan hv (hmax.congr heq.symm) hnearV
  filter_upwards [heq, Metric.ball_mem_nhds x₀ hr] with x hx hball
  have hh := hrv x (by simpa only [Metric.mem_ball, dist_eq_norm] using hball)
  exact ⟨by simpa only [hx, heq.self_of_nhds] using hh.1, hh.2⟩

end ShadowVerification.WeightedOpen
#print axioms ShadowVerification.WeightedOpen.continuous_extension_near
#print axioms ShadowVerification.WeightedOpen.source_zero_near_local_maximum

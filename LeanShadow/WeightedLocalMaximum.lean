import LeanShadow.WeightedEllipticity
import LeanShadow.NonisotropyMechanism

/-! # The local weighted maximum principle with derived coefficient bounds

Spanning and positive definiteness are needed only at the base point.
Continuity derives uniform ellipticity and bounded principal trace and drift
on a sufficiently small ball. The source inequality remains an explicit
input, so this theorem does not assume the geometric nonisotropy conclusion.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Filter Set
open scoped BigOperators Topology
namespace ShadowVerification.WeightedLocal
open WeightedFrame WeightedEllipticity

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] [Nontrivial E]

omit [DecidableEq ι] in
/-- Uniform coefficient bounds and ellipticity follow from continuous data
and a spanning frame at the central point. -/
theorem local_coefficient_bounds
    (A : E → Matrix ι ι ℝ) (V : ι → E → E) (b : E → E) (x₀ : E)
    (hA : ∀ i j, ContinuousAt (fun x => A x i j) x₀)
    (hV : ∀ i, ContinuousAt (V i) x₀) (hb : ContinuousAt b x₀)
    (hpos : (A x₀).PosDef)
    (hspan : ∀ v : E, (∀ i, inner ℝ v (V i x₀) = 0) → v = 0) :
    ∃ lam > 0, ∃ C ≥ 0, ∃ B ≥ 0, ∀ᶠ x in 𝓝 x₀,
      (∀ v : E, lam * ‖v‖ ^ 2 ≤ symbol A V x v) ∧
      (∑ i, ∑ j, A x i j * inner ℝ (V i x) (V j x)) ≤ C ∧ ‖b x‖ ≤ B := by
  obtain ⟨lam, hlam, hell⟩ := eventually_uniform_of_spanning A V x₀ hA hV hpos hspan
  let tr : E → ℝ := fun x => ∑ i, ∑ j, A x i j * inner ℝ (V i x) (V j x)
  have htr : ContinuousAt tr x₀ := by dsimp [tr]; fun_prop
  let C := |tr x₀| + 1
  let B := ‖b x₀‖ + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have htlt : tr x₀ < C := by dsimp [C]; linarith [le_abs_self (tr x₀)]
  have hblt : ‖b x₀‖ < B := by dsimp [B]; linarith
  refine ⟨lam, hlam, C, hC, B, hB, ?_⟩
  filter_upwards [hell, htr.eventually (eventually_lt_nhds htlt),
    hb.norm.eventually (eventually_lt_nhds hblt)] with x hx ht hb'
  exact ⟨hx, ht.le, hb'.le⟩

/-- A positive source at an interior maximum vanishes on an actual open
neighborhood. Every maximum-principle coefficient bound is derived here. -/
theorem source_zero_near_maximum {F : Type*} [NormedAddCommGroup F]
    (A : E → Matrix ι ι ℝ) (V : ι → E → E) (b : E → E)
    (u : E → ℝ) (G : E → F) (x₀ : E) (c : ℝ) (hc : 0 < c)
    (hA : ∀ i j, ContinuousAt (fun x => A x i j) x₀)
    (hV : ∀ i, ContinuousAt (V i) x₀) (hb : ContinuousAt b x₀)
    (hpos : (A x₀).PosDef)
    (hspan : ∀ v : E, (∀ i, inner ℝ v (V i x₀) = 0) → v = 0)
    (hu : Continuous u) (hmax : IsLocalMax u x₀)
    (hnear : ∀ᶠ x in 𝓝 x₀, ContDiffAt ℝ 2 u x ∧ (A x).PosSemidef ∧
      c * ‖G x‖ ^ 2 ≤ op A V b u x) :
    ∃ r > 0, ∀ x, ‖x - x₀‖ < r → u x = u x₀ ∧ G x = 0 := by
  obtain ⟨lam, hlam, C, hC, B, hB, hbounds⟩ :=
    local_coefficient_bounds A V b x₀ hA hV hb hpos hspan
  have hall := hnear.and (hmax.and hbounds)
  obtain ⟨R, hR, hr⟩ := Metric.eventually_nhds_iff.mp hall
  have hdata (x : E) (hx : ‖x - x₀‖ < R) := hr (by simpa only [dist_eq_norm] using hx)
  have hconst := Nonisotropy.source_zero_near_maximum
    (fun k x => directions (A x) (fun i => V i x) k) b u G x₀
    R lam C B c hR hlam hC hB hc hu
    (fun x hx => (hdata x hx).2.1) ?_ ?_ ?_ ?_ ?_
  · exact ⟨R / 4, by positivity, hconst⟩
  · intro x hx v
    have hl : ContDiff ℝ 2 (fun t : ℝ => x + t • v) :=
      contDiff_const.add (contDiff_id.smul contDiff_const)
    have hc2 : ContDiffAt ℝ 2 u (x + (0 : ℝ) • v) := by
      simpa using (hdata x hx).1.1
    exact hc2.comp 0 hl.contDiffAt
  · intro x hx
    rw [← op_eq_frameOp A V b u x (hdata x hx).1.2.1 (hdata x hx).1.1]
    exact (hdata x hx).1.2.2
  · intro x hx v
    rw [directions_symbol (A x) (hdata x hx).1.2.1]
    exact (hdata x hx).2.2.1 v
  · intro x hx
    rw [directions_trace (A x) (hdata x hx).1.2.1]
    exact (hdata x hx).2.2.2.1
  · intro x hx
    exact (hdata x hx).2.2.2.2

end ShadowVerification.WeightedLocal
#print axioms ShadowVerification.WeightedLocal.local_coefficient_bounds
#print axioms ShadowVerification.WeightedLocal.source_zero_near_maximum

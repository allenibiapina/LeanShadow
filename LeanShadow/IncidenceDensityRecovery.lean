import LeanShadow.HaarDensityRepresentatives
import LeanShadow.IncidenceKernelCompactness

/-! # Unconditional pointwise recovery for the actual Haar incidence law

Two sets whose intersection has measure zero cannot both occupy asymptotically
all of the same averaging balls. For an orthogonal spherical pair, frame
transitivity supplies the same group center for its two lifted sets. The
descended Haar-density representatives therefore avoid pointwise.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.IncidenceRecovery
open Spherical OrthogonalHaar HaarDensity

/-- A null intersection bounds the sum of the two local occupancy ratios by one. -/
theorem ratio_sum_le_one {X : Type*} [MeasurableSpace X] (nu : Measure X)
    (A B U : Set X) (hB : MeasurableSet B) (hU : MeasurableSet U)
    (hz : nu (A ∩ B) = 0) :
    nu (A ∩ U) / nu U + nu (B ∩ U) / nu U ≤ 1 := by
  have hi : nu ((A ∩ U) ∩ (B ∩ U)) = 0 :=
    measure_mono_null (by intro x hx; exact ⟨hx.1.1, hx.2.1⟩) hz
  have hs : nu (A ∩ U) + nu (B ∩ U) ≤ nu U := by
    rw [← measure_union_add_inter (A ∩ U) (hB.inter hU), hi, add_zero]
    apply measure_mono
    intro x hx
    rcases hx with hx | hx
    · exact hx.2
    · exact hx.2
  rw [← ENNReal.add_div]
  exact (ENNReal.div_le_div_right hs _).trans ENNReal.div_self_le_one

theorem incompatible_density_limits {X : Type*} [MeasurableSpace X] (nu : Measure X)
    (A B : Set X) (hB : MeasurableSet B) (U : ℕ → Set X)
    (hU : ∀ j, MeasurableSet (U j)) (hz : nu (A ∩ B) = 0)
    (ha : Tendsto (fun j => nu (A ∩ U j) / nu (U j)) atTop (𝓝 1))
    (hb : Tendsto (fun j => nu (B ∩ U j) / nu (U j)) atTop (𝓝 1)) : False := by
  have h : (1 : ℝ≥0∞) + 1 ≤ 1 := le_of_tendsto (ha.add hb)
    (Eventually.of_forall fun j => ratio_sum_le_one nu A B (U j) hB (hU j) hz)
  norm_num at h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-- Zero incidence gives pointwise avoidance of the actual descended density representatives. -/
theorem representatives_avoid (a b : Sphere E)
    (hab : inner ℝ (a : E) (b : E) = 0)
    (D C : Set (Sphere E)) (hD : MeasurableSet D) (hC : MeasurableSet C)
    (hz : OrthogonalIncidence.measure a b (D ×ˢ C) = 0) :
    Avoids (representative D) (representative C) := by
  rw [OrthogonalIncidence.measure, Measure.map_apply
    (OrthogonalIncidence.frame_continuous a b).measurable (hD.prod hC)] at hz
  change haar E (lift D a ∩ lift C b) = 0 at hz
  intro x hx y hy hxy
  obtain ⟨R, hRx, hRy⟩ := OrthogonalFrame.exists_pair a b x y hab hxy
  have hd : Tendsto (fun j => haar E (lift D a ∩ closedBall R (SingularKernel.scale j)) /
      haar E (closedBall R (SingularKernel.scale j))) atTop (𝓝 1) := by
    simp_rw [← average_rotate D hD a R, hRx]
    exact hx
  have hc : Tendsto (fun j => haar E (lift C b ∩ closedBall R (SingularKernel.scale j)) /
      haar E (closedBall R (SingularKernel.scale j))) atTop (𝓝 1) := by
    simp_rw [← average_rotate C hC b R, hRy]
    exact hy
  exact incompatible_density_limits (haar E) (lift D a) (lift C b)
    (lift_measurable C hC b) (fun j => closedBall R (SingularKernel.scale j))
    (fun _ => isClosed_closedBall.measurableSet) hz hd hc

variable (mu : Measure E) [mu.IsAddHaarMeasure]

/-- Every field of the recovery hypothesis for the concrete incidence law is now proved. -/
theorem pointwiseRecovery (hd : 1 < Module.finrank ℝ E) :
    Attainment.PointwiseRecovery mu (OrthogonalIncidence.realization mu hd).measure := by
  intro D C hD hC hz
  let a := OrthogonalIncidence.firstPoint (E := E) hd
  let b := OrthogonalIncidence.secondPoint (E := E) hd
  refine ⟨representative D, representative C, representative_measurable D hD,
    representative_measurable C hC, representative_area mu D hD a,
    representative_area mu C hC b, ?_⟩
  exact representatives_avoid a b (OrthogonalIncidence.exists_orthogonal_pair hd).choose_spec.choose_spec
    D C hD hC hz

/-- Attainment now needs only compactness of the constructed incidence operator. -/
theorem exists_optimizer_of_compact (hd : 1 < Module.finrank ℝ E)
    (hc : IsCompactOperator (SphericalIncidenceOperator.operator mu hd))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ A B : Set (Sphere E), Profile.IsOptimalPair mu p A B ∧ Profile.IsOptimizer mu p A :=
  SphericalIncidenceOperator.exists_optimizer_of_compact mu hd hc (pointwiseRecovery mu hd) p hp0 hp1

end ShadowVerification.IncidenceRecovery
#print axioms ShadowVerification.IncidenceRecovery.ratio_sum_le_one
#print axioms ShadowVerification.IncidenceRecovery.incompatible_density_limits
#print axioms ShadowVerification.IncidenceRecovery.representatives_avoid
#print axioms ShadowVerification.IncidenceRecovery.pointwiseRecovery
#print axioms ShadowVerification.IncidenceRecovery.exists_optimizer_of_compact

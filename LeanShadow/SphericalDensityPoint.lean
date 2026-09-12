import LeanShadow.SphericalProjective
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-! # Density-zero axes for arbitrary measurable spherical sets

The spherical probability measure is embedded into the ambient finite-dimensional
space. Besicovitch differentiation applies to this singular Borel measure as
well as to volume. Pulling the conclusion back to the sphere gives genuine
density-zero points whenever the complement has positive measure.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.SphericalDensity
open Spherical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Differentiation applies intrinsically to spherical balls, even though
the ambient pushforward measure is concentrated on a hypersurface. -/
theorem ae_density_ratio (nu : Measure (Sphere E)) [IsFiniteMeasure nu]
    (A : Set (Sphere E)) (hA : MeasurableSet A) :
    ∀ᵐ e ∂nu, e ∉ A →
      Tendsto (fun r => nu (A ∩ closedBall e r) / nu (closedBall e r)) (𝓝[>] 0) (𝓝 0) := by
  let j : Sphere E → E := Subtype.val
  have hj : MeasurableEmbedding j := MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet
  have himage : MeasurableSet (j '' A) := hj.measurableSet_image.mpr hA
  have hd := Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet (nu.map j) himage
  have hp := ae_of_ae_map hj.measurable.aemeasurable hd
  filter_upwards [hp] with e he hnot
  have hnot' : j e ∉ j '' A := by simpa only [Set.mem_image, hj.injective.eq_iff, exists_eq_right] using hnot
  simp only [Set.indicator_of_notMem hnot'] at he
  have hb (r : ℝ) : j ⁻¹' closedBall (j e) r = closedBall e r := rfl
  have hi (r : ℝ) : j ⁻¹' (j '' A ∩ closedBall (j e) r) = A ∩ closedBall e r := by
    rw [preimage_inter, preimage_image_eq A hj.injective, hb]
  have heq (r : ℝ) :
      (nu.map j) (j '' A ∩ closedBall (j e) r) / (nu.map j) (closedBall (j e) r) =
        nu (A ∩ closedBall e r) / nu (closedBall e r) := by
    rw [Measure.map_apply hj.measurable (himage.inter isClosed_closedBall.measurableSet),
      Measure.map_apply hj.measurable isClosed_closedBall.measurableSet, hi, hb]
  simpa only [heq] using he

/-- Positive complement measure supplies an actual unit axis with zero density. -/
theorem exists_density_zero (nu : Measure (Sphere E)) [IsFiniteMeasure nu]
    (A : Set (Sphere E)) (hA : MeasurableSet A) (hcompl : nu Aᶜ ≠ 0) :
    ∃ e : Sphere E, e ∉ A ∧
      Tendsto (fun r => nu (A ∩ closedBall e r) / nu (closedBall e r)) (𝓝[>] 0) (𝓝 0) := by
  have hd := ae_density_ratio nu A hA
  have he : ∃ e ∈ Aᶜ, e ∉ A →
      Tendsto (fun r => nu (A ∩ closedBall e r) / nu (closedBall e r)) (𝓝[>] 0) (𝓝 0) :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hcompl (hd.filter_mono ae_restrict_le)
  obtain ⟨e, he, hd⟩ := he
  exact ⟨e, he, hd he⟩

variable [Nontrivial E] (mu : Measure E) [mu.IsAddHaarMeasure]

/-- Every measurable spherical set of normalized area less than one has a
density-zero axis; no open hole or boundary regularity is assumed. -/
theorem exists_axis_of_area_lt_one (A : Set (Sphere E)) (hA : MeasurableSet A)
    (hp : area mu A < 1) :
    ∃ e : Sphere E, e ∉ A ∧
      Tendsto (fun r => probability mu (A ∩ closedBall e r) / probability mu (closedBall e r))
        (𝓝[>] 0) (𝓝 0) := by
  apply exists_density_zero (probability mu) A hA
  intro hz
  have h := measure_add_measure_compl hA (μ := probability mu)
  rw [hz, add_zero, probability_univ] at h
  have ha : area mu A = 1 := by simp [area, measureReal_def, h]
  linarith

end ShadowVerification.SphericalDensity
#print axioms ShadowVerification.SphericalDensity.ae_density_ratio
#print axioms ShadowVerification.SphericalDensity.exists_density_zero
#print axioms ShadowVerification.SphericalDensity.exists_axis_of_area_lt_one

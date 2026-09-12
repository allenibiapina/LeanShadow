import LeanShadow.AxisCoordinates

/-! # The measure class of spherical latitudes

In dimension at least two, the signed coordinate of a uniform spherical
point has exactly the null sets of Lebesgue measure on (-1,1). This is
proved by polar integration, linear Haar disintegration and a smooth
one-dimensional change of variables, without assuming the latitude density.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.LatitudeClass
open Spherical AxisCoordinates

theorem product_event_null_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (nu : Measure F) [nu.IsAddHaarMeasure] (N : Set ℝ) (hN : MeasurableSet N) :
    (volume.prod nu) {z : ℝ × F | z.1 / Real.sqrt (z.1 ^ 2 + ‖z.2‖ ^ 2) ∈ N} = 0 ↔
      volume (N ∩ Ioo (-1) 1) = 0 := by
  let S : Set (ℝ × F) := {z | z.1 / Real.sqrt (z.1 ^ 2 + ‖z.2‖ ^ 2) ∈ N}
  have hS : MeasurableSet S := hN.preimage (by fun_prop)
  have he : (volume.prod nu) S = 0 ↔
      ∀ᵐ v ∂nu, volume ((fun t : ℝ => t / Real.sqrt (t ^ 2 + ‖v‖ ^ 2)) ⁻¹' N) = 0 := by
    rw [Measure.prod_apply_symm hS, lintegral_eq_zero_iff (measurable_measure_prodMk_right hS)]
    rfl
  have hn : ∀ᵐ v ∂nu, v ≠ (0 : F) := by simp [ae_iff]
  change (volume.prod nu) S = 0 ↔ _
  rw [he]
  constructor
  · intro h
    obtain ⟨v, hv, hv0⟩ := (h.and hn).exists
    exact (LatitudeCoordinate.normalized_null_iff ‖v‖ (norm_pos_iff.mpr hv0) N).mp hv
  · intro h
    filter_upwards [hn] with v hv
    exact (LatitudeCoordinate.normalized_null_iff ‖v‖ (norm_pos_iff.mpr hv) N).mpr h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

/-- Exact null-set equivalence for the coordinate of the pre-existing spherical probability. -/
theorem coordinate_null_iff (hd : 1 < Module.finrank ℝ E) (a : Sphere E)
    (N : Set ℝ) (hN : MeasurableSet N) :
    probability mu {x : Sphere E | inner ℝ (a : E) (x : E) ∈ N} = 0 ↔
      volume (N ∩ Ioo (-1) 1) = 0 := by
  let : Nontrivial (perpendicular a) := perpendicular_nontrivial a hd
  rw [DirectionNull.latitude_null_iff mu a N hN,
    ambient_null_iff mu a _ (hN.preimage (DirectionNull.ratio_measurable a))]
  have he : equivalence a ⁻¹' (DirectionNull.ratio a ⁻¹' N) =
      {z : ℝ × perpendicular a | z.1 / Real.sqrt (z.1 ^ 2 + ‖z.2‖ ^ 2) ∈ N} := by
    ext ⟨t,v⟩
    simp only [mem_preimage, mem_ofPred_eq, ratio_equivalence]
  rw [he]
  exact product_event_null_iff (Measure.addHaar : Measure (perpendicular a)) N hN

end ShadowVerification.LatitudeClass
#print axioms ShadowVerification.LatitudeClass.product_event_null_iff
#print axioms ShadowVerification.LatitudeClass.coordinate_null_iff

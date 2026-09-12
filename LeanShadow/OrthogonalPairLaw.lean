import LeanShadow.HaarConditionalAverage

/-! # Haar pair laws and identification of continuous averages with the actual operator -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.PairLaw
open Spherical OrthogonalHaar OrthogonalIncidence ConditionalAverage

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

theorem measure_eq_of_inner_eq (a b x y : Sphere E)
    (h : inner ℝ (a : E) (b : E) = inner ℝ (x : E) (y : E)) :
    OrthogonalIncidence.measure a b = OrthogonalIncidence.measure x y := by
  obtain ⟨S, ha, hb⟩ := OrthogonalFrame.exists_pair_of_inner_eq a b x y h
  have hm : Measurable (fun R : OrthogonalHaar.Group E => R * S) :=
    (continuous_mul_const S).measurable
  calc
    _ = ((haar E).map (· * S)).map (frame a b) := by rw [haar_map_right]; rfl
    _ = _ := by
      rw [Measure.map_map (frame_continuous a b).measurable hm]
      congr 1
      funext R
      simp only [Function.comp_apply, frame, rotate_mul, ha, hb]

variable (mu : Measure E) [mu.IsAddHaarMeasure]

theorem continuous_inner (u v : C(Sphere E, ℝ)) :
    inner ℝ (ContinuousMap.toLp 2 (probability mu) ℝ u)
      (ContinuousMap.toLp 2 (probability mu) ℝ v) =
      ∫ x, u x * v x ∂probability mu := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) (probability mu) u,
    ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) (probability mu) v] with x hx hy
  simp only [hx, hy, RCLike.inner_apply, conj_trivial, mul_comm]

/-- The actual L² incidence operator has the continuous Haar pairing in any orthonormal frame. -/
theorem continuous_pairing (hd : 1 < Module.finrank ℝ E)
    (a b : Sphere E) (hab : inner ℝ (a : E) (b : E) = 0)
    (u v : C(Sphere E, ℝ)) :
    inner ℝ (ContinuousMap.toLp 2 (probability mu) ℝ u)
      (SphericalIncidenceOperator.operator mu hd (ContinuousMap.toLp 2 (probability mu) ℝ v)) =
      ∫ R : OrthogonalHaar.Group E, u (rotate R a) * v (rotate R b) ∂haar E := by
  rw [SphericalIncidenceOperator.pairing]
  have he : (realization mu hd).measure = OrthogonalIncidence.measure a b :=
    measure_eq_of_inner_eq (firstPoint hd) (secondPoint hd) a b
      ((exists_orthogonal_pair hd).choose_spec.choose_spec.trans hab.symm)
  rw [he]
  have hi : (∫ z : Sphere E × Sphere E,
      (ContinuousMap.toLp 2 (probability mu) ℝ u) z.1 *
      (ContinuousMap.toLp 2 (probability mu) ℝ v) z.2 ∂OrthogonalIncidence.measure a b) =
      ∫ z : Sphere E × Sphere E, u z.1 * v z.2 ∂OrthogonalIncidence.measure a b := by
    apply integral_congr_ae
    filter_upwards [(firstMarginal mu a b).quasiMeasurePreserving.ae
      (ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) (probability mu) u),
      (secondMarginal mu a b).quasiMeasurePreserving.ae
      (ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) (probability mu) v)] with z hz hw
    rw [hz, hw]
  rw [hi]
  exact integral_map_of_stronglyMeasurable (frame_continuous a b).measurable
    (show StronglyMeasurable (fun z : Sphere E × Sphere E => u z.1 * v z.2) by
      exact (show Continuous _ by fun_prop).stronglyMeasurable)

/-- Stabilizer integration is an actual continuous representative of the L² operator. -/
theorem continuous_image (hd : 1 < Module.finrank ℝ E)
    (a b : Sphere E) (hab : inner ℝ (a : E) (b : E) = 0)
    (v : C(Sphere E, ℝ)) :
    SphericalIncidenceOperator.operator mu hd (ContinuousMap.toLp 2 (probability mu) ℝ v) =
      ContinuousMap.toLp 2 (probability mu) ℝ (spherical a b v) := by
  apply ext_inner_left ℝ
  have hdense := ContinuousMap.toLp_denseRange ℝ (probability mu) ℝ
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  have he := hdense.equalizer
    (show Continuous (fun u : Lp ℝ 2 (probability mu) =>
      inner ℝ u (SphericalIncidenceOperator.operator mu hd (ContinuousMap.toLp 2 (probability mu) ℝ v))) by fun_prop)
    (show Continuous (fun u : Lp ℝ 2 (probability mu) =>
      inner ℝ u (ContinuousMap.toLp 2 (probability mu) ℝ (spherical a b v))) by fun_prop)
    (show _ = _ from funext fun u => by
      change inner ℝ (ContinuousMap.toLp 2 (probability mu) ℝ u)
        (SphericalIncidenceOperator.operator mu hd (ContinuousMap.toLp 2 (probability mu) ℝ v)) =
        inner ℝ (ContinuousMap.toLp 2 (probability mu) ℝ u)
          (ContinuousMap.toLp 2 (probability mu) ℝ (spherical a b v))
      rw [continuous_pairing mu hd a b hab, continuous_inner, spherical_pairing])
  exact fun u => congrFun he u

end ShadowVerification.PairLaw
#print axioms ShadowVerification.PairLaw.measure_eq_of_inner_eq
#print axioms ShadowVerification.PairLaw.continuous_inner
#print axioms ShadowVerification.PairLaw.continuous_pairing
#print axioms ShadowVerification.PairLaw.continuous_image

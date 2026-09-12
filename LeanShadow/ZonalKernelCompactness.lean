import LeanShadow.SphericalPairDensity
import LeanShadow.SignedKernelBound
import LeanShadow.SphericalKernelTruncation

/-! # Every integrable zonal kernel defines a compact L² operator

Approximate the scalar density in L¹ of the actual Gram distribution.
Rotation invariance turns that L¹ error into an identical bound for every
row and column, so the signed Schur estimate gives operator-norm convergence.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal BoundedContinuousFunction
namespace ShadowVerification.ZonalCompactness
open Spherical OrthogonalHaar InvariantPair
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

def law : Measure ℝ := ((probability mu).prod (probability mu)).map gram

instance : IsProbabilityMeasure (law mu) :=
  Measure.isProbabilityMeasure_map gram_continuous.measurable.aemeasurable

omit [Nontrivial E] [mu.IsAddHaarMeasure] in
theorem global_integrable (h : ℝ → ℝ) (hi : Integrable h (law mu)) :
    Integrable (fun z : Sphere E × Sphere E => h (gram z))
      ((probability mu).prod (probability mu)) :=
  (integrable_map_measure hi.aestronglyMeasurable gram_continuous.measurable.aemeasurable).mp hi

theorem row_integrable (h : ℝ → ℝ) (hi : Integrable h (law mu)) (x : Sphere E) :
    Integrable (fun y : Sphere E => h (gram (x,y))) (probability mu) := by
  obtain ⟨z, hz⟩ := (global_integrable mu h hi).prod_right_ae.exists
  apply SphericalKernel.row_integrable mu (fun w => h (gram w)) _ z hz x
  intro R a b
  simp only [gram, rotate_inner]

theorem row_integral (h : ℝ → ℝ) (hm : Measurable h) (hi : Integrable h (law mu))
    (x : Sphere E) :
    (∫ y : Sphere E, h (gram (x,y)) ∂probability mu) = ∫ t, h t ∂law mu := by
  have he (z : Sphere E) :
      (∫ y : Sphere E, h (gram (z,y)) ∂probability mu) =
        ∫ y : Sphere E, h (gram (x,y)) ∂probability mu := by
    apply SphericalKernel.row_integral_eq mu (fun w => h (gram w)) (hm.comp gram_continuous.measurable) _ z x
    intro R a b
    simp only [gram, rotate_inner]
  change _ = ∫ t, h t ∂((probability mu).prod (probability mu)).map gram
  rw [integral_map gram_continuous.measurable.aemeasurable hm.aestronglyMeasurable,
    integral_prod _ (global_integrable mu h hi)]
  simp_rw [he]
  simp

theorem product_integrable (h : ℝ → ℝ) (hm : Measurable h) (h0 : ∀ t, 0 ≤ h t)
    (hi : Integrable h (law mu)) (u v : Lp ℝ 2 (probability mu)) :
    Integrable (fun z : Sphere E × Sphere E => h (gram z) * (u z.1 * v z.2))
      ((probability mu).prod (probability mu)) := by
  refine KernelMeasure.product_integrable (probability mu) (fun z => h (gram z)) (hm.comp gram_continuous.measurable)
    (fun z => h0 (gram z)) (∫ t, h t ∂law mu) (integral_nonneg h0)
    (row_integrable mu h hi) ?_ ?_ ?_ u v
  · intro y
    simpa only [gram, real_inner_comm (y : E)] using row_integrable mu h hi y
  · exact row_integral mu h hm hi
  · intro y
    simpa only [gram, real_inner_comm (y : E)] using row_integral mu h hm hi y

def continuousKernel (g : ℝ →ᵇ ℝ) : C(Sphere E × Sphere E, ℝ) :=
  ⟨fun z => g (gram z), g.continuous.comp gram_continuous⟩

theorem norm_error (h : ℝ → ℝ) (hm : Measurable h) (h0 : ∀ t, 0 ≤ h t)
    (hi : Integrable h (law mu))
    (T : Lp ℝ 2 (probability mu) →L[ℝ] Lp ℝ 2 (probability mu))
    (hp : ∀ u v, inner ℝ u (T v) = ∫ z : Sphere E × Sphere E,
      h (gram z) * (u z.1 * v z.2) ∂(probability mu).prod (probability mu))
    (g : ℝ →ᵇ ℝ) (hg : Integrable g (law mu)) :
    ‖T - ContinuousKernel.operator (probability mu) (probability mu) (continuousKernel g)‖ ≤
      ∫ t, ‖h t - g t‖ ∂law mu := by
  let r : ℝ → ℝ := fun t => h t - g t
  have hrm : Measurable r := hm.sub g.continuous.measurable
  have hri : Integrable r (law mu) := hi.sub hg
  apply SignedKernel.norm_le (probability mu) (fun z => r (gram z))
    (hrm.comp gram_continuous.measurable) _ (integral_nonneg fun _ => norm_nonneg _)
    (row_integrable mu (fun t => ‖r t‖) hri.norm)
  · intro y
    simpa only [gram, real_inner_comm (y : E)] using row_integrable mu (fun t => ‖r t‖) hri.norm y
  · exact row_integral mu (fun t => ‖r t‖) hrm.norm hri.norm
  · intro y
    simpa only [gram, real_inner_comm (y : E)] using row_integral mu (fun t => ‖r t‖) hrm.norm hri.norm y
  · intro u v
    change inner ℝ u (T v - ContinuousKernel.operator _ _ _ v) = _
    rw [inner_sub_right, hp, ContinuousKernel.pairing]
    rw [← integral_sub (product_integrable mu h hm h0 hi u v)
      (ContinuousKernel.product_integrable (probability mu) (probability mu) (continuousKernel g) u v)]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      change h (gram z) * (u z.1 * v z.2) - g (gram z) * (u z.1 * v z.2) =
        (h (gram z) - g (gram z)) * (u z.1 * v z.2)
      ring

/-- No explicit latitude formula is needed: integrability of the scalar density suffices. -/
theorem compact (h : ℝ → ℝ) (hm : Measurable h) (h0 : ∀ t, 0 ≤ h t)
    (hi : Integrable h (law mu))
    (T : Lp ℝ 2 (probability mu) →L[ℝ] Lp ℝ 2 (probability mu))
    (hp : ∀ u v, inner ℝ u (T v) = ∫ z : Sphere E × Sphere E,
      h (gram z) * (u z.1 * v z.2) ∂(probability mu).prod (probability mu)) :
    IsCompactOperator T := by
  have he (j : ℕ) : ∃ g : ℝ →ᵇ ℝ,
      (∫ t, ‖h t - g t‖ ∂law mu) ≤ 1 / ((j : ℝ) + 1) ∧ Integrable g (law mu) :=
    hi.exists_boundedContinuous_integral_sub_le (by positivity)
  choose g hg hgi using he
  let K (j : ℕ) := ContinuousKernel.operator (probability mu) (probability mu) (continuousKernel (g j))
  have he (j : ℕ) : ‖T - K j‖ ≤ 1 / ((j : ℝ) + 1) :=
    (norm_error mu h hm h0 hi T hp (g j) (hgi j)).trans (hg j)
  have ht : Tendsto K atTop (𝓝 T) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have h := squeeze_zero (fun j => norm_nonneg (T - K j)) he
      tendsto_one_div_add_atTop_nhds_zero_nat
    convert h using 1
    funext j
    exact norm_sub_rev _ _
  exact isCompactOperator_of_tendsto ht
    (Eventually.of_forall fun j => ContinuousKernel.compact _ _ _)

end ShadowVerification.ZonalCompactness
#print axioms ShadowVerification.ZonalCompactness.global_integrable
#print axioms ShadowVerification.ZonalCompactness.row_integrable
#print axioms ShadowVerification.ZonalCompactness.row_integral
#print axioms ShadowVerification.ZonalCompactness.product_integrable
#print axioms ShadowVerification.ZonalCompactness.norm_error
#print axioms ShadowVerification.ZonalCompactness.compact

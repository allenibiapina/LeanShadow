import LeanShadow.SphericalSingularKernel

/-! # The analytic compactness argument for the spherical singular kernel

Continuous compact approximations converge in operator norm. The final
corollaries concern the actual Haar incidence operator. Their remaining
geometric hypotheses are one-row integrability and the square-kernel
pairing identity; neither is hidden in a definition or assumed as an axiom.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.IncidenceCompactness
open Spherical SphericalKernel SingularKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]
  (beta : ℝ) (hb : 0 ≤ beta) (x : Sphere E)
  (hi : Integrable (fun y => kernel beta (x,y)) (probability mu))
  (T : Lp ℝ 2 (probability mu) →L[ℝ] Lp ℝ 2 (probability mu))
  (hp : ∀ u v, inner ℝ u (T v) = ∫ z : Sphere E × Sphere E,
    kernel beta z * (u z.1 * v z.2) ∂(probability mu).prod (probability mu))

include hb hi hp

/-- The norm error is bounded by the common row mass of the positive residual kernel. -/
theorem norm_error_le (j : ℕ) :
    ‖T - SphericalKernel.operator mu beta (scale j) (scale_pos j)‖ ≤
      ∫ y, kernel beta (x,y) - cutoff beta (scale j) (x,y) ∂probability mu := by
  let r : Sphere E × Sphere E → ℝ := fun z => kernel beta z - cutoff beta (scale j) z
  have hm : Measurable r := (SingularKernel.measurable beta).sub
    (cutoff_continuous beta (scale j) (scale_pos j)).measurable
  have h0 (z : Sphere E × Sphere E) : 0 ≤ r z :=
    sub_nonneg.mpr (cutoff_le beta (scale j) hb (scale_pos j) z)
  have hir (z : Sphere E) : Integrable (fun y => r (z,y)) (probability mu) :=
    (rows_integrable mu beta x hi z).sub (cutoff_row_integrable mu beta (scale j) (scale_pos j) z)
  have hs (z y : Sphere E) : r (z,y) = r (y,z) := by
    dsimp [r]
    rw [SingularKernel.symmetric beta z y, cutoff_symm beta (scale j) z y]
  have hv (R : OrthogonalHaar.Group E) (z y : Sphere E) :
      r (OrthogonalHaar.rotate R z,OrthogonalHaar.rotate R y) = r (z,y) := by
    dsimp [r]
    rw [invariant, cutoff_invariant]
  apply KernelMeasure.norm_le (probability mu) r hm h0 _ (integral_nonneg fun y => h0 (x,y)) hir
  · intro y
    simp_rw [hs _ y]
    exact hir y
  · intro z
    exact row_integral_eq mu r hm hv z x
  · intro z
    simp_rw [hs _ z]
    exact row_integral_eq mu r hm hv z x
  · intro u v
    change inner ℝ u (T v - SphericalKernel.operator mu beta (scale j) (scale_pos j) v) = _
    rw [inner_sub_right, hp, SphericalKernel.pairing]
    have hki : Integrable (fun z : Sphere E × Sphere E =>
        cutoff beta (scale j) z * (u z.1 * v z.2)) ((probability mu).prod (probability mu)) :=
      ContinuousKernel.product_integrable (probability mu) (probability mu)
        (continuousCutoff beta (scale j) (scale_pos j)) u v
    rw [← integral_sub (SingularKernel.product_integrable mu beta hb x hi u v) hki]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by dsimp [r]; ring

/-- The actual continuous-kernel approximations converge in operator norm. -/
theorem operator_tendsto :
    Tendsto (fun j => SphericalKernel.operator mu beta (scale j) (scale_pos j)) atTop (𝓝 T) := by
  have h := squeeze_zero (fun j => norm_nonneg (T - SphericalKernel.operator mu beta (scale j) (scale_pos j)))
    (norm_error_le mu beta hb x hi T hp) (row_error_tendsto mu beta hb x hi)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  convert h using 1
  funext j
  exact norm_sub_rev _ _

/-- A bounded operator represented by this integrable singular kernel is compact. -/
theorem compact : IsCompactOperator T :=
  isCompactOperator_of_tendsto (operator_tendsto mu beta hb x hi T hp)
    (Eventually.of_forall fun j => SphericalKernel.compact mu beta (scale j) (scale_pos j))

omit T hp in
/-- Application to the concrete Haar incidence operator, with the geometric kernel identity exposed. -/
theorem incidence_compact (hd : 1 < Module.finrank ℝ E)
    (hk : ∀ u v, inner ℝ u (SphericalIncidenceOperator.operator mu hd
      (SphericalIncidenceOperator.operator mu hd v)) = ∫ z : Sphere E × Sphere E,
      kernel beta z * (u z.1 * v z.2) ∂(probability mu).prod (probability mu)) :
    IsCompactOperator (SphericalIncidenceOperator.operator mu hd) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  apply CompactSquare.compact_of_comp_self (SphericalIncidenceOperator.operator mu hd)
    (SphericalIncidenceOperator.symmetric mu hd)
  exact compact mu beta hb x hi _ hk

omit T hp in
/-- Once kernel geometry and density-point recovery are supplied, attainment follows for the actual profile. -/
theorem exists_optimizer (hd : 1 < Module.finrank ℝ E)
    (hk : ∀ u v, inner ℝ u (SphericalIncidenceOperator.operator mu hd
      (SphericalIncidenceOperator.operator mu hd v)) = ∫ z : Sphere E × Sphere E,
      kernel beta z * (u z.1 * v z.2) ∂(probability mu).prod (probability mu))
    (hr : Attainment.PointwiseRecovery mu (OrthogonalIncidence.realization mu hd).measure)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ A B : Set (Sphere E), Profile.IsOptimalPair mu p A B ∧ Profile.IsOptimizer mu p A :=
  SphericalIncidenceOperator.exists_optimizer_of_compact mu hd
    (incidence_compact mu beta hb x hi hd hk) hr p hp0 hp1

end ShadowVerification.IncidenceCompactness
#print axioms ShadowVerification.IncidenceCompactness.norm_error_le
#print axioms ShadowVerification.IncidenceCompactness.operator_tendsto
#print axioms ShadowVerification.IncidenceCompactness.compact
#print axioms ShadowVerification.IncidenceCompactness.incidence_compact
#print axioms ShadowVerification.IncidenceCompactness.exists_optimizer

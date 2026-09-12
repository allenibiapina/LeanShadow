import LeanShadow.ProjectiveArea
import LeanShadow.CompactParametricIntegral

/-! # Differentiating the projective density over measurable spherical sets

Joint continuity on the compact sphere supplies the domination estimates.
The first and second derivative formulas below concern the actual integral,
not a formal interchange of differentiation and integration.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace ShadowVerification.Projective
open Spherical Parametric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem flow_joint_continuous (H : E →L[ℝ] E) :
    Continuous (fun p : ℝ × E => flow H p.2 p.1) := by
  have hc : Continuous (fun t : ℝ => NormedSpace.exp (t • H)) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_exp_smul_const H t).continuousAt)
  exact (hc.comp continuous_fst).clm_apply continuous_snd

theorem flowNormSq_ne_zero (H : E →L[ℝ] E) (x : E) (hx : x ≠ 0) (t : ℝ) :
    flowNormSq H x t ≠ 0 := by
  have hne : flow H x t ≠ 0 := by
    rw [← flowEquiv_apply]
    simpa only [map_zero] using (flowEquiv H t).injective.ne hx
  rw [flowNormSq, real_inner_self_eq_norm_sq]
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr hne)

noncomputable def flowNormSqDD (H : E →L[ℝ] E) (x : E) (t : ℝ) : ℝ :=
  2 * (inner ℝ (flow H x t) (flow H (H (H x)) t) +
    inner ℝ (flow H (H x) t) (flow H (H x) t))

theorem flowNormSqD_hasDeriv (H : E →L[ℝ] E) (x : E) (t : ℝ) :
    HasDerivAt (flowNormSqD H x) (flowNormSqDD H x t) t := by
  exact ((flow_hasDeriv H x t).inner ℝ (flow_hasDeriv H (H x) t)).const_mul 2

noncomputable def densityD (N : ℝ) (H : E →L[ℝ] E) (x : E) (t : ℝ) : ℝ :=
  flowNormSqD H x t * (-N / 2) * flowNormSq H x t ^ (-N / 2 - 1)

noncomputable def densityDD (N : ℝ) (H : E →L[ℝ] E) (x : E) (t : ℝ) : ℝ :=
  flowNormSqDD H x t * (-N / 2) * flowNormSq H x t ^ (-N / 2 - 1) +
    flowNormSqD H x t * (-N / 2) *
      (flowNormSqD H x t * (-N / 2 - 1) * flowNormSq H x t ^ (-N / 2 - 1 - 1))

theorem density_hasDeriv (N : ℝ) (H : E →L[ℝ] E) (x : E) (hx : x ≠ 0) (t : ℝ) :
    HasDerivAt (flowDensity N H x) (densityD N H x t) t := by
  exact (flowNormSq_hasDeriv H x t).rpow_const (Or.inl (flowNormSq_ne_zero H x hx t))

theorem densityD_hasDeriv (N : ℝ) (H : E →L[ℝ] E) (x : E) (hx : x ≠ 0) (t : ℝ) :
    HasDerivAt (densityD N H x) (densityDD N H x t) t := by
  exact ((flowNormSqD_hasDeriv H x t).mul_const (-N / 2)).mul
    ((flowNormSq_hasDeriv H x t).rpow_const (Or.inl (flowNormSq_ne_zero H x hx t)))

theorem density_joint_continuous (N : ℝ) (H : E →L[ℝ] E) :
    Continuous (fun p : ℝ × Sphere E => flowDensity N H (p.2 : E) p.1) ∧
    Continuous (fun p : ℝ × Sphere E => densityD N H (p.2 : E) p.1) ∧
    Continuous (fun p : ℝ × Sphere E => densityDD N H (p.2 : E) p.1) := by
  have hX : Continuous (fun p : ℝ × Sphere E => (p.2 : E)) :=
    continuous_subtype_val.comp continuous_snd
  have h0 := (flow_joint_continuous H).comp (continuous_fst.prodMk hX)
  have h1 := (flow_joint_continuous H).comp (continuous_fst.prodMk (H.continuous.comp hX))
  have h2 := (flow_joint_continuous H).comp
    (continuous_fst.prodMk (H.continuous.comp (H.continuous.comp hX)))
  have hq : Continuous (fun p : ℝ × Sphere E => flowNormSq H (p.2 : E) p.1) :=
    h0.inner h0
  have hd : Continuous (fun p : ℝ × Sphere E => flowNormSqD H (p.2 : E) p.1) :=
    (h0.inner h1).const_mul 2
  have hdd : Continuous (fun p : ℝ × Sphere E => flowNormSqDD H (p.2 : E) p.1) :=
    ((h0.inner h2).add (h1.inner h1)).const_mul 2
  have hp (c : ℝ) : Continuous (fun p : ℝ × Sphere E => flowNormSq H (p.2 : E) p.1 ^ c) :=
    hq.rpow_const (fun p => Or.inl (flowNormSq_ne_zero H p.2 (unit_ne_zero p.2) p.1))
  exact ⟨hp _, (hd.mul_const _).mul (hp _),
    ((hdd.mul_const _).mul (hp _)).add
      ((hd.mul_const _).mul ((hd.mul_const _).mul (hp _)))⟩

omit [CompleteSpace E] in
theorem densityD_zero (N : ℝ) (H : E →L[ℝ] E) (x : Sphere E) :
    densityD N H (x : E) 0 = -N * inner ℝ (x : E) (H x) := by
  have hx : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  simp only [densityD, flowNormSqD, flowNormSq, flow_zero,
    real_inner_self_eq_norm_sq, hx, one_pow, Real.one_rpow]
  ring

theorem densityDD_zero (N : ℝ) (H : E →L[ℝ] E) (x : Sphere E)
    (hH : ∀ u v : E, inner ℝ (H u) v = inner ℝ u (H v)) :
    densityDD N H (x : E) 0 =
      N * (N + 2) * (inner ℝ (x : E) (H x)) ^ 2 -
        2 * N * inner ℝ (x : E) (H (H x)) := by
  have heq : deriv (flowDensity N H (x : E)) = densityD N H (x : E) :=
    funext (fun t => (density_hasDeriv N H x (unit_ne_zero x) t).deriv)
  rw [← (densityD_hasDeriv N H x (unit_ne_zero x) 0).deriv, ← heq]
  exact flowDensity_second_deriv_zero N H x (mem_sphere_zero_iff_norm.mp x.property) hH

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The unnormalized density integral; the actual image area also contains
the determinant factor, as proved in `exponential_area_integral`. -/
noncomputable def densityIntegral (mu : Measure (Sphere E)) (A : Set (Sphere E))
    (N : ℝ) (H : E →L[ℝ] E) (t : ℝ) : ℝ :=
  ∫ x in A, flowDensity N H (x : E) t ∂mu

theorem densityIntegral_hasDeriv (mu : Measure (Sphere E)) [IsFiniteMeasure mu]
    (A : Set (Sphere E)) (N : ℝ) (H : E →L[ℝ] E) (t : ℝ) :
    HasDerivAt (densityIntegral mu A N H) (∫ x in A, densityD N H (x : E) t ∂mu) t := by
  let : CompactSpace (Sphere E) := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  exact hasDerivAt_integral_compact (mu.restrict A) _ _ t
    (density_joint_continuous N H).1 (density_joint_continuous N H).2.1
    (fun t x => density_hasDeriv N H x (unit_ne_zero x) t)

theorem densityIntegralD_hasDeriv (mu : Measure (Sphere E)) [IsFiniteMeasure mu]
    (A : Set (Sphere E)) (N : ℝ) (H : E →L[ℝ] E) (t : ℝ) :
    HasDerivAt (fun s => ∫ x in A, densityD N H (x : E) s ∂mu)
      (∫ x in A, densityDD N H (x : E) t ∂mu) t := by
  let : CompactSpace (Sphere E) := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  exact hasDerivAt_integral_compact (mu.restrict A) _ _ t
    (density_joint_continuous N H).2.1 (density_joint_continuous N H).2.2
    (fun t x => densityD_hasDeriv N H x (unit_ne_zero x) t)

theorem densityIntegral_second_deriv (mu : Measure (Sphere E)) [IsFiniteMeasure mu]
    (A : Set (Sphere E)) (N : ℝ) (H : E →L[ℝ] E) (t : ℝ) :
    deriv (deriv (densityIntegral mu A N H)) t = ∫ x in A, densityDD N H (x : E) t ∂mu := by
  let : CompactSpace (Sphere E) := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  exact second_deriv_integral_compact (mu.restrict A) _ _ _ t
    (density_joint_continuous N H).1 (density_joint_continuous N H).2.1
    (density_joint_continuous N H).2.2
    (fun t x => density_hasDeriv N H x (unit_ne_zero x) t)
    (fun t x => densityD_hasDeriv N H x (unit_ne_zero x) t)

theorem densityIntegral_hasDeriv_zero (mu : Measure (Sphere E)) [IsFiniteMeasure mu]
    (A : Set (Sphere E)) (N : ℝ) (H : E →L[ℝ] E) :
    HasDerivAt (densityIntegral mu A N H)
      (∫ x in A, -N * inner ℝ (x : E) (H x) ∂mu) 0 := by
  simpa only [densityD_zero] using densityIntegral_hasDeriv mu A N H 0

theorem densityIntegral_second_deriv_zero (mu : Measure (Sphere E)) [IsFiniteMeasure mu]
    (A : Set (Sphere E)) (N : ℝ) (H : E →L[ℝ] E)
    (hH : ∀ u v : E, inner ℝ (H u) v = inner ℝ u (H v)) :
    deriv (deriv (densityIntegral mu A N H)) 0 =
      ∫ x in A, N * (N + 2) * (inner ℝ (x : E) (H x)) ^ 2 -
        2 * N * inner ℝ (x : E) (H (H x)) ∂mu := by
  rw [densityIntegral_second_deriv]
  simp_rw [densityDD_zero N H _ hH]

end ShadowVerification.Projective
#print axioms ShadowVerification.Projective.flow_joint_continuous
#print axioms ShadowVerification.Projective.flowNormSq_ne_zero
#print axioms ShadowVerification.Projective.flowNormSqD_hasDeriv
#print axioms ShadowVerification.Projective.density_hasDeriv
#print axioms ShadowVerification.Projective.densityD_hasDeriv
#print axioms ShadowVerification.Projective.density_joint_continuous
#print axioms ShadowVerification.Projective.densityD_zero
#print axioms ShadowVerification.Projective.densityDD_zero
#print axioms ShadowVerification.Projective.densityIntegral_hasDeriv
#print axioms ShadowVerification.Projective.densityIntegralD_hasDeriv
#print axioms ShadowVerification.Projective.densityIntegral_second_deriv
#print axioms ShadowVerification.Projective.densityIntegral_hasDeriv_zero
#print axioms ShadowVerification.Projective.densityIntegral_second_deriv_zero

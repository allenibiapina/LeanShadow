import LeanShadow.CouplingOperator

/-! # Operator-norm control from constant marginal masses

A positive joint measure with both marginals equal to `c • sigma` has
an L² pairing operator of norm at most `c`. For positive `c`, normalize
the measure and use the proved coupling contraction. The zero-mass case
is proved separately. This is the error bound needed for rotationally
invariant kernel truncations, including the singular case.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.ConstantMarginal

variable {X : Type*} [MeasurableSpace X]
  (sigma : Measure X)
  (rho : Measure (X × X))

theorem normalized_marginal (c : ℝ) (hc : 0 < c)
    (f : X × X → X) (hf : Measurable f)
    (hm : rho.map f = ENNReal.ofReal c • sigma) :
    MeasurePreserving f ((ENNReal.ofReal c)⁻¹ • rho) sigma := by
  refine ⟨hf, ?_⟩
  rw [Measure.map_smul, hm, smul_smul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top, one_smul]

/-- The zero marginal forces the entire positive joint measure to be zero. -/
theorem measure_zero_of_first_marginal_zero (h : rho.map Prod.fst = 0) : rho = 0 := by
  exact (Measure.map_eq_zero_iff measurable_fst.aemeasurable).mp h

/-- The marginal identities also justify integrability of every L² product. -/
theorem product_integrable (c : ℝ) (hc : 0 ≤ c)
    (hfst : rho.map Prod.fst = ENNReal.ofReal c • sigma)
    (hsnd : rho.map Prod.snd = ENNReal.ofReal c • sigma)
    (u v : Lp ℝ 2 sigma) : Integrable (fun z : X × X => u z.1 * v z.2) rho := by
  rcases eq_or_lt_of_le hc with he | he
  · have hc0 : c = 0 := he.symm
    subst c
    have hr : rho = 0 := measure_zero_of_first_marginal_zero rho (by simpa using hfst)
    simp [hr]
  · have hi := IncidenceRounding.product_integrable sigma ((ENNReal.ofReal c)⁻¹ • rho)
      (normalized_marginal sigma rho c he Prod.fst measurable_fst hfst)
      (normalized_marginal sigma rho c he Prod.snd measurable_snd hsnd) u v
    have hscale : ENNReal.ofReal c • ((ENNReal.ofReal c)⁻¹ • rho) = rho := by
      rw [smul_smul, ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr he)
        ENNReal.ofReal_ne_top, one_smul]
    have h := hi.smul_measure (c := ENNReal.ofReal c) ENNReal.ofReal_ne_top
    rwa [hscale] at h

theorem norm_le_of_positive_marginals (T : Lp ℝ 2 sigma →L[ℝ] Lp ℝ 2 sigma)
    (c : ℝ) (hc : 0 < c)
    (hfst : rho.map Prod.fst = ENNReal.ofReal c • sigma)
    (hsnd : rho.map Prod.snd = ENNReal.ofReal c • sigma)
    (hp : ∀ u v, inner ℝ u (T v) = ∫ z : X × X, u z.1 * v z.2 ∂rho) :
    ‖T‖ ≤ c := by
  let nu := (ENNReal.ofReal c)⁻¹ • rho
  have h1 : MeasurePreserving Prod.fst nu sigma :=
    normalized_marginal sigma rho c hc Prod.fst measurable_fst hfst
  have h2 : MeasurePreserving Prod.snd nu sigma :=
    normalized_marginal sigma rho c hc Prod.snd measurable_snd hsnd
  let F := CouplingOperator.operator sigma nu h1 h2
  have he (v : Lp ℝ 2 sigma) : T v = c • F v := by
    apply ext_inner_left ℝ
    intro u
    rw [real_inner_smul_right, CouplingOperator.pairing]
    change inner ℝ u (T v) = c * ∫ z : X × X, u z.1 * v z.2
      ∂((ENNReal.ofReal c)⁻¹ • rho)
    rw [integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal hc.le,
      smul_eq_mul, ← hp]
    field_simp
  apply T.opNorm_le_bound hc.le
  intro v
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  exact mul_le_mul_of_nonneg_left (CouplingOperator.norm_apply_le sigma nu h1 h2 v) hc.le

/-- Constant row and column masses control the operator norm, also when the mass is zero. -/
theorem norm_le (T : Lp ℝ 2 sigma →L[ℝ] Lp ℝ 2 sigma)
    (c : ℝ) (hc : 0 ≤ c)
    (hfst : rho.map Prod.fst = ENNReal.ofReal c • sigma)
    (hsnd : rho.map Prod.snd = ENNReal.ofReal c • sigma)
    (hp : ∀ u v, inner ℝ u (T v) = ∫ z : X × X, u z.1 * v z.2 ∂rho) :
    ‖T‖ ≤ c := by
  rcases eq_or_lt_of_le hc with he | he
  · have hc0 : c = 0 := he.symm
    subst c
    have hr : rho = 0 := measure_zero_of_first_marginal_zero rho (by simpa using hfst)
    have hT : T = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      apply ext_inner_left ℝ
      intro u
      simp only [hp, hr, integral_zero_measure, zero_apply, inner_zero_right]
    simp [hT]
  · exact norm_le_of_positive_marginals sigma rho T c he hfst hsnd hp

end ShadowVerification.ConstantMarginal
#print axioms ShadowVerification.ConstantMarginal.normalized_marginal
#print axioms ShadowVerification.ConstantMarginal.measure_zero_of_first_marginal_zero
#print axioms ShadowVerification.ConstantMarginal.norm_le_of_positive_marginals
#print axioms ShadowVerification.ConstantMarginal.norm_le
#print axioms ShadowVerification.ConstantMarginal.product_integrable

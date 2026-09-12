import LeanShadow.KernelMeasureBound

/-! # A signed Schur estimate from the absolute row and column masses -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.SignedKernel
variable {X : Type*} [MeasurableSpace X]
  (sigma : Measure X)

def absolute (u : Lp ℝ 2 sigma) : Lp ℝ 2 sigma := (Lp.memLp u).norm.toLp (fun x => ‖u x‖)

theorem absolute_ae (u : Lp ℝ 2 sigma) :
    (absolute sigma u : X → ℝ) =ᵐ[sigma] (fun x => ‖u x‖) := MemLp.coeFn_toLp _

theorem absolute_norm (u : Lp ℝ 2 sigma) : ‖absolute sigma u‖ = ‖u‖ := by
  rw [absolute, Lp.norm_toLp, eLpNorm_norm, Lp.norm_def]

theorem normalized_product_bound (rho : Measure (X × X))
    (hfst : MeasurePreserving Prod.fst rho sigma)
    (hsnd : MeasurePreserving Prod.snd rho sigma) (u v : Lp ℝ 2 sigma) :
    (∫ z : X × X, ‖u z.1‖ * ‖v z.2‖ ∂rho) ≤ ‖u‖ * ‖v‖ := by
  let F := CouplingOperator.operator sigma rho hfst hsnd
  have he : (∫ z : X × X, ‖u z.1‖ * ‖v z.2‖ ∂rho) =
      inner ℝ (absolute sigma u) (F (absolute sigma v)) := by
    rw [CouplingOperator.pairing]
    apply integral_congr_ae
    filter_upwards [hfst.quasiMeasurePreserving.ae (absolute_ae sigma u),
      hsnd.quasiMeasurePreserving.ae (absolute_ae sigma v)] with z hz hw
    rw [hz, hw]
  rw [he]
  calc
    _ ≤ ‖absolute sigma u‖ * ‖F (absolute sigma v)‖ := real_inner_le_norm _ _
    _ ≤ ‖absolute sigma u‖ * ‖absolute sigma v‖ :=
      mul_le_mul_of_nonneg_left (CouplingOperator.norm_apply_le sigma rho hfst hsnd _) (norm_nonneg _)
    _ = _ := by rw [absolute_norm, absolute_norm]

theorem product_bound (rho : Measure (X × X)) (c : ℝ) (hc : 0 ≤ c)
    (hfst : rho.map Prod.fst = ENNReal.ofReal c • sigma)
    (hsnd : rho.map Prod.snd = ENNReal.ofReal c • sigma) (u v : Lp ℝ 2 sigma) :
    (∫ z : X × X, ‖u z.1‖ * ‖v z.2‖ ∂rho) ≤ c * (‖u‖ * ‖v‖) := by
  rcases eq_or_lt_of_le hc with he | hp
  · subst c
    have hr := ConstantMarginal.measure_zero_of_first_marginal_zero rho (by simpa using hfst)
    simp [hr]
  · let eta := (ENNReal.ofReal c)⁻¹ • rho
    have h1 := ConstantMarginal.normalized_marginal sigma rho c hp Prod.fst measurable_fst hfst
    have h2 := ConstantMarginal.normalized_marginal sigma rho c hp Prod.snd measurable_snd hsnd
    have hb := normalized_product_bound sigma eta h1 h2 u v
    have hscale : ENNReal.ofReal c • eta = rho := by
      rw [smul_smul, ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hp)
        ENNReal.ofReal_ne_top, one_smul]
    calc
      _ = c * ∫ z : X × X, ‖u z.1‖ * ‖v z.2‖ ∂eta := by
        rw [← hscale, integral_smul_measure, ENNReal.toReal_ofReal hp.le, smul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hb hp.le

variable [IsFiniteMeasure sigma]

/-- Absolute row and column masses control an operator with a possibly signed kernel. -/
theorem norm_le (r : X × X → ℝ) (hm : Measurable r) (c : ℝ) (hc : 0 ≤ c)
    (hir : ∀ x, Integrable (fun y => ‖r (x,y)‖) sigma)
    (hic : ∀ y, Integrable (fun x => ‖r (x,y)‖) sigma)
    (hr : ∀ x, (∫ y, ‖r (x,y)‖ ∂sigma) = c)
    (hcol : ∀ y, (∫ x, ‖r (x,y)‖ ∂sigma) = c)
    (T : Lp ℝ 2 sigma →L[ℝ] Lp ℝ 2 sigma)
    (hp : ∀ u v, inner ℝ u (T v) =
      ∫ z : X × X, r z * (u z.1 * v z.2) ∂sigma.prod sigma) : ‖T‖ ≤ c := by
  let rho := KernelMeasure.joint sigma (fun z => ‖r z‖)
  have hfst : rho.map Prod.fst = ENNReal.ofReal c • sigma := by
    apply KernelMeasure.first_marginal sigma _ hm.norm.ennreal_ofReal
    intro x
    rw [← ofReal_integral_eq_lintegral_ofReal (hir x) (Eventually.of_forall fun _ => norm_nonneg _), hr]
  have hsnd : rho.map Prod.snd = ENNReal.ofReal c • sigma := by
    apply KernelMeasure.second_marginal sigma _ hm.norm.ennreal_ofReal
    intro y
    rw [← ofReal_integral_eq_lintegral_ofReal (hic y) (Eventually.of_forall fun _ => norm_nonneg _), hcol]
  have hb (u v : Lp ℝ 2 sigma) : ‖inner ℝ u (T v)‖ ≤ c * (‖u‖ * ‖v‖) := by
    rw [hp]
    calc
      _ ≤ ∫ z : X × X, ‖r z * (u z.1 * v z.2)‖ ∂sigma.prod sigma := norm_integral_le_integral_norm _
      _ = ∫ z : X × X, ‖u z.1‖ * ‖v z.2‖ ∂rho := by
        change _ = ∫ z : X × X, (fun x => ‖u x‖) z.1 * (fun y => ‖v y‖) z.2
          ∂KernelMeasure.joint sigma (fun z => ‖r z‖)
        rw [KernelMeasure.pairing sigma (fun z => ‖r z‖) hm.norm (fun z => norm_nonneg (r z))
          (fun x => ‖u x‖) (fun y => ‖v y‖)]
        simp only [norm_mul]
      _ ≤ _ := product_bound sigma rho c hc hfst hsnd u v
  apply T.opNorm_le_bound hc
  intro v
  have h := hb (T v) v
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h
  by_cases hz : ‖T v‖ = 0
  · rw [hz]
    exact mul_nonneg hc (norm_nonneg v)
  · apply (mul_le_mul_iff_right₀ (lt_of_le_of_ne (norm_nonneg (T v)) (Ne.symm hz))).mp
    calc
      ‖T v‖ * ‖T v‖ = ‖T v‖ ^ 2 := (pow_two _).symm
      _ ≤ c * (‖T v‖ * ‖v‖) := h
      _ = ‖T v‖ * (c * ‖v‖) := by ring

end ShadowVerification.SignedKernel
#print axioms ShadowVerification.SignedKernel.absolute_ae
#print axioms ShadowVerification.SignedKernel.absolute_norm
#print axioms ShadowVerification.SignedKernel.normalized_product_bound
#print axioms ShadowVerification.SignedKernel.product_bound
#print axioms ShadowVerification.SignedKernel.norm_le

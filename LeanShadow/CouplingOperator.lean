import LeanShadow.IncidenceRounding

/-! # Constructing an incidence operator from its joint measure

For any measure on pairs with equal prescribed marginals, the two coordinate
pullbacks are linear isometries between the actual L² spaces. The operator
`P₁* P₂` is therefore a bounded linear incidence operator. Its pairing formula,
contraction estimate, and self-adjointness under exchange symmetry are proved
here, so none needs to be a field of the geometric incidence data.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.CouplingOperator

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {nu : Measure X} {rho : Measure Y}

noncomputable def pullback (f : Y → X) (hf : MeasurePreserving f rho nu) :
    Lp ℝ 2 nu →L[ℝ] Lp ℝ 2 rho :=
  (Lp.compMeasurePreservingₗᵢ ℝ f hf).toContinuousLinearMap

theorem pullback_ae (f : Y → X) (hf : MeasurePreserving f rho nu) (u : Lp ℝ 2 nu) :
    (pullback f hf u : Y → ℝ) =ᵐ[rho] (fun y => u (f y)) :=
  Lp.coeFn_compMeasurePreserving u hf

theorem pullback_norm (f : Y → X) (hf : MeasurePreserving f rho nu) (u : Lp ℝ 2 nu) :
    ‖pullback f hf u‖ = ‖u‖ :=
  (Lp.compMeasurePreservingₗᵢ ℝ f hf).norm_map u

variable (nu : Measure X) (rho : Measure (X × X))
  (hfst : MeasurePreserving Prod.fst rho nu) (hsnd : MeasurePreserving Prod.snd rho nu)

noncomputable def operator : Lp ℝ 2 nu →L[ℝ] Lp ℝ 2 nu :=
  (pullback Prod.fst hfst).adjoint.comp (pullback Prod.snd hsnd)

/-- The operator represents integration against the actual joint measure. -/
theorem pairing (u v : Lp ℝ 2 nu) :
    inner ℝ u (operator nu rho hfst hsnd v) = ∫ z, u z.1 * v z.2 ∂rho := by
  rw [operator, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [pullback_ae Prod.fst hfst u, pullback_ae Prod.snd hsnd v] with z hz hw
  simp [hz, hw, mul_comm]

set_option maxHeartbeats 800000 in
/-- Marginal identities alone imply the probability-normalized norm bound. -/
theorem norm_apply_le (u : Lp ℝ 2 nu) : ‖operator nu rho hfst hsnd u‖ ≤ ‖u‖ := by
  let T := operator nu rho hfst hsnd
  have h := real_inner_le_norm (pullback Prod.fst hfst (T u)) (pullback Prod.snd hsnd u)
  have he : inner ℝ (T u) (T u) =
      inner ℝ (pullback Prod.fst hfst (T u)) (pullback Prod.snd hsnd u) :=
    ContinuousLinearMap.adjoint_inner_right (pullback Prod.fst hfst) (T u)
      (pullback Prod.snd hsnd u)
  rw [← he, real_inner_self_eq_norm_sq, pullback_norm, pullback_norm] at h
  change ‖T u‖ ≤ ‖u‖
  nlinarith [norm_nonneg (T u), norm_nonneg u]

/-- Exchange symmetry of the joint measure gives a self-adjoint operator. -/
theorem symmetric (hswap : MeasurePreserving Prod.swap rho rho) :
    (operator nu rho hfst hsnd).toLinearMap.IsSymmetric := by
  intro u v
  change inner ℝ (operator nu rho hfst hsnd u) v = inner ℝ u (operator nu rho hfst hsnd v)
  rw [real_inner_comm v (operator nu rho hfst hsnd u), pairing, pairing]
  have h := hswap.integral_comp (MeasurableEquiv.prodComm.measurableEmbedding)
    (fun z : X × X => u z.1 * v z.2)
  simpa only [Prod.fst_swap, Prod.snd_swap, mul_comm] using h

end ShadowVerification.CouplingOperator
#print axioms ShadowVerification.CouplingOperator.pullback_ae
#print axioms ShadowVerification.CouplingOperator.pullback_norm
#print axioms ShadowVerification.CouplingOperator.pairing
#print axioms ShadowVerification.CouplingOperator.norm_apply_le
#print axioms ShadowVerification.CouplingOperator.symmetric

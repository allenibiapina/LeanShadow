import LeanShadow.WeightedFlow
import LeanShadow.ShadowVerification

/-! # Necessary variation conditions at a smooth local maximum

The polarized exponential Hessian is negative semidefinite at a local
maximum. Its acceleration terms vanish because the full first derivative
vanishes. Closedness of the positive cone removes positive perturbations.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set Filter
open scoped Topology BigOperators
namespace ShadowVerification.FlowMaximum
open WeightedFlow Curves

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem flow_first_zero (u : E → ℝ) (H : E →L[ℝ] E) (x : E)
    (hu : DifferentiableAt ℝ u x) (hm : IsLocalMax u x) :
    deriv (fun t => u (Projective.flow H x t)) 0 = 0 := by
  rw [flow_first_deriv u H x hu, Elliptic.firstLine_zero_at_max hm]

theorem flowHessian_neg_posSemidef (u : E → ℝ) (H : ι → E →L[ℝ] E) (x : E)
    (hu : ContDiffAt ℝ 2 u x) (hm : IsLocalMax u x) :
    (-flowHessian u H x).PosSemidef := by
  have hc (i j : ι) : flowHessian u H x i j =
      ((fderiv ℝ (fderiv ℝ u) x (H i x)) (H j x) +
        (fderiv ℝ (fderiv ℝ u) x (H j x)) (H i x)) / 2 := by
    rw [flowHessian_coordinates u H x hu, hm.fderiv_eq_zero]
    simp
  refine posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · ext i j
    change -(flowHessian u H x j i) = -(flowHessian u H x i j)
    rw [hc, hc]
    ring
  · intro v
    have h := Elliptic.secondLine_nonpos_at_max hu.continuousAt hm (∑ i, v i • H i x)
    rw [secondLine_eq_fderiv u x _ hu] at h
    have heq : v ⬝ᵥ (flowHessian u H x *ᵥ v) =
        (fderiv ℝ (fderiv ℝ u) x (∑ i, v i • H i x)) (∑ i, v i • H i x) := by
      simp only [dotProduct, mulVec, hc, Finset.mul_sum]
      have hcontract := symmetric_contract (rankOne v)
        (fun i j => (fderiv ℝ (fderiv ℝ u) x (H i x)) (H j x)) (rankOne_isSymm v)
      simp only [rankOne] at hcontract
      simp only [map_sum, map_smul, _root_.sum_apply,
        _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
      convert hcontract using 1
      · apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
    simpa only [star_trivial, neg_mulVec, dotProduct_neg, heq, neg_nonneg] using h

theorem isClosed_posSemidef : IsClosed {M : Matrix ι ι ℝ | M.PosSemidef} := by
  simp only [posSemidef_iff_dotProduct_mulVec, IsHermitian, ofPred_and, ofPred_forall]
  exact (isClosed_eq (by fun_prop) continuous_id).inter
    (isClosed_iInter fun v => isClosed_le continuous_const (by fun_prop))

/-- The unperturbed matrix follows from all strictly positive perturbations. -/
theorem posSemidef_of_pos_perturbation (M R : Matrix ι ι ℝ)
    (h : ∀ eps : ℝ, 0 < eps → (M + eps • R).PosSemidef) : M.PosSemidef := by
  have hc : Continuous (fun eps : ℝ => M + eps • R) := by fun_prop
  have hlim : Tendsto (fun eps : ℝ => M + eps • R) (𝓝[>] 0) (𝓝 M) := by
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply isClosed_posSemidef.mem_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with eps heps
  exact h eps heps

end ShadowVerification.FlowMaximum
#print axioms ShadowVerification.FlowMaximum.flow_first_zero
#print axioms ShadowVerification.FlowMaximum.flowHessian_neg_posSemidef
#print axioms ShadowVerification.FlowMaximum.isClosed_posSemidef
#print axioms ShadowVerification.FlowMaximum.posSemidef_of_pos_perturbation

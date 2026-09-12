import LeanShadow.CurveCalculus
import Mathlib.Analysis.Matrix.PosDef

/-! # Weighted nondivergence operators and the checked maximum principle

A positive coefficient matrix is factored pointwise. The resulting directions
are frozen vectors at each point; their derivatives never enter the operator.
No regularity of a chosen eigenbasis is required.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set Filter
open scoped BigOperators Topology
namespace ShadowVerification.WeightedFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def factor (A : Matrix ι ι ℝ) : Matrix ι ι ℝ := by
  classical
  exact if h : A.PosSemidef then
    fun k i => Real.sqrt (h.isHermitian.eigenvalues k) *
      (h.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) i k
  else 0

/-- Fixed-size Gram factorization, including singular positive matrices. -/
theorem factor_identity (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (i j : ι) :
    A i j = ∑ k, factor A k i * factor A k j := by
  classical
  have hs := congrArg (fun M : Matrix ι ι ℝ => M i j) hA.isHermitian.spectral_theorem
  simp [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro k _
  simp only [factor, dif_pos hA]
  simp only [Matrix.IsHermitian.eigenvectorUnitary_apply]
  have hsq := Real.sq_sqrt (hA.eigenvalues_nonneg k)
  linear_combination -(hA.isHermitian.eigenvectorBasis k) i *
    (hA.isHermitian.eigenvectorBasis k) j * hsq

section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def directions (A : Matrix ι ι ℝ) (V : ι → E) (k : ι) : E :=
  ∑ i, factor A k i • V i

/-- Gram factorization preserves contraction against every bilinear form. -/
theorem contract_bilinear (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (V : ι → E) (B : E →L[ℝ] E →L[ℝ] ℝ) :
    (∑ k, B (directions A V k) (directions A V k)) =
      ∑ i, ∑ j, A i j * B (V i) (V j) := by
  have hexp (k : ι) : B (directions A V k) (directions A V k) =
      ∑ i, ∑ j, factor A k i * (factor A k j * B (V i) (V j)) := by
    unfold directions
    rw [map_sum B]
    simp only [_root_.sum_apply, map_smul, _root_.smul_apply, smul_eq_mul, map_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hexp]
  calc
    (∑ k, ∑ i, ∑ j, factor A k i * (factor A k j * B (V i) (V j))) =
        ∑ i, ∑ j, ∑ k, factor A k i * (factor A k j * B (V i) (V j)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul, ← factor_identity A hA]

/-- Coordinate form of a weighted nondivergence operator. -/
noncomputable def op (A : E → Matrix ι ι ℝ) (V : ι → E → E)
    (b : E → E) (u : E → ℝ) (x : E) : ℝ :=
  (∑ i, ∑ j, A x i j * (fderiv ℝ (fderiv ℝ u) x (V i x)) (V j x)) +
    fderiv ℝ u x (b x)

/-- Exact conversion to the operator used in the maximum principle. -/
theorem op_eq_frameOp (A : E → Matrix ι ι ℝ) (V : ι → E → E)
    (b : E → E) (u : E → ℝ) (x : E) (hA : (A x).PosSemidef)
    (hu : ContDiffAt ℝ 2 u x) :
    op A V b u x = Elliptic.frameOp
      (fun k y => directions (A y) (fun i => V i y) k) b u x := by
  unfold op Elliptic.frameOp
  simp_rw [Curves.secondLine_eq_fderiv u x _ hu,
    Curves.firstLine_eq_fderiv u x _ (hu.differentiableAt (by norm_num))]
  rw [contract_bilinear (A x) hA]

end Normed

section Inner
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The principal symbol is unchanged by the pointwise factorization. -/
theorem directions_symbol (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (V : ι → E) (v : E) :
    (∑ k, (inner ℝ v (directions A V k)) ^ 2) =
      (fun i => inner ℝ v (V i)) ⬝ᵥ (A *ᵥ (fun i => inner ℝ v (V i))) := by
  have h := contract_bilinear A hA V ((innerSL ℝ v).smulRight (innerSL ℝ v))
  change (∑ k, inner ℝ v (directions A V k) * inner ℝ v (directions A V k)) =
    ∑ i, ∑ j, A i j * (inner ℝ v (V i) * inner ℝ v (V j)) at h
  simpa only [← pow_two, dotProduct, Matrix.mulVec, Finset.mul_sum,
    mul_left_comm] using h

/-- The trace bound uses the original coefficients, not a smooth square root. -/
theorem directions_trace (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (V : ι → E) :
    (∑ k, ‖directions A V k‖ ^ 2) = ∑ i, ∑ j, A i j * inner ℝ (V i) (V j) := by
  have h := contract_bilinear A hA V (innerSL ℝ)
  change (∑ k, inner ℝ (directions A V k) (directions A V k)) =
    ∑ i, ∑ j, A i j * inner ℝ (V i) (V j) at h
  simpa only [real_inner_self_eq_norm_sq] using h

/-- The checked maximum principle accepts variable weighted coefficients and
bounds expressed directly in the original frame. -/
theorem local_strong_maximum [ProperSpace E]
    (A : E → Matrix ι ι ℝ) (V : ι → E → E) (b : E → E)
    (u : E → ℝ) (x₀ : E) (R lam C B : ℝ)
    (hR : 0 < R) (hlam : 0 < lam) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hu : Continuous u)
    (hmax : ∀ x, ‖x - x₀‖ < R → u x ≤ u x₀)
    (hsmooth : ∀ x, ‖x - x₀‖ < R → ContDiffAt ℝ 2 u x)
    (hA : ∀ x, ‖x - x₀‖ < R → (A x).PosSemidef)
    (hsub : ∀ x, ‖x - x₀‖ < R → 0 ≤ op A V b u x)
    (hell : ∀ x, ‖x - x₀‖ < R → ∀ v : E,
      lam * ‖v‖ ^ 2 ≤ (fun i => inner ℝ v (V i x)) ⬝ᵥ
        (A x *ᵥ (fun i => inner ℝ v (V i x))))
    (htrace : ∀ x, ‖x - x₀‖ < R →
      (∑ i, ∑ j, A x i j * inner ℝ (V i x) (V j x)) ≤ C)
    (hdrift : ∀ x, ‖x - x₀‖ < R → ‖b x‖ ≤ B) :
    ∀ x, ‖x - x₀‖ < R / 4 → u x = u x₀ := by
  apply Elliptic.local_strong_maximum
    (fun k y => directions (A y) (fun i => V i y) k) b u x₀
    R lam C B hR hlam hC hB hu hmax
  · intro x hx v
    have hl : ContDiff ℝ 2 (fun t : ℝ => x + t • v) :=
      contDiff_const.add (contDiff_id.smul contDiff_const)
    have hx0 : ContDiffAt ℝ 2 u (x + (0 : ℝ) • v) := by simpa using hsmooth x hx
    exact hx0.comp 0 hl.contDiffAt
  · intro x hx
    rw [← op_eq_frameOp A V b u x (hA x hx) (hsmooth x hx)]
    exact hsub x hx
  · intro x hx v
    rw [directions_symbol (A x) (hA x hx)]
    exact hell x hx v
  · intro x hx
    rw [directions_trace (A x) (hA x hx)]
    exact htrace x hx
  · exact hdrift

end Inner
end ShadowVerification.WeightedFrame
#print axioms ShadowVerification.WeightedFrame.factor_identity
#print axioms ShadowVerification.WeightedFrame.contract_bilinear
#print axioms ShadowVerification.WeightedFrame.op_eq_frameOp
#print axioms ShadowVerification.WeightedFrame.directions_symbol
#print axioms ShadowVerification.WeightedFrame.directions_trace
#print axioms ShadowVerification.WeightedFrame.local_strong_maximum

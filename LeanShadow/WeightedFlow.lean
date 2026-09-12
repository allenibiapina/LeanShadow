import LeanShadow.WeightedFrame

/-! # Weighted exponential variations with their full drift

The field Hessian is defined by polarizing actual exponential-flow second
derivatives. Contracting it with a symmetric variable weight gives precisely
a nondivergence operator, including the acceleration terms. The weight is
never differentiated.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators Topology
namespace ShadowVerification.WeightedFlow
open WeightedFrame Curves

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def flowHessian (u : E → ℝ) (H : ι → E →L[ℝ] E) (x : E) :
    Matrix ι ι ℝ := fun i j =>
  (deriv (deriv (fun t => u (Projective.flow (H i + H j) x t))) 0 -
    deriv (deriv (fun t => u (Projective.flow (H i) x t))) 0 -
    deriv (deriv (fun t => u (Projective.flow (H j) x t))) 0) / 2

noncomputable def acceleration (A : E → Matrix ι ι ℝ)
    (H : ι → E →L[ℝ] E) (x : E) : E :=
  ∑ i, ∑ j, A x i j • ((1 / 2 : ℝ) • (H i (H j x) + H j (H i x)))

omit [DecidableEq ι] in
/-- Symmetrization has no effect when contracted with a symmetric coefficient matrix. -/
theorem symmetric_contract (A Q : Matrix ι ι ℝ) (hA : A.IsSymm) :
    (∑ i, ∑ j, A i j * ((Q i j + Q j i) / 2)) = ∑ i, ∑ j, A i j * Q i j := by
  have hswap : (∑ i, ∑ j, A i j * Q j i) = ∑ i, ∑ j, A i j * Q i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hA.apply j i]
  have ht (i j : ι) : A i j * ((Q i j + Q j i) / 2) =
      (A i j * Q i j + A i j * Q j i) / 2 := by ring
  simp_rw [ht, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [hswap]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The polarized second derivative retains both orders of mixed acceleration. -/
theorem flowHessian_coordinates (u : E → ℝ) (H : ι → E →L[ℝ] E)
    (x : E) (hu : ContDiffAt ℝ 2 u x) (i j : ι) :
    flowHessian u H x i j =
      ((fderiv ℝ (fderiv ℝ u) x (H i x)) (H j x) +
        (fderiv ℝ (fderiv ℝ u) x (H j x)) (H i x)) / 2 +
      fderiv ℝ u x ((1 / 2 : ℝ) • (H i (H j x) + H j (H i x))) :=
  polarized_flow_second_deriv u (H i) (H j) x hu

omit [DecidableEq ι] in
/-- The weighted flow Hessian is exactly a coordinate operator with drift. -/
theorem weighted_flow_eq_op (A : E → Matrix ι ι ℝ)
    (H : ι → E →L[ℝ] E) (d : E → E) (u : E → ℝ) (x : E)
    (hA : (A x).IsSymm) (hu : ContDiffAt ℝ 2 u x) :
    (∑ i, ∑ j, A x i j * flowHessian u H x i j) +
        Elliptic.firstLine u x (d x) =
      op A (fun i y => H i y) (fun y => acceleration A H y + d y) u x := by
  simp_rw [flowHessian_coordinates u H x hu, mul_add, Finset.sum_add_distrib]
  rw [symmetric_contract (A x) _ hA,
    firstLine_eq_fderiv u x _ (hu.differentiableAt (by norm_num))]
  unfold op acceleration
  simp only [map_add, map_sum, map_smul, smul_eq_mul]
  ring

/-- The same identity holds for the actual sums-of-squares operator used by
our maximum-principle proof. Its factor directions are frozen at each point. -/
theorem weighted_flow_eq_frameOp (A : E → Matrix ι ι ℝ)
    (H : ι → E →L[ℝ] E) (d : E → E) (u : E → ℝ) (x : E)
    (hA : (A x).PosSemidef) (hu : ContDiffAt ℝ 2 u x) :
    (∑ i, ∑ j, A x i j * flowHessian u H x i j) +
        Elliptic.firstLine u x (d x) =
      Elliptic.frameOp
        (fun k y => directions (A y) (fun i => H i y) k)
        (fun y => acceleration A H y + d y) u x := by
  rw [weighted_flow_eq_op A H d u x (by simpa using hA.isHermitian) hu]
  exact op_eq_frameOp A (fun i y => H i y) _ u x hA hu

end ShadowVerification.WeightedFlow
#print axioms ShadowVerification.WeightedFlow.symmetric_contract
#print axioms ShadowVerification.WeightedFlow.flowHessian_coordinates
#print axioms ShadowVerification.WeightedFlow.weighted_flow_eq_op
#print axioms ShadowVerification.WeightedFlow.weighted_flow_eq_frameOp

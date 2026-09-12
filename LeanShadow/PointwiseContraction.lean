import LeanShadow.ProjectionSquares

/-! # The actual pointwise Hessian contraction

For any Frobenius-orthonormal basis of the symmetric trace-free matrices,
we prove the manuscript's pointwise contraction and zero-trace identities.
The kernel is defined by its explicit coefficients; neither identity is
assumed. Integration and identification with the area Hessian remain separate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix
open Matrix Module
namespace ShadowVerification.Frame

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem pairing_outer (H : Matrix n n ℝ) (u v : n → ℝ) :
    pairing H (vecMulVec u v) = u ⬝ᵥ (H *ᵥ v) := by
  simp only [pairing, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {ι : Type*} [Fintype ι]

theorem quadratic_reconstruction [Nonempty n]
    (b : Basis ι ℝ (symZero (n := n))) (hb : IsOrthonormal b) (x : n → ℝ) :
    (∑ i, (x ⬝ᵥ (frame b i *ᵥ x)) • frame b i) = projection (vecMulVec x x) := by
  simpa only [pairing_outer] using frame_reconstruction b hb (vecMulVec x x)

theorem row_reconstruction [Nonempty n]
    (b : Basis ι ℝ (symZero (n := n))) (hb : IsOrthonormal b) (x : n → ℝ) (k : n) :
    (∑ i, (frame b i *ᵥ x) k • frame b i) =
      projection (vecMulVec (Pi.single k 1) x) := by
  simpa [pairing_outer] using frame_reconstruction b hb (vecMulVec (Pi.single k 1) x)

/-- The first-variation coefficients reconstruct the actual moment density. -/
theorem first_variation_reconstruction [Nonempty n]
    (b : Basis ι ℝ (symZero (n := n))) (hb : IsOrthonormal b)
    (x : n → ℝ) (hx : x ⬝ᵥ x = 1) :
    (∑ i, (-(Fintype.card n : ℝ) * (x ⬝ᵥ (frame b i *ᵥ x))) • frame b i) =
      1 - (Fintype.card n : ℝ) • vecMulVec x x := by
  have hn : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp_rw [mul_smul]
  rw [← Finset.smul_sum, quadratic_reconstruction b hb, projection_outer_self x hx]
  ext a c
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  field_simp
  ring

omit [DecidableEq n] in
theorem contraction_sum {κ : Type*} [Fintype κ]
    (H : ι → Matrix n n ℝ) (Q : κ → Matrix ι ι ℝ) :
    manuscriptContraction H (∑ k, Q k) = ∑ k, manuscriptContraction H (Q k) := by
  classical
  simp only [manuscriptContraction, Matrix.sum_apply, Finset.sum_div, Finset.sum_smul]
  calc
    (∑ i, ∑ j, ∑ k, (Q k i j / 2) • (H i * H j + H j * H i)) =
        ∑ i, ∑ k, ∑ j, (Q k i j / 2) • (H i * H j + H j * H i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, (Q k i j / 2) • (H i * H j + H j * H i) := Finset.sum_comm

/-- Coefficient matrix of the polarized trace-free second-variation density. -/
noncomputable def pointwiseKernel (H : ι → Matrix n n ℝ) (x : n → ℝ) : Matrix ι ι ℝ :=
  ((Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2)) •
      rankOne (fun i => x ⬝ᵥ (H i *ᵥ x)) -
    (2 * (Fintype.card n : ℝ)) • ∑ k, rankOne (fun i => (H i *ᵥ x) k)

omit [DecidableEq n] [Fintype ι] in
theorem pointwiseKernel_apply (H : ι → Matrix n n ℝ) (x : n → ℝ) (i j : ι) :
    pointwiseKernel H x i j =
      (Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2) *
        (x ⬝ᵥ (H i *ᵥ x)) * (x ⬝ᵥ (H j *ᵥ x)) -
      2 * (Fintype.card n : ℝ) * ((H i *ᵥ x) ⬝ᵥ (H j *ᵥ x)) := by
  simp only [pointwiseKernel, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.sum_apply, rankOne, dotProduct]
  ring

omit [DecidableEq n] [Fintype ι] in
/-- On a symmetric direction the diagonal is the actual second-variation
density, with the iterated action H(Hx). -/
theorem pointwiseKernel_diagonal (H : ι → Matrix n n ℝ) (x : n → ℝ) (i : ι)
    (hi : (H i).IsSymm) :
    pointwiseKernel H x i i =
      (Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2) *
        (x ⬝ᵥ (H i *ᵥ x)) ^ 2 -
      2 * (Fintype.card n : ℝ) * (x ⬝ᵥ (H i *ᵥ (H i *ᵥ x))) := by
  have h : x ⬝ᵥ (H i *ᵥ (H i *ᵥ x)) = (H i *ᵥ x) ⬝ᵥ (H i *ᵥ x) := by
    simpa only [hi.eq] using dotProduct_transpose_mulVec (H i) x (H i *ᵥ x)
  rw [pointwiseKernel_apply, h]
  ring

/-- Lemma 5.1's contraction identity for the explicitly defined kernel. -/
theorem pointwise_contraction [Nonempty n]
    (b : Basis ι ℝ (symZero (n := n))) (hb : IsOrthonormal b)
    (x : n → ℝ) (hx : x ⬝ᵥ x = 1) :
    manuscriptContraction (frame b) (pointwiseKernel (frame b) x) =
      (((Fintype.card n : ℝ) - 2) / 2) •
        ((Fintype.card n : ℝ) • vecMulVec x x - 1) := by
  rw [pointwiseKernel, manuscriptContraction_sub, manuscriptContraction_smul,
    manuscriptContraction_smul, contraction_sum, manuscriptContraction_rankOne,
    quadratic_reconstruction b hb]
  simp_rw [manuscriptContraction_rankOne, row_reconstruction b hb, ← pow_two]
  exact projected_pointwise_identity x hx

omit [DecidableEq n] in
theorem trace_mul_eq_pairing (A B : Matrix n n ℝ) (hB : B.IsSymm) :
    (A * B).trace = pairing A B := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pairing]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hB.apply i j]

omit [DecidableEq n] in
/-- Frobenius orthonormality makes contraction preserve operator trace. -/
theorem contraction_trace (b : Basis ι ℝ (symZero (n := n))) (hb : IsOrthonormal b)
    (Q : Matrix ι ι ℝ) : (manuscriptContraction (frame b) Q).trace = Q.trace := by
  classical
  unfold IsOrthonormal at hb
  have hpair : ∀ i j, (frame b i * frame b j).trace = if i = j then 1 else 0 := by
    intro i j
    exact (trace_mul_eq_pairing (frame b i) (frame b j) (b j).property.1).trans (hb i j)
  have hterm : ∀ i j, (Q i j / 2) *
      ((if i = j then (1 : ℝ) else 0) + (if j = i then (1 : ℝ) else 0)) =
      if i = j then Q i j else 0 := by
    intro i j
    by_cases hij : i = j
    · simp only [hij, if_true]
      ring
    · simp [hij, Ne.symm hij]
  simp only [manuscriptContraction, Matrix.trace_sum, Matrix.trace_smul,
    Matrix.trace_add, smul_eq_mul, hpair, hterm]
  simp [Matrix.trace, Matrix.diag]

/-- The same pointwise kernel has zero trace on the trace-free matrix space. -/
theorem pointwise_trace [Nonempty n]
    (b : Basis ι ℝ (symZero (n := n))) (hb : IsOrthonormal b)
    (x : n → ℝ) (hx : x ⬝ᵥ x = 1) :
    (pointwiseKernel (frame b) x).trace = 0 := by
  rw [← contraction_trace b hb, pointwise_contraction b hb x hx]
  simp [Matrix.trace_smul, Matrix.trace_sub, trace_vecMulVec, hx]

end ShadowVerification.Frame
#print axioms ShadowVerification.Frame.pairing_outer
#print axioms ShadowVerification.Frame.quadratic_reconstruction
#print axioms ShadowVerification.Frame.row_reconstruction
#print axioms ShadowVerification.Frame.first_variation_reconstruction
#print axioms ShadowVerification.Frame.contraction_sum
#print axioms ShadowVerification.Frame.pointwiseKernel_apply
#print axioms ShadowVerification.Frame.pointwiseKernel_diagonal
#print axioms ShadowVerification.Frame.pointwise_contraction
#print axioms ShadowVerification.Frame.trace_mul_eq_pairing
#print axioms ShadowVerification.Frame.contraction_trace
#print axioms ShadowVerification.Frame.pointwise_trace

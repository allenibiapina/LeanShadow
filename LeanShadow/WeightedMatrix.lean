import LeanShadow.ShadowVerification
import Mathlib.Analysis.Matrix.Normed

/-! # Matrix estimates for the elliptic weight

All norms in this module are Frobenius norms. The estimates apply to actual
finite matrices and their traces, including the cubic error and the positive
principal quadratic form in the nonisotropy argument.
-/
set_option autoImplicit false
open scoped BigOperators Matrix Matrix.Norms.Frobenius
namespace ShadowVerification.Weighted

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem frobenius_sq (A : Matrix n n ℝ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp_rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

/-- Cauchy--Schwarz for the trace pairing, expressed in the actual matrix norm. -/
theorem abs_trace_mul_le (A B : Matrix n n ℝ) :
    |(A * B).trace| ≤ ‖A‖ * ‖B‖ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (n × n))
    (fun ij => A ij.1 ij.2) (fun ij => B ij.2 ij.1)
  simp only [Fintype.sum_prod_type] at hcs
  have hB : (∑ i, ∑ j, B j i ^ 2) = ‖B‖ ^ 2 := by
    rw [frobenius_sq, Finset.sum_comm]
  rw [hB, ← frobenius_sq A] at hcs
  have htr : (A * B).trace = ∑ i, ∑ j, A i j * B j i := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [← htr] at hcs
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    (by simpa only [sq_abs, mul_pow] using hcs)

theorem trace_sq_of_symm (G : Matrix n n ℝ) (hG : G.IsSymm) :
    (G ^ 2).trace = ‖G‖ ^ 2 := by
  rw [frobenius_sq, pow_two]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hG.apply j i]
  ring

theorem abs_trace_cube_le (G : Matrix n n ℝ) :
    |(G ^ 3).trace| ≤ ‖G‖ ^ 3 := by
  calc
    |(G ^ 3).trace| = |(G ^ 2 * G).trace| := by rw [pow_succ]
    _ ≤ ‖G ^ 2‖ * ‖G‖ := abs_trace_mul_le _ _
    _ ≤ (‖G‖ * ‖G‖) * ‖G‖ :=
      mul_le_mul_of_nonneg_right (by simpa only [pow_two] using Matrix.frobenius_norm_mul G G)
        (norm_nonneg _)
    _ = ‖G‖ ^ 3 := by ring

/-- The principal quadratic form of the weight `I - L G` is bounded below
on every symmetric matrix `H`; in particular it is uniformly positive on the
symmetric trace-free subspace used in the manuscript. -/
theorem weighted_quadratic_lower_bound (G H : Matrix n n ℝ) (L : ℝ)
    (hH : H.IsSymm) (hL : 0 ≤ L) (hsmall : L * ‖G‖ ≤ 1 / 2) :
    (1 / 2 : ℝ) * ‖H‖ ^ 2 ≤ ((H ^ 2) * (1 - L • G)).trace := by
  have habs : |((H ^ 2) * G).trace| ≤ ‖H‖ ^ 2 * ‖G‖ := by
    exact (abs_trace_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right
        (by simpa only [pow_two] using Matrix.frobenius_norm_mul H H) (norm_nonneg _))
  have ht : L * ((H ^ 2) * G).trace ≤ ‖H‖ ^ 2 / 2 := by
    have ht' := mul_le_mul_of_nonneg_left ((le_abs_self _).trans habs) hL
    have hs := mul_le_mul_of_nonneg_left hsmall (sq_nonneg ‖H‖)
    nlinarith
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.trace_sub,
    Matrix.trace_smul, trace_sq_of_symm H hH]
  change _ ≤ ‖H‖ ^ 2 - L * ((H ^ 2) * G).trace
  linarith

/-- The exact weighted trace identity behind the positive source term. -/
theorem weighted_trace_identity (G : Matrix n n ℝ) (hG : G.IsSymm)
    (htrace : G.trace = 0) (d k rho L : ℝ) :
    (((-d * k) • G - rho • (G ^ 2)) * (1 - L • G)).trace =
      (d * L * k - rho) * ‖G‖ ^ 2 + rho * L * (G ^ 3).trace := by
  have hGG : G * G = G ^ 2 := (pow_two G).symm
  have hGGG : G ^ 2 * G = G ^ 3 := (pow_succ G 2).symm
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_one,
    Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, htrace, hGG, hGGG,
    trace_sq_of_symm G hG, smul_eq_mul]
  ring

/-- Matrix-level coercivity, without a separately assumed bound on the cubic
trace. The smallness hypothesis controls that term through the Frobenius norm. -/
theorem weighted_source_lower_bound (G : Matrix n n ℝ) (hG : G.IsSymm)
    (htrace : G.trace = 0) (d k rho L : ℝ) (hrho : 0 ≤ rho) (hL : 0 ≤ L)
    (hcoefficient : 2 * rho ≤ d * L * k) (hsmall : L * ‖G‖ ≤ 1 / 2) :
    rho / 2 * ‖G‖ ^ 2 ≤
      (((-d * k) • G - rho • (G ^ 2)) * (1 - L • G)).trace := by
  rw [weighted_trace_identity G hG htrace]
  apply weighted_coercivity rho (d * L * k) L (‖G‖ ^ 2) ((G ^ 3).trace)
    hrho (sq_nonneg _) hcoefficient
  rw [abs_mul, abs_of_nonneg hL]
  have hc := mul_le_mul_of_nonneg_left (abs_trace_cube_le G) hL
  have hs := mul_le_mul_of_nonneg_left hsmall (sq_nonneg ‖G‖)
  nlinarith

section Coefficients
variable {ι : Type*} [Fintype ι]

/-- Coefficients of the weighted quadratic form on the symmetric frame. -/
noncomputable def weightCoefficients
    (H : ι → Matrix n n ℝ) (Z : Matrix n n ℝ) : Matrix ι ι ℝ :=
  fun i j => (1 / 2 : ℝ) * ((H i * H j + H j * H i) * Z).trace

omit [DecidableEq n] [Fintype ι] in
theorem weightCoefficients_symm (H : ι → Matrix n n ℝ) (Z : Matrix n n ℝ) :
    (weightCoefficients H Z).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, weightCoefficients, add_comm]

omit [DecidableEq n] in
/-- The coefficient contraction is exactly the trace pairing with Ψ. -/
theorem weightCoefficients_contract (H : ι → Matrix n n ℝ)
    (Z : Matrix n n ℝ) (Q : Matrix ι ι ℝ) :
    (∑ i, ∑ j, Q i j * weightCoefficients H Z i j) =
      (manuscriptContraction H Q * Z).trace := by
  simp only [manuscriptContraction, Finset.sum_mul, Matrix.smul_mul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, weightCoefficients]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weightCoefficients_quadratic (H : ι → Matrix n n ℝ)
    (Z : Matrix n n ℝ) (v : ι → ℝ) :
    v ⬝ᵥ (weightCoefficients H Z *ᵥ v) =
      (((∑ i, v i • H i) ^ 2) * Z).trace := by
  have h := weightCoefficients_contract H Z (rankOne v)
  rw [manuscriptContraction_rankOne] at h
  rw [pow_two]
  rw [← h]
  simp only [dotProduct, Matrix.mulVec, rankOne, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Uniform lower bound on the weighted principal form, written directly in
frame coordinates. -/
theorem weightCoefficients_lower_bound (H : ι → Matrix n n ℝ)
    (hH : ∀ i, (H i).IsSymm) (G : Matrix n n ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hsmall : L * ‖G‖ ≤ 1 / 2) (v : ι → ℝ) :
    (1 / 2 : ℝ) * ‖∑ i, v i • H i‖ ^ 2 ≤
      v ⬝ᵥ (weightCoefficients H (1 - L • G) *ᵥ v) := by
  rw [weightCoefficients_quadratic]
  apply weighted_quadratic_lower_bound G _ L _ hL hsmall
  change (∑ i, v i • H i)ᵀ = ∑ i, v i • H i
  simp only [Matrix.transpose_sum, Matrix.transpose_smul, (hH _).eq]

/-- Linear independence of the matrix frame makes the weighted coefficient
matrix positive definite. -/
theorem weightCoefficients_posDef (H : ι → Matrix n n ℝ)
    (hH : ∀ i, (H i).IsSymm)
    (hinj : Function.Injective (fun v : ι → ℝ => ∑ i, v i • H i))
    (G : Matrix n n ℝ) (L : ℝ) (hL : 0 ≤ L) (hsmall : L * ‖G‖ ≤ 1 / 2) :
    (weightCoefficients H (1 - L • G)).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · simpa using weightCoefficients_symm H (1 - L • G)
  · intro v hv
    have hn : (∑ i, v i • H i) ≠ 0 := by
      intro heq
      apply hv
      apply hinj
      simpa using heq
    have hp : 0 < (1 / 2 : ℝ) * ‖∑ i, v i • H i‖ ^ 2 :=
      mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hn))
    simpa only [star_trivial] using hp.trans_le
      (weightCoefficients_lower_bound H hH G L hL hsmall v)

/-- Combining the geometric contraction identity with the actual matrix
weight gives the positive source term. The contraction identity itself is a
premise here and still needs its geometric derivation in Lean. -/
theorem contracted_source_lower_bound (H : ι → Matrix n n ℝ)
    (Q : Matrix ι ι ℝ) (D G : Matrix n n ℝ) (c d k rho L : ℝ)
    (hG : G.IsSymm) (htrace : G.trace = 0) (hrho : 0 ≤ rho) (hL : 0 ≤ L)
    (hcoefficient : 2 * rho ≤ d * L * k) (hsmall : L * ‖G‖ ≤ 1 / 2)
    (hidentity : manuscriptContraction H Q = c • D + (-d * k) • G - rho • G ^ 2) :
    rho / 2 * ‖G‖ ^ 2 ≤
      (∑ i, ∑ j, Q i j * weightCoefficients H (1 - L • G) i j) -
        c * (D * (1 - L • G)).trace := by
  rw [weightCoefficients_contract, hidentity]
  have heq : ((c • D + (-d * k) • G - rho • G ^ 2) * (1 - L • G)).trace -
      c * (D * (1 - L • G)).trace =
      (((-d * k) • G - rho • G ^ 2) * (1 - L • G)).trace := by
    simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul,
      Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    ring
  rw [heq]
  exact weighted_source_lower_bound G hG htrace d k rho L hrho hL hcoefficient hsmall

end Coefficients

end ShadowVerification.Weighted
#print axioms ShadowVerification.Weighted.frobenius_sq
#print axioms ShadowVerification.Weighted.abs_trace_mul_le
#print axioms ShadowVerification.Weighted.trace_sq_of_symm
#print axioms ShadowVerification.Weighted.abs_trace_cube_le
#print axioms ShadowVerification.Weighted.weighted_quadratic_lower_bound
#print axioms ShadowVerification.Weighted.weighted_trace_identity
#print axioms ShadowVerification.Weighted.weighted_source_lower_bound

#print axioms ShadowVerification.Weighted.weightCoefficients_symm
#print axioms ShadowVerification.Weighted.weightCoefficients_contract
#print axioms ShadowVerification.Weighted.weightCoefficients_quadratic
#print axioms ShadowVerification.Weighted.weightCoefficients_lower_bound
#print axioms ShadowVerification.Weighted.contracted_source_lower_bound

#print axioms ShadowVerification.Weighted.weightCoefficients_posDef

import LeanShadow.FrameProjection

/-! # Squares of the projected rank-one and coordinate-row matrices

These identities are the finite-dimensional calculation underlying the
pointwise Hessian contraction. All sums range over actual coordinates.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix
open Matrix
namespace ShadowVerification.Frame

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem projection_row (x : n → ℝ) (k : n) :
    projection (vecMulVec (Pi.single k 1) x) =
      (1 / 2 : ℝ) • (vecMulVec (Pi.single k 1) x + vecMulVec x (Pi.single k 1)) -
        (x k / (Fintype.card n : ℝ)) • 1 := by
  simp [projection, transpose_vecMulVec, trace_vecMulVec]

theorem projection_row_square (x : n → ℝ) (hx : x ⬝ᵥ x = 1) (k : n) :
    projection (vecMulVec (Pi.single k 1) x) ^ 2 =
      (1 / 4 : ℝ) • vecMulVec (Pi.single k 1) (Pi.single k 1) +
      (1 / 4 : ℝ) • vecMulVec x x +
      (((1 / 4 : ℝ) - 1 / (Fintype.card n : ℝ)) * x k) •
        (vecMulVec (Pi.single k 1) x + vecMulVec x (Pi.single k 1)) +
      (x k ^ 2 / (Fintype.card n : ℝ) ^ 2) • (1 : Matrix n n ℝ) := by
  have hee : (Pi.single k (1 : ℝ)) ⬝ᵥ Pi.single k 1 = 1 := by simp
  have hxe : x ⬝ᵥ Pi.single k 1 = x k := by simp
  have hex : (Pi.single k (1 : ℝ)) ⬝ᵥ x = x k := by simp
  rw [projection_row, pow_two]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul,
    vecMulVec_mul_vecMulVec, vecMulVec_smul, hx, hee, hxe, hex, one_smul]
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem coordinate_outer_sum :
    (∑ k : n, vecMulVec (Pi.single k (1 : ℝ)) (Pi.single k 1)) = 1 := by
  ext a b
  simp [Matrix.sum_apply, vecMulVec_apply, Matrix.one_apply, Pi.single_apply]

theorem weighted_row_sum (x : n → ℝ) :
    (∑ k, x k • (vecMulVec (Pi.single k 1) x + vecMulVec x (Pi.single k 1))) =
      (2 : ℝ) • vecMulVec x x := by
  ext a b
  simp [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Pi.single_apply,
    Finset.sum_add_distrib, mul_comm]
  ring

theorem projection_row_square_sum (x : n → ℝ) (hx : x ⬝ᵥ x = 1) :
    (∑ k, projection (vecMulVec (Pi.single k 1) x) ^ 2) =
      ((1 / 4 : ℝ) + 1 / (Fintype.card n : ℝ) ^ 2) • (1 : Matrix n n ℝ) +
      ((Fintype.card n : ℝ) / 4 + 1 / 2 - 2 / (Fintype.card n : ℝ)) • vecMulVec x x := by
  have hsq : (∑ k, x k ^ 2) = 1 := by simpa only [dotProduct, pow_two] using hx
  have hcross : (∑ k, (((1 / 4 : ℝ) - 1 / (Fintype.card n : ℝ)) * x k) •
      (vecMulVec (Pi.single k 1) x + vecMulVec x (Pi.single k 1))) =
      ((1 / 4 : ℝ) - 1 / (Fintype.card n : ℝ)) • ((2 : ℝ) • vecMulVec x x) := by
    rw [← weighted_row_sum x, Finset.smul_sum]
    simp only [smul_smul]
  have hlast : (∑ k, (x k ^ 2 / (Fintype.card n : ℝ) ^ 2) • (1 : Matrix n n ℝ)) =
      (1 / (Fintype.card n : ℝ) ^ 2) • (1 : Matrix n n ℝ) := by
    rw [← Finset.sum_smul, ← Finset.sum_div, hsq]
  have hconst : (∑ _k : n, (1 / 4 : ℝ) • vecMulVec x x) =
      ((Fintype.card n : ℝ) / 4) • vecMulVec x x := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    ring
  simp_rw [projection_row_square x hx]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.smul_sum, coordinate_outer_sum, hcross, hlast, hconst]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem projection_outer_self (x : n → ℝ) (hx : x ⬝ᵥ x = 1) :
    projection (vecMulVec x x) = vecMulVec x x - (1 / (Fintype.card n : ℝ)) • 1 := by
  rw [projection, transpose_vecMulVec, trace_vecMulVec, hx]
  ext a b
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

theorem projection_outer_self_square (x : n → ℝ) (hx : x ⬝ᵥ x = 1) :
    projection (vecMulVec x x) ^ 2 =
      (1 - 2 / (Fintype.card n : ℝ)) • vecMulVec x x +
      (1 / (Fintype.card n : ℝ) ^ 2) • (1 : Matrix n n ℝ) := by
  rw [projection_outer_self x hx, pow_two]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_one, vecMulVec_mul_vecMulVec, hx, one_smul]
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The full symbolic matrix subtraction, after projection reconstruction. -/
theorem projected_pointwise_identity [Nonempty n] (x : n → ℝ) (hx : x ⬝ᵥ x = 1) :
    ((Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2)) • projection (vecMulVec x x) ^ 2 -
      (2 * (Fintype.card n : ℝ)) • (∑ k, projection (vecMulVec (Pi.single k 1) x) ^ 2) =
      (((Fintype.card n : ℝ) - 2) / 2) •
        ((Fintype.card n : ℝ) • vecMulVec x x - 1) := by
  have hn : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [projection_outer_self_square x hx, projection_row_square_sum x hx]
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

end ShadowVerification.Frame
#print axioms ShadowVerification.Frame.projection_row
#print axioms ShadowVerification.Frame.projection_row_square
#print axioms ShadowVerification.Frame.coordinate_outer_sum
#print axioms ShadowVerification.Frame.weighted_row_sum
#print axioms ShadowVerification.Frame.projection_row_square_sum
#print axioms ShadowVerification.Frame.projection_outer_self
#print axioms ShadowVerification.Frame.projection_outer_self_square
#print axioms ShadowVerification.Frame.projected_pointwise_identity

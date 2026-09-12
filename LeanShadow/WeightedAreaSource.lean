import LeanShadow.PairedAreaVariation
import LeanShadow.WeightedMatrix

/-! # The positive weighted source for actual area derivatives

The contact matrix uses actual first and second area variations. Its
contraction and coercivity are derived from those variations, with no
stationarity assumption and no assumed contraction identity. Identification
with the complete coordinate PDE is a separate calculus step.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius
namespace ShadowVerification.WeightedSource
open _root_.ShadowVerification.Frame
open Paired Integrated Weighted Spherical

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]

noncomputable def contactMatrix (A B : Set (UnitSphere n)) (k rho : ℝ) :
    Matrix (FrobeniusIndex n) (FrobeniusIndex n) ℝ :=
  pairedMatrix mu A B k - rho • rankOne (actualFirst mu A)

noncomputable def contactGradient (A B : Set (UnitSphere n)) (k : ℝ) : Matrix n n ℝ :=
  k • actualMoment mu A - actualMoment mu B

/-- The rank-one chain-rule term contracts to the square of the actual moment. -/
theorem contact_contraction (A B : Set (UnitSphere n))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (k rho : ℝ) :
    manuscriptContraction (frame (frobeniusBasis (n := n))) (contactMatrix mu A B k rho) =
      (((Fintype.card n : ℝ) - 2) / 2) • contactGradient mu A B k +
      (-((Fintype.card n : ℝ) - 2) * k) • actualMoment mu A -
      rho • (actualMoment mu A ^ 2) := by
  rw [contactMatrix, manuscriptContraction_sub, manuscriptContraction_smul,
    manuscriptContraction_rankOne, actual_first_reconstruction mu A hA,
    paired_contraction mu A B hA hB]
  simp only [contactGradient, pow_two]
  abel

/-- The source estimate (6.7) for any two Borel sets, without stationarity. -/
theorem actual_source_lower_bound (A B : Set (UnitSphere n))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (k rho L : ℝ)
    (hrho : 0 ≤ rho) (hL : 0 ≤ L)
    (hcoefficient : 2 * rho ≤ ((Fintype.card n : ℝ) - 2) * L * k)
    (hsmall : L * ‖actualMoment mu A‖ ≤ 1 / 2) :
    rho / 2 * ‖actualMoment mu A‖ ^ 2 ≤
      (∑ i, ∑ j, contactMatrix mu A B k rho i j *
        weightCoefficients (frame (frobeniusBasis (n := n)))
          (1 - L • actualMoment mu A) i j) -
      (((Fintype.card n : ℝ) - 2) / 2) *
        (contactGradient mu A B k * (1 - L • actualMoment mu A)).trace := by
  apply contracted_source_lower_bound
    (frame (frobeniusBasis (n := n))) (contactMatrix mu A B k rho)
    (contactGradient mu A B k) (actualMoment mu A)
    (((Fintype.card n : ℝ) - 2) / 2) ((Fintype.card n : ℝ) - 2) k rho L
  · exact gradient_symmetric _
  · exact gradient_trace_zero _
  · exact hrho
  · exact hL
  · exact hcoefficient
  · exact hsmall
  · exact contact_contraction mu A B hA hB k rho

omit [Nonempty n] [MeasurableSpace (EuclideanSpace ℝ n)]
    [BorelSpace (EuclideanSpace ℝ n)] in
/-- The actual constructed frame has the Euclidean coefficient norm. -/
theorem frame_sum_norm_sq (v : FrobeniusIndex n → ℝ) :
    ‖∑ i, v i • frame (frobeniusBasis (n := n)) i‖ ^ 2 = ∑ i, v i ^ 2 := by
  let H := frame (frobeniusBasis (n := n))
  have hnorm (M : Matrix n n ℝ) : ‖M‖ ^ 2 = pairing M M := by
    rw [frobenius_sq]
    simp only [pairing, pow_two]
  have horth : ∀ i j, pairing (H i) (H j) = if i = j then 1 else 0 :=
    by
      intro i j
      have h := frobeniusBasis_orthonormal (n := n)
      unfold Frame.IsOrthonormal at h
      by_cases hij : i = j
      · simpa only [if_pos hij, H] using h i j
      · simpa only [if_neg hij, H] using h i j
  have hp (i : FrobeniusIndex n) : pairing (∑ j, v j • H j) (H i) = v i := by
    rw [pairing_comm, pairing_sum_right]
    simp [pairing_smul_right, horth]
  change ‖∑ i, v i • H i‖ ^ 2 = _
  rw [hnorm, pairing_sum_right]
  simp only [pairing_smul_right, hp, pow_two]

omit [Nonempty n] [BorelSpace (EuclideanSpace ℝ n)] [mu.IsAddHaarMeasure] in
/-- Uniform ellipticity in symmetric frame coordinates has explicit constant 1/2. -/
theorem actual_weight_lower_bound (A : Set (UnitSphere n)) (L : ℝ)
    (hL : 0 ≤ L) (hsmall : L * ‖actualMoment mu A‖ ≤ 1 / 2)
    (v : FrobeniusIndex n → ℝ) :
    (1 / 2 : ℝ) * (∑ i, v i ^ 2) ≤
      v ⬝ᵥ (weightCoefficients (frame (frobeniusBasis (n := n)))
        (1 - L • actualMoment mu A) *ᵥ v) := by
  have h := weightCoefficients_lower_bound (frame (frobeniusBasis (n := n)))
    (fun i => (frobeniusBasis i).property.1) (actualMoment mu A) L hL hsmall v
  rwa [frame_sum_norm_sq] at h

omit [Nonempty n] [BorelSpace (EuclideanSpace ℝ n)] [mu.IsAddHaarMeasure] in
/-- The coefficient matrix is positive semidefinite for the geometric weight. -/
theorem actual_weight_posSemidef (A : Set (UnitSphere n)) (L : ℝ)
    (hL : 0 ≤ L) (hsmall : L * ‖actualMoment mu A‖ ≤ 1 / 2) :
    (weightCoefficients (frame (frobeniusBasis (n := n)))
      (1 - L • actualMoment mu A)).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · simpa using weightCoefficients_symm (frame (frobeniusBasis (n := n)))
      (1 - L • actualMoment mu A)
  · intro v
    have h := actual_weight_lower_bound mu A L hL hsmall v
    simpa only [star_trivial] using
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (Finset.sum_nonneg fun i _ => sq_nonneg (v i))).trans h

end ShadowVerification.WeightedSource
#print axioms ShadowVerification.WeightedSource.contact_contraction
#print axioms ShadowVerification.WeightedSource.actual_source_lower_bound
#print axioms ShadowVerification.WeightedSource.frame_sum_norm_sq
#print axioms ShadowVerification.WeightedSource.actual_weight_lower_bound
#print axioms ShadowVerification.WeightedSource.actual_weight_posSemidef

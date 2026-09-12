import LeanShadow.AreaContraction
import LeanShadow.FrobeniusBasis

/-! # Actual area matrices in a constructed frame, and the paired implication

The frame is now constructed, and every matrix entry comes from derivatives
of actual image measures. For two sets, first-variation stationarity implies
the moment relation and the precise contraction used by the manuscript.
Stationarity and the second-variation inequality remain explicit hypotheses;
this file does not assert that an optimizer supplies them.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open Matrix MeasureTheory Set
namespace ShadowVerification.Paired
open Spherical Integrated AreaContraction
open _root_.ShadowVerification.Frame

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]

noncomputable def actualMatrix (A : Set (UnitSphere n)) :
    Matrix (FrobeniusIndex n) (FrobeniusIndex n) ℝ :=
  polarizedAreaMatrix mu A (frame (frobeniusBasis (n := n)))

noncomputable def actualFirst (A : Set (UnitSphere n)) : FrobeniusIndex n → ℝ :=
  fun i => firstArea mu A (frame (frobeniusBasis (n := n)) i)

noncomputable def actualMoment (A : Set (UnitSphere n)) : Matrix n n ℝ :=
  gradientMatrix ((probability mu).restrict A)

theorem actual_contraction (A : Set (UnitSphere n)) (hA : MeasurableSet A) :
    manuscriptContraction (frame (frobeniusBasis (n := n))) (actualMatrix mu A) =
      (-((Fintype.card n : ℝ) - 2) / 2) • actualMoment mu A :=
  area_contraction mu A hA frobeniusBasis frobeniusBasis_orthonormal

theorem actual_trace_zero (A : Set (UnitSphere n)) (hA : MeasurableSet A) :
    (actualMatrix mu A).trace = 0 :=
  area_trace_zero mu A hA frobeniusBasis frobeniusBasis_orthonormal

theorem actual_first_reconstruction (A : Set (UnitSphere n)) (hA : MeasurableSet A) :
    (∑ i, actualFirst mu A i • frame (frobeniusBasis (n := n)) i) = actualMoment mu A :=
  firstArea_reconstruction mu A hA frobeniusBasis frobeniusBasis_orthonormal

noncomputable def pairedMatrix (A B : Set (UnitSphere n)) (k : ℝ) :
    Matrix (FrobeniusIndex n) (FrobeniusIndex n) ℝ :=
  actualMatrix mu B + k • actualMatrix mu A

/-- The identity also records the first-variation defect away from stationarity. -/
theorem paired_contraction (A B : Set (UnitSphere n)) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (k : ℝ) :
    manuscriptContraction (frame (frobeniusBasis (n := n))) (pairedMatrix mu A B k) =
      (-((Fintype.card n : ℝ) - 2) * k) • actualMoment mu A +
      (((Fintype.card n : ℝ) - 2) / 2) • (k • actualMoment mu A - actualMoment mu B) := by
  have hadd := (MatrixIntegral.contractionLinear (frame (frobeniusBasis (n := n)))).map_add
    (actualMatrix mu B) (k • actualMatrix mu A)
  dsimp only [MatrixIntegral.contractionLinear, LinearMap.coe_mk, AddHom.coe_mk] at hadd
  change manuscriptContraction _ (_ + _) = _
  rw [hadd, manuscriptContraction_smul, actual_contraction mu A hA, actual_contraction mu B hB]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The stationarity equations for opposing projective directions imply the
exact relation between the two actual moment matrices. -/
theorem stationary_moments (A B : Set (UnitSphere n)) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (k : ℝ)
    (hstationary : ∀ i, actualFirst mu B i = k * actualFirst mu A i) :
    actualMoment mu B = k • actualMoment mu A := by
  rw [← actual_first_reconstruction mu B hB, ← actual_first_reconstruction mu A hA,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hstationary, smul_smul]

theorem paired_contraction_stationary (A B : Set (UnitSphere n)) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (k : ℝ)
    (hstationary : ∀ i, actualFirst mu B i = k * actualFirst mu A i) :
    manuscriptContraction (frame (frobeniusBasis (n := n))) (pairedMatrix mu A B k) =
      (-((Fintype.card n : ℝ) - 2) * k) • actualMoment mu A := by
  rw [paired_contraction mu A B hA hB k, stationary_moments mu A B hA hB k hstationary,
    sub_self, smul_zero, add_zero]

/-- The algebraic matrix bound now uses actual area derivatives and moments.
Only stationarity and the second-variation order are assumed here. -/
theorem actual_variation_bound (A B : Set (UnitSphere n)) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (k rho : ℝ)
    (hstationary : ∀ i, actualFirst mu B i = k * actualFirst mu A i)
    (hvariation : (rho • rankOne (actualFirst mu A) - pairedMatrix mu A B k).PosSemidef) :
    (rho • (actualMoment mu A * actualMoment mu A) +
      (((Fintype.card n : ℝ) - 2) * k) • actualMoment mu A).PosSemidef := by
  apply contracted_variation_bound (frame (frobeniusBasis (n := n))) (pairedMatrix mu A B k)
    (actualFirst mu A) (actualMoment mu A) rho (((Fintype.card n : ℝ) - 2) * k)
  · exact fun i => (frobeniusBasis i).property.1
  · exact actual_first_reconstruction mu A hA
  · exact hvariation
  · simpa only [neg_mul] using paired_contraction_stationary mu A B hA hB k hstationary

end ShadowVerification.Paired
#print axioms ShadowVerification.Paired.actual_contraction
#print axioms ShadowVerification.Paired.actual_trace_zero
#print axioms ShadowVerification.Paired.actual_first_reconstruction
#print axioms ShadowVerification.Paired.paired_contraction
#print axioms ShadowVerification.Paired.stationary_moments
#print axioms ShadowVerification.Paired.paired_contraction_stationary
#print axioms ShadowVerification.Paired.actual_variation_bound

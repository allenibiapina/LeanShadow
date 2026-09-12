import LeanShadow.OptimizerVariation
import LeanShadow.ProfileRegularity
import LeanShadow.SpectralStep

/-! # Almost-everywhere optimizer variation and spectral curvature bounds

Block 2 supplies the Peano expansion and positive slope; attainment supplies
the optimizer; the compression argument supplies its nonzero moment. Block 3
now derives the actual matrix inequality and its negative-eigenvalue bound.
Only the sharp cap Rayleigh bound remains an input to the cap comparison.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set MeasureTheory Filter
open scoped Topology BigOperators
namespace ShadowVerification.ProfileVariations
open Spherical Profile ProfileSupport Paired Integrated RightSlopeTaylor OptimizerVariation

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]
  (hdim : 2 < Module.finrank ℝ (EuclideanSpace ℝ n))

include hdim

theorem optimizer_spectral_bound (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (A : Set (UnitSphere n)) (hA : IsOptimizer mu p A) (k rho : ℝ)
    (hexp : HasQuadraticExpansion (profile mu) p k rho) (hk : 0 < k) :
    ∃ (d : ℝ) (z : n → ℝ), 0 < d ∧ z ⬝ᵥ z = 1 ∧
      actualMoment mu A *ᵥ z = (-d) • z ∧
      ((Fintype.card n : ℝ) - 2) * k / d ≤ rho := by
  have hn : (2 : ℝ) < Fintype.card n := by
    have h : 2 < Fintype.card n := by simpa using hdim
    exact_mod_cast h
  have hne := OptimizerCompression.optimizer_nonisotropic mu p A hA k rho hexp hk hn hp.1 hp.2
  obtain ⟨d,z,hd,hz,heigen⟩ := exists_unit_negative_eigenvector (actualMoment mu A)
    (Integrated.gradient_symmetric _) (Integrated.gradient_trace_zero _) hne
  exact ⟨d,z,hd,hz,heigen,matrix_negative_eigenvalue_bound _ z rho
    (((Fintype.card n : ℝ) - 2) * k) d hd hz heigen
    (optimizer_matrix_bound mu p A hA k rho hexp)⟩

/-- The precise remaining interface for the sharp moment calculation. -/
theorem optimizer_curvature_bound_of_rayleigh (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (A : Set (UnitSphere n)) (hA : IsOptimizer mu p A) (k rho D : ℝ)
    (hexp : HasQuadraticExpansion (profile mu) p k rho) (hk : 0 < k)
    (hRayleigh : ∀ z : n → ℝ, z ⬝ᵥ z = 1 → -D ≤ z ⬝ᵥ (actualMoment mu A *ᵥ z)) :
    ((Fintype.card n : ℝ) - 2) * k / D ≤ rho := by
  obtain ⟨d,z,hd,hz,heigen,hbound⟩ := optimizer_spectral_bound mu hdim p hp A hA k rho hexp hk
  have hn : (2 : ℝ) ≤ Fintype.card n := by
    have h : 2 ≤ Fintype.card n := by simpa using hdim.le
    exact_mod_cast h
  exact moment_bound_transfer rho (((Fintype.card n : ℝ) - 2) * k) d D
    (mul_nonneg (sub_nonneg.mpr hn) hk.le) hd
    (rayleigh_bound_for_negative_eigenvalue _ z d D hz heigen hRayleigh) hbound

/-- Existence and all variational conclusions hold on one full-measure set
of interior masses, simultaneously for every optimizer at that mass. -/
theorem ae_optimizer_variations :
    ∀ᵐ p : ℝ, p ∈ Ioo (0 : ℝ) 1 →
      (∃ A : Set (UnitSphere n), IsOptimizer mu p A) ∧
      ∀ A : Set (UnitSphere n), IsOptimizer mu p A →
        (∀ i, actualFirst mu (avoidingPartner mu A) i =
          rightSlope (profile mu) p * actualFirst mu A i) ∧
        actualMoment mu (avoidingPartner mu A) = rightSlope (profile mu) p • actualMoment mu A ∧
        ((-deriv (rightSlope (profile mu)) p) • rankOne (actualFirst mu A) -
          pairedMatrix mu A (avoidingPartner mu A) (rightSlope (profile mu) p)).PosSemidef ∧
        ((-deriv (rightSlope (profile mu)) p) • (actualMoment mu A * actualMoment mu A) +
          (((Fintype.card n : ℝ) - 2) * rightSlope (profile mu) p) • actualMoment mu A).PosSemidef ∧
        actualMoment mu A ≠ 0 := by
  filter_upwards [ProfileRegularity.ae_positive_quadratic_expansion mu hdim,
    ProfileRegularity.ae_optimizer_nonisotropic mu hdim] with p hp hn hpin
  refine ⟨(hn hpin).1,fun A hA => ?_⟩
  have hpair := optimalPair_of_optimizer mu p A hA
  have hexp := (hp hpin).2.2.2
  exact ⟨pair_stationarity mu p A _ hpair _ _ hexp,
    pair_moment_stationarity mu p A _ hpair _ _ hexp,
    pair_second_variation mu p A _ hpair _ _ hexp,
    optimizer_matrix_bound mu p A hA _ _ hexp,(hn hpin).2 A hA⟩

theorem ae_optimizer_spectral_bound :
    ∀ᵐ p : ℝ, p ∈ Ioo (0 : ℝ) 1 →
      (∃ A : Set (UnitSphere n), IsOptimizer mu p A) ∧
      ∀ A : Set (UnitSphere n), IsOptimizer mu p A →
        ∃ (d : ℝ) (z : n → ℝ), 0 < d ∧ z ⬝ᵥ z = 1 ∧
          actualMoment mu A *ᵥ z = (-d) • z ∧
          ((Fintype.card n : ℝ) - 2) * rightSlope (profile mu) p / d ≤
            -deriv (rightSlope (profile mu)) p := by
  filter_upwards [ProfileRegularity.ae_positive_quadratic_expansion mu hdim,
    ProfileRegularity.ae_optimizer_nonisotropic mu hdim] with p hp hn hpin
  refine ⟨(hn hpin).1,fun A hA => ?_⟩
  exact optimizer_spectral_bound mu hdim p hpin A hA _ _ (hp hpin).2.2.2 (hp hpin).1

/-- Strict negativity is an a.e. density statement. It does not discard
the singular part of the BV derivative needed in the later comparison. -/
theorem ae_rightSlope_deriv_neg :
    ∀ᵐ p : ℝ, p ∈ Ioo (0 : ℝ) 1 → deriv (rightSlope (profile mu)) p < 0 := by
  filter_upwards [ae_optimizer_spectral_bound mu hdim] with p hp hpin
  obtain ⟨A,hA⟩ := (hp hpin).1
  obtain ⟨d,z,hd,_,_,hbound⟩ := (hp hpin).2 A hA
  have hn : (2 : ℝ) < Fintype.card n := by
    have h : 2 < Fintype.card n := by simpa using hdim
    exact_mod_cast h
  have hpos := div_pos (mul_pos (sub_pos.mpr hn)
    (ProfileRegularity.rightSlope_pos mu hdim p hpin)) hd
  linarith

end ShadowVerification.ProfileVariations
#print axioms ShadowVerification.ProfileVariations.optimizer_spectral_bound
#print axioms ShadowVerification.ProfileVariations.optimizer_curvature_bound_of_rayleigh
#print axioms ShadowVerification.ProfileVariations.ae_optimizer_variations
#print axioms ShadowVerification.ProfileVariations.ae_optimizer_spectral_bound
#print axioms ShadowVerification.ProfileVariations.ae_rightSlope_deriv_neg

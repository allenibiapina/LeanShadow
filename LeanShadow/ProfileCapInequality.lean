import LeanShadow.CapRayleigh
import LeanShadow.CapModel
import LeanShadow.CapShadow
import LeanShadow.ProfileVariations

/-! # The sharp almost-everywhere differential inequality for the actual profile

The cap bound is proved here for the actual spherical moment, and is no
longer an input. This is an a.e. density statement; the BV singular part
and the resulting global comparison are the next block.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology BigOperators
namespace ShadowVerification.ProfileCapInequality
open Spherical Profile ProfileSupport Integrated Paired RightSlopeTaylor
open CapFunctions CapRadius CapModel CapRayleigh

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]

omit [DecidableEq n] in
theorem profile_le_model (hd : 1 < Module.finrank ℝ (EuclideanSpace ℝ n))
    (a : UnitSphere n) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    profile mu p ≤ model (Fintype.card n - 2) p := by
  have h := CapShadow.profile_le_cap mu hd a (radius (Fintype.card n - 2) p)
    (radius_mem (Fintype.card n - 2) p)
  simpa only [model,finrank_euclideanSpace,mass_radius _ p hp] using h

theorem moment_bound_at_mass (hd : 1 < Module.finrank ℝ (EuclideanSpace ℝ n))
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (A : Set (UnitSphere n)) (hA : MeasurableSet A)
    (hmass : area mu A = p) (z : n → ℝ) (hz : z ⬝ᵥ z = 1) :
    -bound (Fintype.card n - 2) p ≤ z ⬝ᵥ (actualMoment mu A *ᵥ z) :=
  sharp_rayleigh mu hd (radius (Fintype.card n - 2) p) (radius_mem _ p) A hA
    (hmass.trans (mass_radius _ p hp).symm) z hz

theorem optimizer_curvature_bound (hdim : 2 < Module.finrank ℝ (EuclideanSpace ℝ n))
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) (A : Set (UnitSphere n)) (hA : IsOptimizer mu p A)
    (k rho : ℝ) (hexp : HasQuadraticExpansion (profile mu) p k rho) (hk : 0 < k) :
    ((Fintype.card n : ℝ) - 2) * k / bound (Fintype.card n - 2) p ≤ rho := by
  apply ProfileVariations.optimizer_curvature_bound_of_rayleigh mu hdim p hp A hA k rho _ hexp hk
  exact moment_bound_at_mass mu (by omega) p ⟨hp.1.le,hp.2.le⟩ A hA.measurable hA.mass

theorem ae_profile_inequality (hdim : 2 < Module.finrank ℝ (EuclideanSpace ℝ n)) :
    ∀ᵐ p : ℝ, p ∈ Ioo (0 : ℝ) 1 →
      deriv (rightSlope (profile mu)) p +
        ((Fintype.card n : ℝ) - 2) * rightSlope (profile mu) p /
          bound (Fintype.card n - 2) p ≤ 0 := by
  filter_upwards [ProfileRegularity.ae_positive_quadratic_expansion mu hdim,
    ProfileRegularity.ae_optimizer_nonisotropic mu hdim] with p hp ha hpin
  obtain ⟨A,hA⟩ := (ha hpin).1
  have h := optimizer_curvature_bound mu hdim p hpin A hA _ _ (hp hpin).2.2.2 (hp hpin).1
  linarith

theorem ae_profile_model_inequality (hdim : 2 < Module.finrank ℝ (EuclideanSpace ℝ n)) :
    ∀ᵐ p : ℝ, p ∈ Ioo (0 : ℝ) 1 →
      deriv (rightSlope (profile mu)) p -
        (deriv (deriv (model (Fintype.card n - 2))) p / deriv (model (Fintype.card n - 2)) p) *
          rightSlope (profile mu) p ≤ 0 := by
  filter_upwards [ae_profile_inequality mu hdim] with p hp hpin
  rw [model_ode _ p hpin]
  have hn : 2 ≤ Fintype.card n := by simpa using hdim.le
  rw [Nat.cast_sub hn,Nat.cast_ofNat]
  convert hp hpin using 1
  ring

end ShadowVerification.ProfileCapInequality
#print axioms ShadowVerification.ProfileCapInequality.profile_le_model
#print axioms ShadowVerification.ProfileCapInequality.moment_bound_at_mass
#print axioms ShadowVerification.ProfileCapInequality.optimizer_curvature_bound
#print axioms ShadowVerification.ProfileCapInequality.ae_profile_inequality
#print axioms ShadowVerification.ProfileCapInequality.ae_profile_model_inequality

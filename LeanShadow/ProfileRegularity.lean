import LeanShadow.ProfileEndpoints
import LeanShadow.RightSlopeTaylor
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-! # Block 2: regularity of the actual optimal shadow profile

All statements refer to Profile.profile, the unchanged infimum over Borel
antipodal sets and literal-shadow outer measures. Concavity, continuity,
positive right slope, local bounded variation, and almost-everywhere Peano
expansions are conclusions. The last theorem supplies nonisotropy at almost
every interior mass to the next variational block.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace ShadowVerification.ProfileRegularity
open Spherical Profile RightSlopeTaylor ProfileEndpoints

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]
  (hd : 2 < Module.finrank ℝ (EuclideanSpace ℝ n))

include hd

theorem continuous : ContinuousOn (profile mu) (Icc 0 1) := by
  intro p hp
  by_cases hp0 : p = 0
  · rw [hp0]
    exact continuous_zero mu (by omega)
  by_cases hp1 : p = 1
  · rw [hp1]
    exact continuous_one mu (by omega)
  have hin : p ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0),lt_of_le_of_ne hp.2 hp1⟩
  exact ((ProfileConcavity.continuous_interior mu hd).continuousAt (isOpen_Ioo.mem_nhds hin)).continuousWithinAt

theorem rightSlope_lower_bound (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    (1 - profile mu p) / (1-p) ≤ rightSlope (profile mu) p := by
  have h := (ProfileConcavity.concave mu hd).slope_le_of_hasDerivWithinAt_Ioi
    (show p ∈ Icc (0 : ℝ) 1 from ⟨hp.1.le,hp.2.le⟩) (right_mem_Icc.mpr zero_le_one) hp.2
    (rightSlope_hasDeriv (profile mu) 0 1 (ProfileConcavity.concave mu hd) p hp)
  simpa only [slope_def_field,profile_one mu (by omega)] using h

theorem rightSlope_pos (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) : 0 < rightSlope (profile mu) p := by
  have hlt := SmallShadowCaps.profile_lt_one mu (by omega) p hp.1.le hp.2
  exact (div_pos (sub_pos.mpr hlt) (sub_pos.mpr hp.2)).trans_le (rightSlope_lower_bound mu hd p hp)

theorem rightSlope_eq_right_deriv (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    rightSlope (profile mu) p = derivWithin (profile mu) (Ioi p) p :=
  (rightSlope_hasDeriv (profile mu) 0 1 (ProfileConcavity.concave mu hd) p hp).derivWithin
    (uniqueDiffWithinAt_Ioi p) |>.symm

theorem rightSlope_locallyBV : LocallyBoundedVariationOn (rightSlope (profile mu)) (Ioo 0 1) := by
  have h := (rightSlope_antitone (profile mu) 0 1 (ProfileConcavity.concave mu hd)).neg.locallyBoundedVariationOn
  have hn : LipschitzWith 1 (fun x : ℝ => -x) := isometry_neg.lipschitz
  simpa only [Function.comp_def,Pi.neg_apply,neg_neg] using hn.comp_locallyBoundedVariationOn h

theorem curvature_nonneg (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 ≤ -deriv (rightSlope (profile mu)) p := by
  have h := (rightSlope_antitone (profile mu) 0 1 (ProfileConcavity.concave mu hd)).derivWithin_nonpos (x := p)
  rw [derivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hp)] at h
  linarith

theorem ae_positive_quadratic_expansion :
    ∀ᵐ p : ℝ, p ∈ Ioo (0 : ℝ) 1 →
      0 < rightSlope (profile mu) p ∧ 0 ≤ -deriv (rightSlope (profile mu)) p ∧
      HasDerivAt (profile mu) (rightSlope (profile mu) p) p ∧
      ProfileSupport.HasQuadraticExpansion (profile mu) p (rightSlope (profile mu) p)
        (-deriv (rightSlope (profile mu)) p) := by
  filter_upwards [ae_quadratic_expansion (profile mu) 0 1 (ProfileConcavity.concave mu hd)] with p hp hpin
  exact ⟨rightSlope_pos mu hd p hpin,curvature_nonneg mu hd p hpin,
    expansion_hasDerivAt _ _ _ _ (hp hpin),hp hpin⟩

theorem ae_deriv_eq_rightSlope :
    ∀ᵐ p : ℝ, p ∈ Ioo (0 : ℝ) 1 → deriv (profile mu) p = rightSlope (profile mu) p := by
  filter_upwards [ae_positive_quadratic_expansion mu hd] with p hp hpin
  exact (hp hpin).2.2.1.deriv

theorem ae_optimizer_nonisotropic :
    ∀ᵐ p : ℝ, p ∈ Ioo (0 : ℝ) 1 →
      (∃ A : Set (Sphere (EuclideanSpace ℝ n)), IsOptimizer mu p A) ∧
      ∀ A : Set (Sphere (EuclideanSpace ℝ n)), IsOptimizer mu p A → Paired.actualMoment mu A ≠ 0 := by
  filter_upwards [ae_positive_quadratic_expansion mu hd] with p hp hpin
  obtain ⟨A,_,_,hA⟩ := IncidenceAttainment.exists_optimizer mu hd p hpin.1.le hpin.2.le
  refine ⟨⟨A,hA⟩,fun B hB => ?_⟩
  have hn : (2 : ℝ) < Fintype.card n := by
    have h : 2 < Fintype.card n := by simpa using hd
    exact_mod_cast h
  exact OptimizerCompression.optimizer_nonisotropic mu p B hB
    (rightSlope (profile mu) p) (-deriv (rightSlope (profile mu)) p)
    (hp hpin).2.2.2 (hp hpin).1 hn hpin.1 hpin.2

end ShadowVerification.ProfileRegularity
#print axioms ShadowVerification.ProfileRegularity.continuous
#print axioms ShadowVerification.ProfileRegularity.rightSlope_lower_bound
#print axioms ShadowVerification.ProfileRegularity.rightSlope_pos
#print axioms ShadowVerification.ProfileRegularity.rightSlope_eq_right_deriv
#print axioms ShadowVerification.ProfileRegularity.rightSlope_locallyBV
#print axioms ShadowVerification.ProfileRegularity.curvature_nonneg
#print axioms ShadowVerification.ProfileRegularity.ae_positive_quadratic_expansion
#print axioms ShadowVerification.ProfileRegularity.ae_deriv_eq_rightSlope
#print axioms ShadowVerification.ProfileRegularity.ae_optimizer_nonisotropic

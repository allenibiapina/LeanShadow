import LeanShadow.BVLogComparison
import LeanShadow.RatioSupport
import LeanShadow.ProfileCapInequality

/-! # Block 5: equality of the actual optimal profile with the cap model

Ordinary concavity controls singular variation; the sharp a.e. inequality
controls the density. The logarithmic Stieltjes comparison proves monotonicity
of the actual right-slope ratio. Supporting lines and endpoint continuity
give the global lower bound, and actual cap competitors give equality.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ShadowVerification.SharpProfile
open Spherical Profile Integrated RightSlopeTaylor CapModel

theorem model_strictMono (m : ℕ) : StrictMonoOn (model m) (Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (model_continuous m).continuousOn
  intro p hp
  rw [interior_Icc] at hp
  rw [model_deriv m p hp]
  exact slope_pos m p hp

theorem model_mem (m : ℕ) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) : model m p ∈ Icc (0 : ℝ) 1 := by
  constructor
  · simpa only [model_zero] using (model_strictMono m).monotoneOn ⟨le_rfl,zero_le_one⟩ hp hp.1
  · simpa only [model_one] using (model_strictMono m).monotoneOn hp ⟨zero_le_one,le_rfl⟩ hp.2

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]
  (hdim : 2 < Module.finrank ℝ (EuclideanSpace ℝ n))

include hdim

theorem rightSlope_ratio_antitone :
    AntitoneOn (fun p => rightSlope (profile mu) p / CapModel.slope (Fintype.card n - 2) p)
      (Ioo (0 : ℝ) 1) := by
  apply BVLogComparison.ratio_antitone (rightSlope (profile mu)) (CapModel.slope (Fintype.card n - 2))
    (fun p => -((Fintype.card n - 2 : ℕ) : ℝ) * CapModel.slope (Fintype.card n - 2) p /
      bound (Fintype.card n - 2) p) 0 1
    (rightSlope_antitone (profile mu) 0 1 (ProfileConcavity.concave mu hdim))
    (ProfileRegularity.rightSlope_pos mu hdim) (slope_pos _) (slope_hasDeriv _)
  · exact (continuousOn_const.mul (slope_continuousOn _)).div (bound_continuous _).continuousOn
      (fun p hp => (bound_pos _ p hp).ne')
  · filter_upwards [ProfileCapInequality.ae_profile_model_inequality mu hdim] with p hp hpin
    simpa only [(second_hasDeriv _ p hpin).deriv,model_deriv _ p hpin] using hp hpin

theorem model_le_profile (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    model (Fintype.card n - 2) p ≤ profile mu p := by
  by_cases h0 : p = 0
  · rw [h0,model_zero,ProfileConcavity.profile_zero mu]
  by_cases h1 : p = 1
  · rw [h1,model_one,ProfileEndpoints.profile_one mu (by omega)]
  have hpin : p ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hp.1 (Ne.symm h0),lt_of_le_of_ne hp.2 h1⟩
  exact RatioSupport.endpoint_chord (profile mu) (model (Fintype.card n - 2)) (rightSlope (profile mu))
    (CapModel.slope (Fintype.card n - 2)) (ProfileRegularity.continuous mu hdim)
    (model_continuous _).continuousOn
    (rightSlope_hasDeriv (profile mu) 0 1 (ProfileConcavity.concave mu hdim))
    (model_hasDeriv _) (slope_pos _) (rightSlope_ratio_antitone mu hdim)
    (ProfileConcavity.profile_zero mu) (ProfileEndpoints.profile_one mu (by omega))
    (model_zero _) (model_one _) p hpin (model_mem _ p hp)

theorem profile_eq_model (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    profile mu p = model (Fintype.card n - 2) p := by
  obtain ⟨a,ha⟩ : (Sphere (EuclideanSpace ℝ n)).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  exact le_antisymm (ProfileCapInequality.profile_le_model mu (by omega) ⟨a,ha⟩ p hp)
    (model_le_profile mu hdim p hp)

/-- Equality holds on a neighborhood of each interior mass. -/
theorem profile_eventuallyEq_model (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profile mu =ᶠ[𝓝 p] model (Fintype.card n - 2) := by
  filter_upwards [isOpen_Ioo.mem_nhds hp] with q hq
  exact profile_eq_model mu hdim q ⟨hq.1.le,hq.2.le⟩

theorem profile_hasDeriv (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (profile mu) (CapModel.slope (Fintype.card n - 2) p) p :=
  (model_hasDeriv _ p hp).congr_of_eventuallyEq (profile_eventuallyEq_model mu hdim p hp)

theorem rightSlope_eq_modelSlope (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    rightSlope (profile mu) p = CapModel.slope (Fintype.card n - 2) p := by
  have h1 := (rightSlope_hasDeriv (profile mu) 0 1 (ProfileConcavity.concave mu hdim) p hp).derivWithin
    (uniqueDiffWithinAt_Ioi p)
  have h2 := (profile_hasDeriv mu hdim p hp).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi p)
  exact h1.symm.trans h2

theorem rightSlope_ratio_one (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    rightSlope (profile mu) p / CapModel.slope (Fintype.card n - 2) p = 1 := by
  rw [rightSlope_eq_modelSlope mu hdim p hp]
  exact div_self (slope_pos _ p hp).ne'

theorem profile_contDiffOn_two : ContDiffOn ℝ 2 (profile mu) (Ioo (0 : ℝ) 1) :=
  (model_contDiffOn_two (Fintype.card n - 2)).congr
    (fun p hp => profile_eq_model mu hdim p ⟨hp.1.le,hp.2.le⟩)

theorem profile_quadratic_expansion (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    ProfileSupport.HasQuadraticExpansion (profile mu) p (CapModel.slope (Fintype.card n - 2) p)
      (((Fintype.card n - 2 : ℕ) : ℝ) * CapModel.slope (Fintype.card n - 2) p /
        bound (Fintype.card n - 2) p) := by
  have h := expansion_of_right_derivative (profile mu) (CapModel.slope (Fintype.card n - 2)) 0 1 p
    (-((Fintype.card n - 2 : ℕ) : ℝ) * CapModel.slope (Fintype.card n - 2) p /
      bound (Fintype.card n - 2) p) hp
    ((ProfileRegularity.continuous mu hdim).mono Ioo_subset_Icc_self)
    (fun q hq => (profile_hasDeriv mu hdim q hq).hasDerivWithinAt) (slope_hasDeriv _ p hp)
  simpa only [neg_mul,neg_div,neg_neg] using h

omit [DecidableEq n] [Nonempty n] [MeasurableSpace (EuclideanSpace ℝ n)]
  [BorelSpace (EuclideanSpace ℝ n)] in
theorem curvature_pos (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 < ((Fintype.card n - 2 : ℕ) : ℝ) * CapModel.slope (Fintype.card n - 2) p /
      bound (Fintype.card n - 2) p := by
  have hn : 0 < Fintype.card n - 2 := by
    have hd : 2 < Fintype.card n := by simpa using hdim
    omega
  exact div_pos (mul_pos (Nat.cast_pos.mpr hn) (slope_pos _ p hp)) (bound_pos _ p hp)

end ShadowVerification.SharpProfile
#print axioms ShadowVerification.SharpProfile.model_strictMono
#print axioms ShadowVerification.SharpProfile.model_mem
#print axioms ShadowVerification.SharpProfile.rightSlope_ratio_antitone
#print axioms ShadowVerification.SharpProfile.model_le_profile
#print axioms ShadowVerification.SharpProfile.profile_eq_model

#print axioms ShadowVerification.SharpProfile.profile_eventuallyEq_model
#print axioms ShadowVerification.SharpProfile.profile_hasDeriv
#print axioms ShadowVerification.SharpProfile.rightSlope_eq_modelSlope
#print axioms ShadowVerification.SharpProfile.rightSlope_ratio_one
#print axioms ShadowVerification.SharpProfile.profile_contDiffOn_two
#print axioms ShadowVerification.SharpProfile.profile_quadratic_expansion
#print axioms ShadowVerification.SharpProfile.curvature_pos

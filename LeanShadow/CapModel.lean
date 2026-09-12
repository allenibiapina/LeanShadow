import LeanShadow.CapRadius
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # The model cap profile and its exact differential equation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Real
open scoped Topology ContDiff
namespace ShadowVerification.CapModel
open CapFunctions CapRadius

def model (m : ℕ) (p : ℝ) : ℝ := beltMass m (radius m p)
def angularSlope (m : ℕ) (r : ℝ) : ℝ := (Real.cos r / Real.sin r) ^ m
def slope (m : ℕ) (p : ℝ) : ℝ := angularSlope m (radius m p)
def bound (m : ℕ) (p : ℝ) : ℝ := momentBound m (radius m p)

theorem model_continuous (m : ℕ) : Continuous (model m) :=
  (beltMass_continuous m).comp (radius_continuous m)

theorem model_zero (m : ℕ) : model m 0 = 0 := by simp only [model,radius_zero,beltMass_zero]
theorem model_one (m : ℕ) : model m 1 = 1 := by simp only [model,radius_one,beltMass_half_pi]

theorem model_mass (m : ℕ) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) :
    model m (capMass m r) = beltMass m r := by rw [model,radius_mass m r hr]

theorem bound_mass (m : ℕ) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) :
    bound m (capMass m r) = momentBound m r := by rw [bound,radius_mass m r hr]

theorem slope_pos (m : ℕ) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) : 0 < slope m p :=
  pow_pos (div_pos (radius_cos_pos m p hp) (radius_sin_pos m p hp)) m

theorem bound_pos (m : ℕ) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) : 0 < bound m p :=
  momentBound_pos m (radius m p) (radius_interior m p hp)

theorem bound_continuous (m : ℕ) : Continuous (bound m) := by
  unfold bound momentBound
  exact ((continuous_const.mul (Real.continuous_cos.comp (radius_continuous m))).mul
    ((Real.continuous_sin.comp (radius_continuous m)).pow (m+1)))

theorem model_hasDeriv (m : ℕ) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (model m) (slope m p) p := by
  have h := (beltMass_hasDeriv m (radius m p)).comp p (radius_hasDeriv m p hp)
  apply h.congr_deriv
  dsimp only [slope,angularSlope]
  rw [div_pow]
  field_simp [(normalizer_pos m).ne', (radius_sin_pos m p hp).ne']

theorem angularSlope_hasDeriv (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) (Real.pi/2)) :
    HasDerivAt (angularSlope m) (-(m : ℝ) * angularSlope m r / (Real.sin r * Real.cos r)) r := by
  have hs : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr.1 (by linarith [hr.2,Real.pi_pos])
  have hc : 0 < Real.cos r := Real.cos_pos_of_mem_Ioo ⟨by linarith [hr.1,Real.pi_pos],hr.2⟩
  have hcot : HasDerivAt (fun t => Real.cos t / Real.sin t) (-1 / Real.sin r ^ 2) r := by
    apply ((Real.hasDerivAt_cos r).div (Real.hasDerivAt_sin r) hs.ne').congr_deriv
    congr 1
    nlinarith [Real.sin_sq_add_cos_sq r]
  have h := hcot.pow m
  apply h.congr_deriv
  cases m with
  | zero => simp [angularSlope]
  | succ k =>
    simp only [angularSlope,Nat.cast_succ,Nat.add_sub_cancel,pow_succ]
    field_simp [hs.ne',hc.ne']

theorem slope_hasDeriv (m : ℕ) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (slope m) (-(m : ℝ) * slope m p / bound m p) p := by
  have h := (angularSlope_hasDeriv m (radius m p) (radius_interior m p hp)).comp p
    (radius_hasDeriv m p hp)
  apply h.congr_deriv
  dsimp only [slope,bound,momentBound]
  rw [pow_succ]
  field_simp [(normalizer_pos m).ne', (radius_sin_pos m p hp).ne', (radius_cos_pos m p hp).ne']

theorem model_deriv (m : ℕ) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) : deriv (model m) p = slope m p :=
  (model_hasDeriv m p hp).deriv

theorem slope_deriv (m : ℕ) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    deriv (slope m) p = -(m : ℝ) * slope m p / bound m p := (slope_hasDeriv m p hp).deriv

theorem slope_continuousOn (m : ℕ) : ContinuousOn (slope m) (Ioo (0 : ℝ) 1) :=
  fun p hp => (slope_hasDeriv m p hp).continuousAt.continuousWithinAt

theorem second_hasDeriv (m : ℕ) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (deriv (model m)) (-(m : ℝ) * slope m p / bound m p) p := by
  apply (slope_hasDeriv m p hp).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hp] with q hq
  exact model_deriv m q hq

theorem model_ode (m : ℕ) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv (model m)) p / deriv (model m) p = -(m : ℝ) / bound m p := by
  rw [(second_hasDeriv m p hp).deriv,model_deriv m p hp]
  field_simp [(slope_pos m p hp).ne']

theorem slope_contDiffOn (m : ℕ) : ContDiffOn ℝ 1 (slope m) (Ioo (0 : ℝ) 1) := by
  rw [show (1 : ℕ∞ω) = 0+1 from rfl,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun p hp => (slope_hasDeriv m p hp).differentiableAt.differentiableWithinAt,by simp,?_⟩
  rw [contDiffOn_zero]
  have hc : ContinuousOn (fun p => -(m : ℝ) * slope m p / bound m p) (Ioo (0 : ℝ) 1) :=
    (continuousOn_const.mul (slope_continuousOn m)).div (bound_continuous m).continuousOn
      (fun p hp => (bound_pos m p hp).ne')
  exact hc.congr (fun p hp => slope_deriv m p hp)

theorem model_contDiffOn_two (m : ℕ) : ContDiffOn ℝ 2 (model m) (Ioo (0 : ℝ) 1) := by
  rw [show (2 : ℕ∞ω) = 1+1 from rfl,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun p hp => (model_hasDeriv m p hp).differentiableAt.differentiableWithinAt,by simp,?_⟩
  exact (slope_contDiffOn m).congr (fun p hp => model_deriv m p hp)

end ShadowVerification.CapModel
#print axioms ShadowVerification.CapModel.model_continuous
#print axioms ShadowVerification.CapModel.model_zero
#print axioms ShadowVerification.CapModel.model_one
#print axioms ShadowVerification.CapModel.model_mass
#print axioms ShadowVerification.CapModel.bound_mass
#print axioms ShadowVerification.CapModel.slope_pos
#print axioms ShadowVerification.CapModel.bound_pos
#print axioms ShadowVerification.CapModel.bound_continuous
#print axioms ShadowVerification.CapModel.model_hasDeriv
#print axioms ShadowVerification.CapModel.angularSlope_hasDeriv
#print axioms ShadowVerification.CapModel.slope_hasDeriv
#print axioms ShadowVerification.CapModel.model_deriv
#print axioms ShadowVerification.CapModel.slope_deriv
#print axioms ShadowVerification.CapModel.slope_continuousOn
#print axioms ShadowVerification.CapModel.second_hasDeriv
#print axioms ShadowVerification.CapModel.model_ode

#print axioms ShadowVerification.CapModel.slope_contDiffOn
#print axioms ShadowVerification.CapModel.model_contDiffOn_two

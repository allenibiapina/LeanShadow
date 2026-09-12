import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! # Exact angular cap, belt, and moment functions

The exponent m is the ambient dimension minus two. The normalizing
constant is defined by its exact integral; no special-function identity
is assumed. All functions are total real functions, with geometric
interpretations on the interval [0, pi/2].
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Real
open scoped Topology
namespace ShadowVerification.CapFunctions

def sinPrimitive (m : ℕ) (r : ℝ) : ℝ := ∫ t in 0..r, Real.sin t ^ m
def cosPrimitive (m : ℕ) (r : ℝ) : ℝ := ∫ t in 0..r, Real.cos t ^ m
def normalizer (m : ℕ) : ℝ := (sinPrimitive m (Real.pi / 2))⁻¹
def capMass (m : ℕ) (r : ℝ) : ℝ := normalizer m * sinPrimitive m r
def beltMass (m : ℕ) (r : ℝ) : ℝ := normalizer m * cosPrimitive m r
def capMoment (m : ℕ) (r : ℝ) : ℝ :=
  normalizer m * ∫ t in 0..r, Real.cos t ^ 2 * Real.sin t ^ m
def momentBound (m : ℕ) (r : ℝ) : ℝ :=
  normalizer m * Real.cos r * Real.sin r ^ (m+1)

theorem sinPrimitive_hasDeriv (m : ℕ) (r : ℝ) :
    HasDerivAt (sinPrimitive m) (Real.sin r ^ m) r :=
  intervalIntegral.integral_hasDerivAt_right (by apply Continuous.intervalIntegrable; fun_prop)
    (by exact (Real.continuous_sin.pow m).stronglyMeasurable.stronglyMeasurableAtFilter)
    (by fun_prop)

theorem cosPrimitive_hasDeriv (m : ℕ) (r : ℝ) :
    HasDerivAt (cosPrimitive m) (Real.cos r ^ m) r :=
  intervalIntegral.integral_hasDerivAt_right (by apply Continuous.intervalIntegrable; fun_prop)
    (by exact (Real.continuous_cos.pow m).stronglyMeasurable.stronglyMeasurableAtFilter)
    (by fun_prop)

theorem sinPrimitive_pos (m : ℕ) (r : ℝ) (hr : 0 < r) (hpi : r ≤ Real.pi) :
    0 < sinPrimitive m r := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (by apply Continuous.intervalIntegrable; fun_prop) _ hr
  intro t ht
  exact pow_pos (Real.sin_pos_of_pos_of_lt_pi ht.1 (ht.2.trans_le hpi)) _

theorem normalizer_pos (m : ℕ) : 0 < normalizer m :=
  inv_pos.mpr (sinPrimitive_pos m _ (by positivity) (by linarith [Real.pi_pos]))

theorem sinPrimitive_reflection (m : ℕ) (r : ℝ) :
    sinPrimitive m (Real.pi-r) + sinPrimitive m r = sinPrimitive m Real.pi := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := r)
    (fun x : ℝ => Real.sin x ^ m) Real.pi
  simp only [Real.sin_pi_sub, sub_zero] at h
  rw [sinPrimitive, sinPrimitive, h]
  exact intervalIntegral.integral_add_adjacent_intervals (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop)

theorem sinPrimitive_pi (m : ℕ) : sinPrimitive m Real.pi = 2 * sinPrimitive m (Real.pi/2) := by
  have h := sinPrimitive_reflection m (Real.pi/2)
  have he : Real.pi-Real.pi/2 = Real.pi/2 := by ring
  rw [he] at h
  linarith

theorem capMass_zero (m : ℕ) : capMass m 0 = 0 := by simp [capMass,sinPrimitive]

theorem capMass_half_pi (m : ℕ) : capMass m (Real.pi/2) = 1 := by
  exact inv_mul_cancel₀ (sinPrimitive_pos m _ (by positivity) (by linarith [Real.pi_pos])).ne'

theorem beltMass_zero (m : ℕ) : beltMass m 0 = 0 := by simp [beltMass,cosPrimitive]

theorem beltMass_complement (m : ℕ) (r : ℝ) :
    beltMass m r = 1 - capMass m (Real.pi/2-r) := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := r)
    (fun x : ℝ => Real.sin x ^ m) (Real.pi/2)
  simp only [Real.sin_pi_div_two_sub, sub_zero] at h
  have hi := intervalIntegral.integral_add_adjacent_intervals (a := (0 : ℝ))
    (b := Real.pi/2-r) (c := Real.pi/2) (μ := volume) (f := fun x => Real.sin x ^ m)
    (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop)
  rw [← h] at hi
  change sinPrimitive m (Real.pi/2-r) + cosPrimitive m r = sinPrimitive m (Real.pi/2) at hi
  have hn := capMass_half_pi m
  unfold beltMass capMass at *
  linear_combination normalizer m * hi + hn

theorem beltMass_half_pi (m : ℕ) : beltMass m (Real.pi/2) = 1 := by
  rw [beltMass_complement, sub_self, capMass_zero, sub_zero]

theorem capMass_hasDeriv (m : ℕ) (r : ℝ) :
    HasDerivAt (capMass m) (normalizer m * Real.sin r ^ m) r :=
  (sinPrimitive_hasDeriv m r).const_mul _

theorem beltMass_hasDeriv (m : ℕ) (r : ℝ) :
    HasDerivAt (beltMass m) (normalizer m * Real.cos r ^ m) r :=
  (cosPrimitive_hasDeriv m r).const_mul _

theorem capMass_continuous (m : ℕ) : Continuous (capMass m) :=
  continuous_iff_continuousAt.mpr fun r => (capMass_hasDeriv m r).continuousAt

theorem beltMass_continuous (m : ℕ) : Continuous (beltMass m) :=
  continuous_iff_continuousAt.mpr fun r => (beltMass_hasDeriv m r).continuousAt

theorem capMass_strictMono (m : ℕ) : StrictMonoOn (capMass m) (Icc 0 (Real.pi/2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (capMass_continuous m).continuousOn
  intro r hr
  rw [interior_Icc] at hr
  rw [(capMass_hasDeriv m r).deriv]
  exact mul_pos (normalizer_pos m) (pow_pos
    (Real.sin_pos_of_pos_of_lt_pi hr.1 (by linarith [hr.2,Real.pi_pos])) _)

theorem moment_boundary_hasDeriv (m : ℕ) (r : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cos t * Real.sin t ^ (m+1))
      (((m+2 : ℕ) : ℝ) * Real.cos r ^ 2 * Real.sin r ^ m - Real.sin r ^ m) r := by
  have h := (Real.hasDerivAt_cos r).mul ((Real.hasDerivAt_sin r).pow (m+1))
  apply h.congr_deriv
  simp only [Pi.pow_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_succ]
  linear_combination -(Real.sin r ^ m) * (Real.sin_sq_add_cos_sq r)

theorem moment_identity (m : ℕ) (r : ℝ) :
    ((m+2 : ℕ) : ℝ) * capMoment m r - capMass m r = momentBound m r := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := r) (fun t _ => moment_boundary_hasDeriv m t) (by apply Continuous.intervalIntegrable; fun_prop)
  simp only [Real.cos_zero,Real.sin_zero,zero_pow (Nat.succ_ne_zero m),mul_zero,sub_zero] at h
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop)] at h
  simp_rw [mul_assoc] at h
  rw [intervalIntegral.integral_const_mul] at h
  unfold capMoment capMass momentBound sinPrimitive
  linear_combination normalizer m * h

theorem momentBound_pos (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) (Real.pi/2)) :
    0 < momentBound m r := by
  exact mul_pos (mul_pos (normalizer_pos m)
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,hr.1],hr.2⟩))
    (pow_pos (Real.sin_pos_of_pos_of_lt_pi hr.1 (by linarith [Real.pi_pos,hr.2])) _)

end ShadowVerification.CapFunctions
#print axioms ShadowVerification.CapFunctions.sinPrimitive_hasDeriv
#print axioms ShadowVerification.CapFunctions.cosPrimitive_hasDeriv
#print axioms ShadowVerification.CapFunctions.sinPrimitive_pos
#print axioms ShadowVerification.CapFunctions.normalizer_pos
#print axioms ShadowVerification.CapFunctions.sinPrimitive_reflection
#print axioms ShadowVerification.CapFunctions.sinPrimitive_pi
#print axioms ShadowVerification.CapFunctions.capMass_zero
#print axioms ShadowVerification.CapFunctions.capMass_half_pi
#print axioms ShadowVerification.CapFunctions.beltMass_zero
#print axioms ShadowVerification.CapFunctions.beltMass_complement
#print axioms ShadowVerification.CapFunctions.beltMass_half_pi
#print axioms ShadowVerification.CapFunctions.capMass_hasDeriv
#print axioms ShadowVerification.CapFunctions.beltMass_hasDeriv
#print axioms ShadowVerification.CapFunctions.capMass_continuous
#print axioms ShadowVerification.CapFunctions.beltMass_continuous
#print axioms ShadowVerification.CapFunctions.capMass_strictMono
#print axioms ShadowVerification.CapFunctions.moment_boundary_hasDeriv
#print axioms ShadowVerification.CapFunctions.moment_identity
#print axioms ShadowVerification.CapFunctions.momentBound_pos

import LeanShadow.QuadraticSupport
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Continuous

/-! # Second-order Peano expansions from right derivatives

A continuous function with a right derivative v on an open interval has
a quadratic Peano expansion at each point where v is differentiable.
The one-sided mean-value estimate controls the remainder on either side.
Applying monotone differentiation to the right derivative of a concave
function proves the expansion almost everywhere without a C² assumption.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology Asymptotics
namespace ShadowVerification.RightSlopeTaylor
open ProfileSupport

theorem expansion_hasDerivAt (f : ℝ → ℝ) (p k rho : ℝ)
    (h : HasQuadraticExpansion f p k rho) : HasDerivAt f k p := by
  have hz : Tendsto (fun x : ℝ => x-p) (𝓝 p) (𝓝 0) := by
    simpa using (tendsto_id.sub_const p : Tendsto (fun x : ℝ => x-p) (𝓝 p) (𝓝 (p-p)))
  have ho : (fun x : ℝ => x-p) =o[𝓝 p] (fun _ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr hz
  have hsq : (fun x : ℝ => (x-p)^2) =o[𝓝 p] (fun x => x-p) := by
    simpa only [one_mul,← pow_two] using ho.mul_isBigO (Asymptotics.isBigO_refl (fun x : ℝ => x-p) (𝓝 p))
  have hh := (h.trans hsq).sub (hsq.const_mul_left (rho/2))
  have he : (fun x => (f x - Contact.support (f p) p k rho x) - rho/2*(x-p)^2) =
      fun x => f x - f p - (x-p) * k := by
    funext x
    dsimp [Contact.support]
    ring
  rw [he] at hh
  exact HasDerivAt.of_isLittleO (by simpa only [smul_eq_mul] using hh)

theorem expansion_of_right_derivative (f v : ℝ → ℝ) (a b p lam : ℝ)
    (hp : p ∈ Ioo a b) (hf : ContinuousOn f (Ioo a b))
    (hv : ∀ x ∈ Ioo a b, HasDerivWithinAt f (v x) (Ioi x) x)
    (hvp : HasDerivAt v lam p) : HasQuadraticExpansion f p (v p) (-lam) := by
  let R : ℝ → ℝ := fun x => f x - Contact.support (f p) p (v p) (-lam) x
  let D : ℝ → ℝ := fun x => v x - Contact.slope p (v p) (-lam) x
  have hR0 : R p = 0 := by simp [R,Contact.support]
  have hRc : ContinuousOn R (Ioo a b) := hf.sub (by unfold Contact.support; fun_prop)
  have hRd (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivWithinAt R (D x) (Ici x) x :=
    ((hv x hx).sub (Contact.support_hasDeriv (f p) p (v p) (-lam) x).hasDerivWithinAt).Ici_of_Ioi
  have hDo : D =o[𝓝 p] (fun x => x-p) := by
    have he : D = fun x => v x - v p - (x-p) * lam := by
      funext x
      dsimp [D,Contact.slope]
      ring
    rw [he]
    simpa only [smul_eq_mul] using hvp.isLittleO
  apply Asymptotics.isLittleO_iff.mpr
  intro eps heps
  have hn := (hDo.def heps).and (isOpen_Ioo.mem_nhds hp)
  obtain ⟨d,hd,hnear⟩ := Metric.eventually_nhds_iff.mp hn
  filter_upwards [Metric.ball_mem_nhds p hd] with s hs
  have hsd : |s-p| < d := by simpa only [Metric.mem_ball,Real.dist_eq] using hs
  have hinterval (t : ℝ) (ht : t ∈ uIcc p s) :
      t ∈ Ioo a b ∧ ‖D t‖ ≤ eps * |s-p| := by
    have htle : |t-p| ≤ |s-p| := by
      rcases le_total p s with hps | hsp
      · rw [uIcc_of_le hps] at ht
        rw [abs_of_nonneg (sub_nonneg.mpr ht.1),abs_of_nonneg (sub_nonneg.mpr hps)]
        linarith [ht.2]
      · rw [uIcc_of_ge hsp] at ht
        rw [abs_of_nonpos (sub_nonpos.mpr ht.2),abs_of_nonpos (sub_nonpos.mpr hsp)]
        linarith [ht.1]
    have h := hnear (show dist t p < d by rw [Real.dist_eq]; exact htle.trans_lt hsd)
    exact ⟨h.2,h.1.trans (mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using htle) heps.le)⟩
  have hbound : ‖R s‖ ≤ eps * |s-p| ^ 2 := by
    rcases le_total p s with hps | hsp
    · have hsub : Icc p s ⊆ Ioo a b := fun t ht => (hinterval t (by rwa [uIcc_of_le hps])).1
      have h := norm_image_sub_le_of_norm_deriv_right_le_segment (hRc.mono hsub)
        (fun t ht => hRd t (hsub ⟨ht.1,ht.2.le⟩))
        (fun t ht => (hinterval t (by rw [uIcc_of_le hps]; exact ⟨ht.1,ht.2.le⟩)).2)
        s (right_mem_Icc.mpr hps)
      rw [hR0,sub_zero] at h
      rw [abs_of_nonneg (sub_nonneg.mpr hps)] at h ⊢
      nlinarith
    · have hsub : Icc s p ⊆ Ioo a b := fun t ht => (hinterval t (by rwa [uIcc_of_ge hsp])).1
      have h := norm_image_sub_le_of_norm_deriv_right_le_segment (hRc.mono hsub)
        (fun t ht => hRd t (hsub ⟨ht.1,ht.2.le⟩))
        (fun t ht => (hinterval t (by rw [uIcc_of_ge hsp]; exact ⟨ht.1,ht.2.le⟩)).2)
        p (right_mem_Icc.mpr hsp)
      rw [hR0,zero_sub,norm_neg] at h
      rw [abs_of_nonpos (sub_nonpos.mpr hsp)] at h ⊢
      nlinarith
  simpa only [R,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (s-p)),sq_abs] using hbound

noncomputable def rightSlope (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -derivWithin (-f) (Ioi x) x

theorem rightSlope_hasDeriv (f : ℝ → ℝ) (a b : ℝ) (hf : ConcaveOn ℝ (Icc a b) f)
    (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivWithinAt f (rightSlope f x) (Ioi x) x := by
  have h := (hf.neg.hasDerivWithinAt_rightDeriv_of_mem_interior
    (show x ∈ interior (Icc a b) by simpa only [interior_Icc] using hx)).neg
  simpa only [neg_neg,rightSlope] using h

theorem rightSlope_antitone (f : ℝ → ℝ) (a b : ℝ) (hf : ConcaveOn ℝ (Icc a b) f) :
    AntitoneOn (rightSlope f) (Ioo a b) := by
  have h := hf.neg.monotoneOn_rightDeriv
  intro x hx y hy hxy
  exact neg_le_neg (h (by simpa only [interior_Icc] using hx)
    (by simpa only [interior_Icc] using hy) hxy)

theorem rightSlope_ae_differentiable (f : ℝ → ℝ) (a b : ℝ) (hf : ConcaveOn ℝ (Icc a b) f) :
    ∀ᵐ p : ℝ, p ∈ Ioo a b → DifferentiableAt ℝ (rightSlope f) p := by
  have h := hf.neg.monotoneOn_rightDeriv.ae_differentiableWithinAt_of_mem
  filter_upwards [h] with p hp hpin
  have hin : p ∈ interior (Icc a b) := by simpa only [interior_Icc] using hpin
  exact ((hp hin).differentiableAt (isOpen_interior.mem_nhds hin)).neg

theorem ae_quadratic_expansion (f : ℝ → ℝ) (a b : ℝ) (hf : ConcaveOn ℝ (Icc a b) f) :
    ∀ᵐ p : ℝ, p ∈ Ioo a b →
      HasQuadraticExpansion f p (rightSlope f p) (-deriv (rightSlope f) p) := by
  filter_upwards [rightSlope_ae_differentiable f a b hf] with p hp hpin
  apply expansion_of_right_derivative f (rightSlope f) a b p _ hpin
  · simpa only [interior_Icc] using hf.continuousOn_interior
  · exact rightSlope_hasDeriv f a b hf
  · exact (hp hpin).hasDerivAt

end ShadowVerification.RightSlopeTaylor
#print axioms ShadowVerification.RightSlopeTaylor.expansion_hasDerivAt
#print axioms ShadowVerification.RightSlopeTaylor.expansion_of_right_derivative
#print axioms ShadowVerification.RightSlopeTaylor.rightSlope_hasDeriv
#print axioms ShadowVerification.RightSlopeTaylor.rightSlope_antitone
#print axioms ShadowVerification.RightSlopeTaylor.rightSlope_ae_differentiable
#print axioms ShadowVerification.RightSlopeTaylor.ae_quadratic_expansion

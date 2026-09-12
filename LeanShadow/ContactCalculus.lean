import LeanShadow.CurveCalculus

/-! # The quadratic contact function and its actual derivatives

Only the fixed quadratic support is differentiated. No C² hypothesis about
the optimal shadow profile is made. The functions composed with the support
are ordinary C² functions near the base parameter.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace ShadowVerification.Contact

noncomputable def support (q p k rho s : ℝ) : ℝ :=
  q + k * (s - p) - (rho / 2) * (s - p) ^ 2

noncomputable def slope (p k rho s : ℝ) : ℝ := k - rho * (s - p)

theorem support_hasDeriv (q p k rho s : ℝ) :
    HasDerivAt (support q p k rho) (slope p k rho s) s := by
  have h := ((hasDerivAt_const s q).add (((hasDerivAt_id s).sub_const p).const_mul k)).sub
    ((((hasDerivAt_id s).sub_const p).pow 2).const_mul (rho / 2))
  have he : (0 + k * 1 - rho / 2 * (↑(2 : ℕ) * (id s - p) ^ (2 - 1) * 1)) =
      slope p k rho s := by
    dsimp [slope]
    ring
  rw [he] at h
  exact h

/-- First derivative of b + phi(a), for the actual quadratic support. -/
theorem contact_hasDeriv (q p k rho : ℝ) (a b : ℝ → ℝ) (s da db : ℝ)
    (ha : HasDerivAt a da s) (hb : HasDerivAt b db s) :
    HasDerivAt (fun t => b t + support q p k rho (a t))
      (db + slope p k rho (a s) * da) s :=
  hb.add ((support_hasDeriv q p k rho (a s)).comp s ha)

/-- The negative rank-one term comes from phi'' = -rho. -/
theorem contact_second_deriv (q p k rho : ℝ) (a b : ℝ → ℝ)
    (ha : ContDiffAt ℝ 2 a 0) (hb : ContDiffAt ℝ 2 b 0) :
    deriv (deriv (fun t => b t + support q p k rho (a t))) 0 =
      deriv (deriv b) 0 + slope p k rho (a 0) * deriv (deriv a) 0 -
        rho * (deriv a 0) ^ 2 := by
  have heq : deriv (fun t => b t + support q p k rho (a t)) =ᶠ[𝓝 0]
      fun t => deriv b t + slope p k rho (a t) * deriv a t := by
    filter_upwards [ha.eventually (by norm_num), hb.eventually (by norm_num)] with t hat hbt
    exact (contact_hasDeriv q p k rho a b t (deriv a t) (deriv b t)
      (hat.differentiableAt (by norm_num)).hasDerivAt
      (hbt.differentiableAt (by norm_num)).hasDerivAt).deriv
  rw [heq.deriv_eq]
  have hda := ((ha.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hdb := ((hb.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hs : HasDerivAt (fun t => slope p k rho (a t)) (-rho * deriv a 0) 0 := by
    have h := (hasDerivAt_const 0 k).sub
      ((((ha.differentiableAt (by norm_num)).hasDerivAt).sub_const p).const_mul rho)
    have he : 0 - rho * deriv a 0 = -rho * deriv a 0 := by ring
    rw [he] at h
    exact h
  have hd := hdb.add (hs.mul hda)
  change deriv (deriv b + (fun t => slope p k rho (a t)) * deriv a) 0 = _
  rw [hd.deriv]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual exponential orbit is smooth as a function of its time. -/
theorem flow_contDiff (H : E →L[ℝ] E) (x : E) (k : ℕ) :
    ContDiff ℝ k (Projective.flow H x) := by
  have he : ContDiff ℝ k (NormedSpace.exp : (E →L[ℝ] E) → E →L[ℝ] E) :=
    contDiff_iff_contDiffAt.mpr fun L => (NormedSpace.exp_analytic (𝕂 := ℝ) L).contDiffAt
  exact (he.comp (contDiff_id.smul contDiff_const)).clm_apply contDiff_const

/-- Joint C² regularity gives the C² scalar orbit needed by the contact rule. -/
theorem along_flow_contDiffAt (u : E → ℝ) (H : E →L[ℝ] E) (x : E)
    (hu : ContDiffAt ℝ 2 u x) :
    ContDiffAt ℝ 2 (fun t => u (Projective.flow H x t)) 0 := by
  have h : ContDiffAt ℝ 2 u (Projective.flow H x 0) := by simpa only [Projective.flow_zero] using hu
  exact h.comp 0 (flow_contDiff H x 2).contDiffAt

end ShadowVerification.Contact
#print axioms ShadowVerification.Contact.support_hasDeriv
#print axioms ShadowVerification.Contact.contact_hasDeriv
#print axioms ShadowVerification.Contact.contact_second_deriv
#print axioms ShadowVerification.Contact.flow_contDiff
#print axioms ShadowVerification.Contact.along_flow_contDiffAt

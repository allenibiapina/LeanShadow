import LeanShadow.MonotoneIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # A nonsmooth integrating-factor comparison via logarithmic variation

The positive measure of -log(v) includes its full singular part. Comparing
its increments with the smooth function -log(w) proves that v/w decreases.
No absolute continuity or continuity of v is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ShadowVerification.BVLogComparison
open MonotoneIntegral

theorem smooth_increment_le_monotone (u U u' : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hU : MonotoneOn U (Icc a b))
    (hu : ∀ x ∈ Icc a b, HasDerivAt u (u' x) x)
    (hu' : ContinuousOn u' (Icc a b))
    (hineq : ∀ᵐ x : ℝ, x ∈ Ioo a b → u' x ≤ deriv U x) :
    u b - u a ≤ U b - U a := by
  obtain ⟨F,hF,hUF⟩ := hU.exists_monotone_extension
    (hU.map_bddBelow (s := Icc a b) subset_rfl ⟨a,fun x hx => hx.1,⟨le_rfl,hab.le⟩⟩)
    (hU.map_bddAbove (s := Icc a b) subset_rfl ⟨b,fun x hx => hx.2,⟨hab.le,le_rfl⟩⟩)
  have hFi : IntegrableOn (deriv F) (Ioo a b) :=
    (monotone_deriv_integrable F hF a b).mono_set Ioo_subset_Icc_self
  have hui : IntervalIntegrable u' volume a b := hu'.intervalIntegrable_of_Icc hab.le
  have hFTC : (∫ x in a..b, u' x) = u b - u a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hu x (by simpa only [uIcc_of_le hab.le] using hx)) hui
  have hcomp : (∫ x in a..b, u' x) ≤ ∫ x in a..b, deriv F x := by
    rw [intervalIntegral.integral_of_le hab.le,intervalIntegral.integral_of_le hab.le,
      integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
    apply integral_mono_ae (hu'.integrableOn_Icc.mono_set Ioo_subset_Icc_self) hFi
    filter_upwards [ae_restrict_of_ae hineq,ae_restrict_mem measurableSet_Ioo] with x hx hxin
    have he : U =ᶠ[𝓝 x] F := by
      filter_upwards [isOpen_Ioo.mem_nhds hxin] with y hy
      exact hUF ⟨hy.1.le,hy.2.le⟩
    rw [← he.deriv_eq]
    exact hx hxin
  rw [hFTC] at hcomp
  have hlast := monotone_integral_deriv_le F hF a b hab.le
  rw [← hUF ⟨hab.le,le_rfl⟩,← hUF ⟨le_rfl,hab.le⟩] at hlast
  exact hcomp.trans hlast

theorem ratio_antitone (v w w' : ℝ → ℝ) (a b : ℝ)
    (hv : AntitoneOn v (Ioo a b)) (hvp : ∀ x ∈ Ioo a b, 0 < v x)
    (hwp : ∀ x ∈ Ioo a b, 0 < w x)
    (hw : ∀ x ∈ Ioo a b, HasDerivAt w (w' x) x)
    (hw' : ContinuousOn w' (Ioo a b))
    (hineq : ∀ᵐ x : ℝ, x ∈ Ioo a b → deriv v x - (w' x / w x) * v x ≤ 0) :
    AntitoneOn (fun x => v x / w x) (Ioo a b) := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hxy
  · exact le_rfl
  have hsub : Icc x y ⊆ Ioo a b := fun t ht => ⟨hx.1.trans_le ht.1,ht.2.trans_lt hy.2⟩
  have hvc : MonotoneOn (fun t => -Real.log (v t)) (Icc x y) := by
    intro s hs t ht hst
    exact neg_le_neg (Real.log_le_log (hvp t (hsub ht)) (hv (hsub hs) (hsub ht) hst))
  have hlog : ∀ t ∈ Icc x y, HasDerivAt (fun z => -Real.log (w z)) (-(w' t / w t)) t :=
    fun t ht => ((hw t (hsub ht)).log (hwp t (hsub ht)).ne').neg
  have hcont : ContinuousOn (fun t => -(w' t / w t)) (Icc x y) :=
    ((hw'.mono hsub).div
      (fun t ht => (hw t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hwp t (hsub ht)).ne')).neg
  have hdiff : ∀ᵐ t : ℝ, t ∈ Ioo a b → DifferentiableAt ℝ v t := by
    filter_upwards [hv.neg.ae_differentiableWithinAt_of_mem] with t ht htin
    have hm : DifferentiableAt ℝ (fun z => -v z) t :=
      (ht htin).differentiableAt (isOpen_Ioo.mem_nhds htin)
    have hn : DifferentiableAt ℝ (fun z => -(-v z)) t := hm.neg
    simpa only [neg_neg] using hn
  have hbound : ∀ᵐ t : ℝ, t ∈ Ioo x y →
      -(w' t / w t) ≤ deriv (fun z => -Real.log (v z)) t := by
    filter_upwards [hdiff,hineq] with t ht hi htin
    have hab : t ∈ Ioo a b := hsub ⟨htin.1.le,htin.2.le⟩
    have hd : HasDerivAt (fun z => -Real.log (v z)) (-(deriv v t / v t)) t :=
      ((ht hab).hasDerivAt.log (hvp t hab).ne').neg
    rw [hd.deriv]
    apply neg_le_neg
    apply (div_le_iff₀ (hvp t hab)).mpr
    linarith [hi hab]
  have h := smooth_increment_le_monotone (fun t => -Real.log (w t))
    (fun t => -Real.log (v t)) (fun t => -(w' t / w t)) x y hxy hvc hlog hcont hbound
  apply (Real.log_le_log_iff (div_pos (hvp y hy) (hwp y hy))
    (div_pos (hvp x hx) (hwp x hx))).mp
  rw [Real.log_div (hvp y hy).ne' (hwp y hy).ne',Real.log_div (hvp x hx).ne' (hwp x hx).ne']
  linarith

end ShadowVerification.BVLogComparison
#print axioms ShadowVerification.BVLogComparison.smooth_increment_le_monotone
#print axioms ShadowVerification.BVLogComparison.ratio_antitone

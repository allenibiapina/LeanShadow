import LeanShadow.SphericalCaps
import LeanShadow.SmallShadowCaps

/-! # The literal shadow of an antipodal cap is its equatorial belt -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Real
open scoped Topology ENNReal
namespace ShadowVerification.CapShadow
open Spherical SphericalCaps CapFunctions
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem shadow_cap (a : Sphere E) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) :
    shadow (cap a r) = {y : Sphere E | |inner ℝ (a : E) (y : E)| < Real.sin r} := by
  ext y
  have ha : ‖(a : E)‖ = 1 := mem_sphere_zero_iff_norm.mp a.property
  have hy : ‖(y : E)‖ = 1 := mem_sphere_zero_iff_norm.mp y.property
  have hyy : inner ℝ (y : E) (y : E) = 1 := by rw [real_inner_self_eq_norm_sq,hy]; norm_num
  have haa : inner ℝ (a : E) (a : E) = 1 := by rw [real_inner_self_eq_norm_sq,ha]; norm_num
  have hc : 0 ≤ Real.cos r := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hr.1,Real.pi_pos],hr.2⟩
  have hs : 0 ≤ Real.sin r := Real.sin_nonneg_of_nonneg_of_le_pi hr.1 (by linarith [hr.2,Real.pi_pos])
  let v : E := (a : E) - inner ℝ (a : E) (y : E) • (y : E)
  have hvy : inner ℝ v (y : E) = 0 := by simp [v,inner_sub_left,real_inner_smul_left]
  have hav : inner ℝ (a : E) v = ‖v‖ ^ 2 := by
    have he : inner ℝ v v = inner ℝ (a : E) v := by
      rw [show inner ℝ v v = inner ℝ ((a : E) - inner ℝ (a : E) (y : E) • (y : E)) v from rfl,
        inner_sub_left,real_inner_smul_left,real_inner_comm v (y : E),hvy]
      ring
    exact (real_inner_self_eq_norm_sq v).symm.trans he |>.symm
  have hv : ‖v‖ ^ 2 = 1 - (inner ℝ (a : E) (y : E)) ^ 2 := by
    rw [← hav]
    simp only [v,inner_sub_right,real_inner_smul_right,haa]
    ring
  constructor
  · rintro ⟨x,hx,hxy⟩
    have hxx : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
    have hax : inner ℝ v (x : E) = inner ℝ (a : E) (x : E) := by
      simp [v,inner_sub_left,real_inner_smul_left,real_inner_comm (x : E) (y : E),hxy]
    have hb := abs_real_inner_le_norm v (x : E)
    rw [hax,hxx,mul_one] at hb
    change Real.cos r < |inner ℝ (a : E) (x : E)| at hx
    have hcv : Real.cos r < ‖v‖ := hx.trans_le hb
    have hsq := (sq_lt_sq₀ hc (norm_nonneg v)).mpr hcv
    change |inner ℝ (a : E) (y : E)| < Real.sin r
    nlinarith [Real.sin_sq_add_cos_sq r,sq_abs (inner ℝ (a : E) (y : E)),abs_nonneg (inner ℝ (a : E) (y : E))]
  · intro h
    change |inner ℝ (a : E) (y : E)| < Real.sin r at h
    have ht := (sq_lt_sq₀ (abs_nonneg (inner ℝ (a : E) (y : E))) hs).mpr h
    rw [sq_abs] at ht
    have hcv : Real.cos r < ‖v‖ := by nlinarith [Real.sin_sq_add_cos_sq r,norm_nonneg v]
    have hvpos : 0 < ‖v‖ := hc.trans_lt hcv
    let x : Sphere E := ⟨‖v‖⁻¹ • v, by
      rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hvpos),inv_mul_cancel₀ hvpos.ne']⟩
    refine ⟨x,?_,?_⟩
    · change Real.cos r < |inner ℝ (a : E) (‖v‖⁻¹ • v)|
      rw [real_inner_smul_right,hav]
      have he : ‖v‖⁻¹ * ‖v‖ ^ 2 = ‖v‖ := by field_simp
      rw [he,abs_of_nonneg (norm_nonneg v)]
      exact hcv
    · change inner ℝ (‖v‖⁻¹ • v) (y : E) = 0
      simp only [real_inner_smul_left,hvy,mul_zero]

variable [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem shadow_cap_measurable (a : Sphere E) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) :
    MeasurableSet (shadow (cap a r)) := by
  rw [shadow_cap a r hr]
  exact measurableSet_lt (by fun_prop) measurable_const

theorem shadow_cap_area (hd : 1 < Module.finrank ℝ E) (a : Sphere E) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) :
    area mu (shadow (cap a r)) = beltMass (Module.finrank ℝ E - 2) r := by
  have hn : ∀ᵐ x : Sphere E ∂probability mu, |inner ℝ (a : E) (x : E)| ≠ Real.sin r := by
    simpa only [ae_iff, not_not] using (SmallShadowCaps.abs_latitude_null mu hd a (Real.sin r))
  have he : shadow (cap a r) =ᵐ[probability mu] (cap a (Real.pi/2-r))ᶜ := by
    rw [shadow_cap a r hr]
    filter_upwards [hn] with x hx
    apply propext
    change (|inner ℝ (a : E) (x : E)| < Real.sin r) ↔ ¬ Real.cos (Real.pi/2-r) < |inner ℝ (a : E) (x : E)|
    rw [Real.cos_pi_div_two_sub,not_lt]
    exact lt_iff_le_and_ne.trans (and_iff_left hx)
  unfold area
  rw [measureReal_congr he,measureReal_compl (cap_measurable a _)]
  rw [show (probability mu).real (cap a (Real.pi/2-r)) = capMass (Module.finrank ℝ E - 2) (Real.pi/2-r)
    from cap_area mu hd a _ ⟨by linarith [hr.2],by linarith [hr.1]⟩]
  simpa using (beltMass_complement (Module.finrank ℝ E - 2) r).symm

theorem profile_le_cap (hd : 1 < Module.finrank ℝ E) (a : Sphere E) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) :
    Profile.profile mu (capMass (Module.finrank ℝ E - 2) r) ≤ beltMass (Module.finrank ℝ E - 2) r := by
  rw [← cap_area mu hd a r hr,← shadow_cap_area mu hd a r hr]
  exact Profile.profile_le_shadow mu (cap a r) (cap_measurable a r) (cap_antipodal a r)

end ShadowVerification.CapShadow
#print axioms ShadowVerification.CapShadow.shadow_cap
#print axioms ShadowVerification.CapShadow.shadow_cap_measurable
#print axioms ShadowVerification.CapShadow.shadow_cap_area
#print axioms ShadowVerification.CapShadow.profile_le_cap

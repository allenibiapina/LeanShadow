import LeanShadow.AngularNormalization
import LeanShadow.AntipodalDensity

/-! # Exact measures and axial moments of actual antipodal open caps -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Real
open scoped Topology ENNReal
namespace ShadowVerification.SphericalCaps
open Spherical Antipodal AngularNormalization CapFunctions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def cap (a : Sphere E) (r : ℝ) : Set (Sphere E) :=
  {x | Real.cos r < |inner ℝ (a : E) (x : E)|}

theorem cap_antipodal (a : Sphere E) (r : ℝ) : IsAntipodal (cap a r) := by
  intro x hx
  simpa only [cap,mem_ofPred_eq,antipode_coe,inner_neg_right,abs_neg] using hx

theorem cap_slice_union (a : Sphere E) (r : ℝ) :
    cap a r = slice a r ∪ antipode '' slice a r := by
  ext x
  simp only [cap,slice,mem_ofPred_eq,lt_abs,mem_union,mem_image]
  constructor
  · rintro (h|h)
    · exact Or.inl h
    · right
      refine ⟨antipode x, ?_, antipode_twice x⟩
      simpa only [antipode_coe,inner_neg_right] using h
  · rintro (h|⟨y,hy,rfl⟩)
    · exact Or.inl h
    · right
      simpa only [antipode_coe,inner_neg_right,neg_neg] using hy

theorem cap_slices_disjoint (a : Sphere E) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) :
    Disjoint (slice a r) (antipode '' slice a r) := by
  rw [Set.disjoint_left]
  rintro x hx ⟨y,hy,rfl⟩
  have hc : 0 ≤ Real.cos r := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos,hr.1],hr.2⟩
  change Real.cos r < inner ℝ (a : E) (antipode y : E) at hx
  rw [antipode_coe,inner_neg_right] at hx
  change Real.cos r < inner ℝ (a : E) (y : E) at hy
  linarith

variable [MeasurableSpace E] [BorelSpace E]

theorem cap_measurable (a : Sphere E) (r : ℝ) : MeasurableSet (cap a r) :=
  measurableSet_lt measurable_const (by fun_prop)

variable [FiniteDimensional ℝ E] [Nontrivial E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

theorem measurePreserving_antipode :
    MeasurePreserving (antipode (E := E)) (probability mu) (probability mu) := by
  refine ⟨antipode_continuous.measurable,?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply antipode_continuous.measurable hA]
  have he : antipode ⁻¹' A = antipode '' A := by
    ext x
    constructor
    · intro hx
      exact ⟨antipode x,hx,antipode_twice x⟩
    · rintro ⟨y,hy,rfl⟩
      simpa only [mem_preimage,antipode_twice] using hy
  rw [he,AntipodalDensity.measure_antipode_image mu A hA]

theorem lintegral_cap_even (hd : 1 < Module.finrank ℝ E) (a : Sphere E)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi/2))
    (h : ℝ → ℝ≥0∞) (hh : Measurable h) (heven : ∀ t, h (-t) = h t) :
    (∫⁻ x in cap a r, h (inner ℝ (a : E) (x : E)) ∂probability mu) =
      ENNReal.ofReal (normalizer (Module.finrank ℝ E - 2)) *
        ∫⁻ t in Ioo (0 : ℝ) r,
          ENNReal.ofReal (Real.sin t ^ (Module.finrank ℝ E - 2)) * h (Real.cos t) := by
  have ha : (∫⁻ x in antipode '' slice a r, h (inner ℝ (a : E) (x : E)) ∂probability mu) =
      ∫⁻ x in slice a r, h (inner ℝ (a : E) (x : E)) ∂probability mu := by
    have hi := (measurePreserving_antipode mu).setLIntegral_comp_emb
      (antipodeHomeomorph (E := E)).measurableEmbedding
      (fun x : Sphere E => h (inner ℝ (a : E) (x : E))) (slice a r)
    simpa only [antipode_coe,inner_neg_right,heven] using hi.symm
  have hneg : MeasurableSet (antipode '' slice a r) :=
    (antipodeHomeomorph (E := E)).measurableEmbedding.measurableSet_image.mpr (slice_measurable a r)
  rw [cap_slice_union,lintegral_union hneg
    (cap_slices_disjoint a r hr),ha,← two_mul,
    lintegral_slice mu hd a r ⟨hr.1,by linarith [hr.2,Real.pi_pos]⟩ h hh,
    ← mul_assoc, sinPrimitive_pi]
  congr 1
  have hp := sinPrimitive_pos (Module.finrank ℝ E - 2) (Real.pi/2)
    (by positivity) (by linarith [Real.pi_pos])
  rw [normalizer,ENNReal.ofReal_inv_of_pos hp,ENNReal.ofReal_mul (by norm_num)]
  simp only [ENNReal.ofReal_ofNat]
  rw [ENNReal.mul_inv (by simp) (by simp),← mul_assoc,ENNReal.mul_inv_cancel (by norm_num) (by norm_num),one_mul]

theorem cap_area (hd : 1 < Module.finrank ℝ E) (a : Sphere E)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) :
    area mu (cap a r) = capMass (Module.finrank ℝ E - 2) r := by
  have h := lintegral_cap_even mu hd a r hr (fun _ => 1) measurable_const (fun _ => rfl)
  simp only [lintegral_one,Measure.restrict_apply_univ,mul_one] at h
  rw [lintegral_Ioo_eq_ofReal _ r hr.1 (by fun_prop)
    (fun t ht => pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le
      (by linarith [ht.2,hr.2,Real.pi_pos])) _)] at h
  change (probability mu (cap a r)).toReal = _
  rw [h,ENNReal.toReal_mul,ENNReal.toReal_ofReal (normalizer_pos _).le,
    ENNReal.toReal_ofReal]
  · rfl
  · apply intervalIntegral.integral_nonneg hr.1
    intro t ht
    exact pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht.1
      (by linarith [ht.2,hr.2,Real.pi_pos])) _

theorem cap_axial_moment (hd : 1 < Module.finrank ℝ E) (a : Sphere E)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) :
    (∫ x in cap a r, (inner ℝ (a : E) (x : E)) ^ 2 ∂probability mu) =
      capMoment (Module.finrank ℝ E - 2) r := by
  have h := lintegral_cap_even mu hd a r hr (fun t => ENNReal.ofReal (t^2))
    (by fun_prop) (fun t => by simp)
  have hint : Integrable (fun x : Sphere E => (inner ℝ (a : E) (x : E)) ^ 2) (probability mu) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
    (Filter.Eventually.of_forall fun x => sq_nonneg (inner ℝ (a : E) (x : E)))] at h
  have heq : (∫⁻ t in Ioo (0 : ℝ) r,
      ENNReal.ofReal (Real.sin t ^ (Module.finrank ℝ E - 2)) * ENNReal.ofReal (Real.cos t ^ 2)) =
      ENNReal.ofReal (∫ t in 0..r, Real.cos t ^ 2 * Real.sin t ^ (Module.finrank ℝ E - 2)) := by
    rw [← lintegral_Ioo_eq_ofReal _ r hr.1 (by fun_prop)
      (fun t ht => mul_nonneg (sq_nonneg _) (pow_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [ht.2,hr.2,Real.pi_pos])) _))]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [ENNReal.ofReal_mul (sq_nonneg _),mul_comm]
  rw [heq,← ENNReal.ofReal_mul (normalizer_pos _).le] at h
  have hn : 0 ≤ normalizer (Module.finrank ℝ E - 2) *
      (∫ t in 0..r, Real.cos t ^ 2 * Real.sin t ^ (Module.finrank ℝ E - 2)) := by
    apply mul_nonneg (normalizer_pos _).le
    apply intervalIntegral.integral_nonneg hr.1
    intro t ht
    exact mul_nonneg (sq_nonneg (Real.cos t)) (pow_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, hr.2, Real.pi_pos])) _)
  have ht := congrArg ENNReal.toReal h
  simpa only [capMoment, ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _)),
    ENNReal.toReal_ofReal hn] using ht

end ShadowVerification.SphericalCaps
#print axioms ShadowVerification.SphericalCaps.cap_antipodal
#print axioms ShadowVerification.SphericalCaps.cap_slice_union
#print axioms ShadowVerification.SphericalCaps.cap_slices_disjoint
#print axioms ShadowVerification.SphericalCaps.cap_measurable
#print axioms ShadowVerification.SphericalCaps.measurePreserving_antipode
#print axioms ShadowVerification.SphericalCaps.lintegral_cap_even
#print axioms ShadowVerification.SphericalCaps.cap_area
#print axioms ShadowVerification.SphericalCaps.cap_axial_moment

import LeanShadow.ProfileClosedness

/-! # Positive caps with arbitrarily small literal shadows

Only latitude null sets are needed here, not the sharp cap-volume formula.
The symmetrized metric ball about an axis has shadow inside a thin belt.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace ShadowVerification.SmallShadowCaps
open Spherical Antipodal Profile ProfileClosedness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

theorem open_area_pos (U : Set (Sphere E)) (hU : IsOpen U) (hne : U.Nonempty) :
    0 < area mu U := by
  apply ENNReal.toReal_pos _ (measure_ne_top _ _)
  change ((mu.toSphere univ)⁻¹ • mu.toSphere) U ≠ 0
  rw [Measure.smul_apply,smul_eq_mul]
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) (hU.measure_pos _ hne).ne'

theorem latitude_null (hd : 1 < Module.finrank ℝ E) (e : Sphere E) (t : ℝ) :
    probability mu {x : Sphere E | inner ℝ (e : E) (x : E) = t} = 0 := by
  have h := LatitudeClass.coordinate_null_iff mu hd e {t} (measurableSet_singleton t)
  apply h.mpr
  exact measure_mono_null inter_subset_left (measure_singleton t)

theorem abs_latitude_null (hd : 1 < Module.finrank ℝ E) (e : Sphere E) (t : ℝ) :
    probability mu {x : Sphere E | |inner ℝ (e : E) (x : E)| = t} = 0 := by
  apply measure_mono_null (t := {x : Sphere E | inner ℝ (e : E) (x : E) = t} ∪
    {x : Sphere E | inner ℝ (e : E) (x : E) = -t})
  · intro x hx
    change |inner ℝ (e : E) (x : E)| = t at hx
    rcases le_total 0 (inner ℝ (e : E) (x : E)) with h | h
    · exact Or.inl (by rwa [abs_of_nonneg h] at hx)
    · apply Or.inr
      change inner ℝ (e : E) (x : E) = -t
      rw [abs_of_nonpos h] at hx
      linarith
  · exact measure_union_null (latitude_null mu hd e t) (latitude_null mu hd e (-t))

theorem thin_belt (hd : 1 < Module.finrank ℝ E) (e : Sphere E) (d : ℝ) (hdpos : 0 < d) :
    ∃ r > 0, area mu {x : Sphere E | |inner ℝ (e : E) (x : E)| ≤ r} < d := by
  let c : Sphere E → ℝ := fun x => |inner ℝ (e : E) (x : E)|
  have hc : Measurable c := by dsimp [c]; fun_prop
  have hcont := Trimming.cutMass_continuous (probability mu) c hc (abs_latitude_null mu hd e)
  have hzero : Trimming.cutMass (probability mu) c 0 = 0 := by
    unfold Trimming.cutMass
    have he : {x | c x ≤ 0} = {x | c x = 0} := by
      ext x
      exact ⟨fun h => le_antisymm h (abs_nonneg _), fun h => h.le⟩
    rw [he]
    change ((probability mu) {x | |inner ℝ (e : E) (x : E)| = 0}).toReal = 0
    rw [abs_latitude_null mu hd e,ENNReal.toReal_zero]
  have hnear : ∀ᶠ r in 𝓝 (0 : ℝ), Trimming.cutMass (probability mu) c r < d :=
    hcont.continuousAt.eventually (eventually_lt_nhds (show Trimming.cutMass (probability mu) c 0 < d by rw [hzero]; exact hdpos))
  obtain ⟨R,hR,hRR⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨R/2,half_pos hR,?_⟩
  exact hRR (by rw [dist_zero_right,Real.norm_eq_abs,abs_of_pos (half_pos hR)]; linarith)

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem shadow_ball_subset (e : Sphere E) (r : ℝ) :
    shadow (Metric.ball e r) ⊆ {y : Sphere E | |inner ℝ (e : E) (y : E)| ≤ r} := by
  rintro y ⟨x,hx,hxy⟩
  have hnorm : ‖(e : E) - x‖ < r := by
    simpa only [mem_ball,Subtype.dist_eq,dist_eq_norm,norm_sub_rev] using hx
  have h := abs_real_inner_le_norm ((e : E) - x) (y : E)
  rw [inner_sub_left,hxy,sub_zero,mem_sphere_zero_iff_norm.mp y.property,mul_one] at h
  exact (h.trans_lt hnorm).le

theorem exists_small_shadow (hd : 1 < Module.finrank ℝ E) (d : ℝ) (hdpos : 0 < d) :
    ∃ C : Set (Sphere E), MeasurableSet C ∧ IsAntipodal C ∧
      0 < area mu C ∧ area mu (shadow C) < d := by
  obtain ⟨e,_,_⟩ := OrthogonalIncidence.exists_orthogonal_pair hd
  obtain ⟨r,hr,hsmall⟩ := thin_belt mu hd e d hdpos
  let C := symmetrize (Metric.ball e r)
  refine ⟨C,symmetrize_measurable _ isOpen_ball.measurableSet,symmetrize_antipodal _,?_,?_⟩
  · exact (open_area_pos mu _ isOpen_ball ⟨e,mem_ball_self hr⟩).trans_le
      (measureReal_mono (subset_symmetrize _))
  · rw [show shadow C = shadow (Metric.ball e r) from shadow_symmetrize _]
    exact (measureReal_mono (shadow_ball_subset e r)).trans_lt hsmall

theorem profile_lt_one (hd : 1 < Module.finrank ℝ E) (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1) :
    profile mu p < 1 := by
  obtain ⟨C,hC,haC,hpos,hsmall⟩ := exists_small_shadow mu hd (1-p) (sub_pos.mpr hp1)
  let D := avoidingPartner mu C
  have hmD : p ≤ area mu D := by
    rw [show area mu D = 1 - area mu (shadow C) from avoidingPartner_area mu C]
    linarith
  obtain ⟨A,hAD,hA,haA,hmA⟩ := AntipodalTrimming.exists_subset_area mu hd D
    (avoidingPartner_measurable mu C) (avoidingPartner_antipodal mu C) p hp hmD
  have hAC : Avoids A C := by
    intro x hx y hy hxy
    exact avoids_avoidingPartner mu C y hy x (hAD hx) (by rwa [real_inner_comm])
  have h := feasible_profile_bound mu A C hA hC haA hAC
  rw [hmA] at h
  linarith

theorem profile_small_near_zero (hd : 1 < Module.finrank ℝ E) (d : ℝ) (hdpos : 0 < d) :
    ∃ r > 0, ∀ p, 0 ≤ p → p ≤ r → profile mu p < d := by
  obtain ⟨C,hC,haC,hpos,hsmall⟩ := exists_small_shadow mu hd d hdpos
  refine ⟨area mu C,hpos,fun p hp hpr => ?_⟩
  exact ((profile_monotone mu hd ⟨hp,hpr.trans (area_le_one mu C)⟩
    ⟨hpos.le,area_le_one mu C⟩ hpr).trans (profile_le_shadow mu C hC haC)).trans_lt hsmall

end ShadowVerification.SmallShadowCaps
#print axioms ShadowVerification.SmallShadowCaps.open_area_pos
#print axioms ShadowVerification.SmallShadowCaps.latitude_null
#print axioms ShadowVerification.SmallShadowCaps.abs_latitude_null
#print axioms ShadowVerification.SmallShadowCaps.thin_belt
#print axioms ShadowVerification.SmallShadowCaps.shadow_ball_subset
#print axioms ShadowVerification.SmallShadowCaps.exists_small_shadow
#print axioms ShadowVerification.SmallShadowCaps.profile_lt_one
#print axioms ShadowVerification.SmallShadowCaps.profile_small_near_zero

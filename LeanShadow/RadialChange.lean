import LeanShadow.SphericalProjective
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Polar integration for variable radial cutoffs

The spherical measure is related to actual ambient Haar measure by mathlib's
polar-coordinate measure-preserving homeomorphism. This module makes the
variable radial cutoff calculation explicit.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function MeasureTheory Metric
open scoped ENNReal Topology
namespace ShadowVerification.Radial
open Spherical

section Graph
variable {X : Type*} [MeasurableSpace X]

def graph (A : Set X) (r : X → Ioi (0 : ℝ)) : Set (X × Ioi (0 : ℝ)) :=
  {p | p.1 ∈ A ∧ p.2 < r p.1}

theorem measurable_graph (A : Set X) (r : X → Ioi (0 : ℝ))
    (hA : MeasurableSet A) (hr : Measurable r) : MeasurableSet (graph A r) :=
  (hA.preimage measurable_fst).inter (measurableSet_lt (measurable_subtype_coe.comp measurable_snd)
    (measurable_subtype_coe.comp (hr.comp measurable_fst)))

theorem graph_measure (nu : Measure X) (d : ℕ) (A : Set X) (r : X → Ioi (0 : ℝ))
    (hA : MeasurableSet A) (hr : Measurable r) :
    (nu.prod (Measure.volumeIoiPow d)) (graph A r) =
      ∫⁻ x in A, ENNReal.ofReal ((r x).1 ^ (d + 1) / (d + 1)) ∂nu := by
  classical
  rw [Measure.prod_apply (measurable_graph A r hA hr), ← lintegral_indicator hA]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ A
  · have heq : Prod.mk x ⁻¹' graph A r = Iio (r x) := by ext y; simp [graph, hx]
    simp only [heq, indicator_of_mem hx, Measure.volumeIoiPow_apply_Iio]
  · have heq : Prod.mk x ⁻¹' graph A r = ∅ := by ext y; simp [graph, hx]
    simp only [heq, measure_empty, indicator_of_notMem hx]
end Graph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

noncomputable def cone (A : Set (Sphere E)) (r : Sphere E → Ioi (0 : ℝ)) : Set E :=
  Subtype.val '' ((homeomorphUnitSphereProd E) ⁻¹' graph A r)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Polar coordinates identify the cone with the radial image of its graph. -/
theorem cone_as_image (A : Set (Sphere E)) (r : Sphere E → Ioi (0 : ℝ)) :
    cone A r = (fun p : Sphere E × Ioi (0 : ℝ) => p.2.1 • (p.1 : E)) '' graph A r := by
  unfold cone
  rw [← Homeomorph.image_symm, image_image]
  rfl

noncomputable def cutoff (T : E ≃L[ℝ] E) (x : Sphere E) : Ioi (0 : ℝ) :=
  ⟨‖T x‖⁻¹, inv_pos.mpr (norm_pos_iff.mpr
    (by simpa only [map_zero] using T.injective.ne (unit_ne_zero x)))⟩

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
theorem cutoff_continuous (T : E ≃L[ℝ] E) : Continuous (cutoff T) := by
  apply Continuous.subtype_mk
  apply Continuous.inv₀
  · fun_prop
  · intro x
    exact norm_ne_zero_iff.mpr (by simpa only [map_zero] using T.injective.ne (unit_ne_zero x))

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
/-- A normalized image cone is the linear image of a cone with variable
radial cutoff. This is an equality of sets, prior to taking any measures. -/
theorem action_cone (T : E ≃L[ℝ] E) (A : Set (Sphere E)) :
    cone (action T '' A) (fun _ => ⟨1, by norm_num⟩) = T '' cone A (cutoff T) := by
  rw [cone_as_image, cone_as_image]
  ext z
  constructor
  · rintro ⟨⟨y, s⟩, ⟨⟨x, hx, rfl⟩, hs⟩, rfl⟩
    have hp : 0 < ‖T x‖ := norm_pos_iff.mpr
      (by simpa only [map_zero] using T.injective.ne (unit_ne_zero x))
    let t : Ioi (0 : ℝ) := ⟨s.1 / ‖T x‖, div_pos s.2 hp⟩
    refine ⟨t.1 • (x : E), ⟨(x, t), ⟨hx, ?_⟩, rfl⟩, ?_⟩
    · change s.1 / ‖T x‖ < ‖T x‖⁻¹
      change s.1 < (1 : ℝ) at hs
      simpa only [one_div] using (div_lt_div_of_pos_right hs hp)
    · change T (t.1 • (x : E)) = s.1 • (action T x : E)
      rw [map_smul, action_coe, smul_smul]
      congr 1
  · rintro ⟨_, ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩, rfl⟩
    have hp : 0 < ‖T x‖ := norm_pos_iff.mpr
      (by simpa only [map_zero] using T.injective.ne (unit_ne_zero x))
    let t : Ioi (0 : ℝ) := ⟨s.1 * ‖T x‖, mul_pos s.2 hp⟩
    refine ⟨(action T x, t), ⟨⟨x, hx, rfl⟩, ?_⟩, ?_⟩
    · change s.1 * ‖T x‖ < 1
      change s.1 < ‖T x‖⁻¹ at hs
      simpa only [inv_mul_cancel₀ hp.ne'] using mul_lt_mul_of_pos_right hs hp
    · change t.1 • (action T x : E) = T (s.1 • (x : E))
      rw [action_coe, smul_smul, map_smul]
      congr 1
      dsimp [t]
      field_simp


theorem cone_measure (mu : Measure E) [mu.IsAddHaarMeasure]
    (A : Set (Sphere E)) (r : Sphere E → Ioi (0 : ℝ))
    (hA : MeasurableSet A) (hr : Measurable r) :
    mu (cone A r) =
      ∫⁻ x in A, ENNReal.ofReal ((r x).1 ^ Module.finrank ℝ E / Module.finrank ℝ E)
        ∂mu.toSphere := by
  have hdim : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hp := (mu.measurePreserving_homeomorphUnitSphereProd).measure_preimage
    (measurable_graph A r hA hr).nullMeasurableSet
  rw [comap_subtype_coe_apply (measurableSet_singleton (0 : E)).compl] at hp
  change mu (cone A r) = _ at hp
  rw [hp, graph_measure mu.toSphere (Module.finrank ℝ E - 1) A r hA hr,
    Nat.sub_add_cancel hdim]
  have hdcast : ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + 1 = (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hdim
  rw [hdcast]

/-- Cancellation of the dimension factor from the radial integral. -/
theorem dimension_cancel (N : ℕ) (hN : 0 < N) (a : ℝ) :
    (N : ℝ≥0∞) * ENNReal.ofReal (a / (N : ℝ)) = ENNReal.ofReal a := by
  rw [← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
  congr 1
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  field_simp

theorem scaled_cone_measure (mu : Measure E) [mu.IsAddHaarMeasure]
    (A : Set (Sphere E)) (r : Sphere E → Ioi (0 : ℝ))
    (hA : MeasurableSet A) (hr : Measurable r) :
    (Module.finrank ℝ E : ℝ≥0∞) * mu (cone A r) =
      ∫⁻ x in A, ENNReal.ofReal ((r x).1 ^ Module.finrank ℝ E) ∂mu.toSphere := by
  rw [cone_measure mu A r hA hr,
    ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
  apply lintegral_congr
  intro x
  exact dimension_cancel _ Module.finrank_pos _

theorem cone_one_measure (mu : Measure E) [mu.IsAddHaarMeasure]
    (A : Set (Sphere E)) (hA : MeasurableSet A) :
    (Module.finrank ℝ E : ℝ≥0∞) * mu (cone A (fun _ => ⟨1, by norm_num⟩)) = mu.toSphere A := by
  rw [scaled_cone_measure mu A _ hA measurable_const]
  simp

/-- The projective change-of-measure formula, proved from ambient Haar measure
and polar coordinates. It applies to every Borel set on the unit sphere. -/
theorem toSphere_image (mu : Measure E) [mu.IsAddHaarMeasure]
    (T : E ≃L[ℝ] E) (A : Set (Sphere E)) (hA : MeasurableSet A) :
    mu.toSphere (action T '' A) =
      ENNReal.ofReal |LinearMap.det (T : E →ₗ[ℝ] E)| *
        ∫⁻ x in A, ENNReal.ofReal (‖T x‖⁻¹ ^ Module.finrank ℝ E) ∂mu.toSphere := by
  rw [← cone_one_measure mu (action T '' A) (measurable_action_image T A hA),
    action_cone, mu.addHaar_image_continuousLinearEquiv]
  rw [mul_left_comm, scaled_cone_measure mu A (cutoff T) hA (cutoff_continuous T).measurable]
  rfl


/-- The same geometric measure change after normalizing total spherical mass. -/
theorem probability_image (mu : Measure E) [mu.IsAddHaarMeasure]
    (T : E ≃L[ℝ] E) (A : Set (Sphere E)) (hA : MeasurableSet A) :
    probability mu (action T '' A) =
      ENNReal.ofReal |LinearMap.det (T : E →ₗ[ℝ] E)| *
        ∫⁻ x in A, ENNReal.ofReal (‖T x‖⁻¹ ^ Module.finrank ℝ E) ∂probability mu := by
  unfold probability
  rw [Measure.smul_apply, smul_eq_mul, toSphere_image mu T A hA,
    Measure.restrict_smul, lintegral_smul_measure]
  exact mul_left_comm _ _ _

/-- The real-valued area formula for every measurable set. Its left-hand side
is the measure of an actual projective image; its right-hand side integrates
the density over the original fixed set. -/
theorem transformedArea_integral (mu : Measure E) [mu.IsAddHaarMeasure]
    (T : E ≃L[ℝ] E) (A : Set (Sphere E)) (hA : MeasurableSet A) :
    transformedArea mu A T = |LinearMap.det (T : E →ₗ[ℝ] E)| *
      ∫ x in A, ‖T x‖⁻¹ ^ Module.finrank ℝ E ∂probability mu := by
  let : CompactSpace (Sphere E) := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E) 1)
  have hf : Continuous (fun x : Sphere E => ‖T x‖⁻¹ ^ Module.finrank ℝ E) :=
    (continuous_subtype_val.comp (cutoff_continuous T)).pow _
  have hi : IntegrableOn (fun x : Sphere E => ‖T x‖⁻¹ ^ Module.finrank ℝ E) A
      (probability mu) :=
    (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).integrableOn
  have hn : ∀ x : Sphere E, 0 ≤ ‖T x‖⁻¹ ^ Module.finrank ℝ E :=
    fun x => pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _
  have heq := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)
  have hm : probability mu (action T '' A) = ENNReal.ofReal
      (|LinearMap.det (T : E →ₗ[ℝ] E)| *
        ∫ x in A, ‖T x‖⁻¹ ^ Module.finrank ℝ E ∂probability mu) := by
    rw [probability_image mu T A hA, ← heq, ENNReal.ofReal_mul (abs_nonneg _)]
  unfold transformedArea area Measure.real
  rw [hm, ENNReal.toReal_ofReal]
  exact mul_nonneg (abs_nonneg _) (integral_nonneg hn)


end ShadowVerification.Radial
#print axioms ShadowVerification.Radial.measurable_graph
#print axioms ShadowVerification.Radial.graph_measure
#print axioms ShadowVerification.Radial.cone_measure

#print axioms ShadowVerification.Radial.cone_as_image
#print axioms ShadowVerification.Radial.cutoff_continuous
#print axioms ShadowVerification.Radial.action_cone

#print axioms ShadowVerification.Radial.dimension_cancel
#print axioms ShadowVerification.Radial.scaled_cone_measure
#print axioms ShadowVerification.Radial.cone_one_measure
#print axioms ShadowVerification.Radial.toSphere_image

#print axioms ShadowVerification.Radial.probability_image
#print axioms ShadowVerification.Radial.transformedArea_integral

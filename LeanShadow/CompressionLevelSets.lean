import LeanShadow.AntipodalDensity
import LeanShadow.CompressionTail

/-! # The actual superlevel sets of the compression kernel

For an expanding transverse dilation, the kernel increases with the absolute
axial coordinate. Compactness therefore identifies every nonempty closed
superlevel set with a pair of opposite spherical balls. These geometric
identifications supply the input to the layer-cake density estimate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter Metric
open scoped Topology
namespace ShadowVerification.CompressionLevels
open Spherical Antipodal AntipodalDensity Compression CompressionJacobian CompressionTail

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def height (e x : Sphere E) : ℝ := |inner ℝ (e : E) (x : E)|

theorem height_continuous (e : Sphere E) : Continuous (height e) := by unfold height; fun_prop

theorem height_nonneg (e x : Sphere E) : 0 ≤ height e x := abs_nonneg _

theorem projection_norm_height (e x : Sphere E) : ‖axisProjection e (x : E)‖ = height e x := by
  rw [axisProjection_apply, norm_smul, Real.norm_eq_abs,
    mem_sphere_zero_iff_norm.mp e.property, mul_one]
  rfl

theorem perpendicular_norm_sq (e x : Sphere E) :
    ‖(x : E) - axisProjection e (x : E)‖ ^ 2 = 1 - height e x ^ 2 := by
  have h := projection_sq_sum e x
  rw [projection_norm_height] at h
  linarith

theorem height_le_one (e x : Sphere E) : height e x ≤ 1 := by
  have h := perpendicular_norm_sq e x
  nlinarith [sq_nonneg ‖(x : E) - axisProjection e (x : E)‖]

theorem distance_sq (e x : Sphere E) : dist x e ^ 2 = 2 - 2 * inner ℝ (e : E) (x : E) := by
  rw [Subtype.dist_eq, dist_eq_norm, norm_sub_sq_real,
    mem_sphere_zero_iff_norm.mp x.property, mem_sphere_zero_iff_norm.mp e.property,
    real_inner_comm (x : E) (e : E)]
  ring

theorem distance_antipode_sq (e x : Sphere E) :
    dist x (antipode e) ^ 2 = 2 + 2 * inner ℝ (e : E) (x : E) := by
  rw [distance_sq]
  change 2 - 2 * inner ℝ (-(e : E)) (x : E) = _
  rw [inner_neg_left]
  ring

/-- Opposite spherical balls are exactly an absolute-coordinate threshold. -/
theorem mem_doubleBall_iff_height (e x : Sphere E) (r : ℝ) (hr : 0 ≤ r) :
    x ∈ doubleBall e r ↔ 1 - r ^ 2 / 2 ≤ height e x := by
  have h₁ := distance_sq e x
  have h₂ := distance_antipode_sq e x
  have hd₁ := dist_nonneg (x := x) (y := e)
  have hd₂ := dist_nonneg (x := x) (y := antipode e)
  simp only [doubleBall, mem_union, mem_closedBall, height, abs_eq_max_neg, le_max_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (by nlinarith)
    · exact Or.inr (by nlinarith)
  · rintro (h | h)
    · exact Or.inl (by nlinarith)
    · exact Or.inr (by nlinarith)

theorem dilation_norm_height (e x : Sphere E) (s : ℝ) :
    ‖dilation e s (x : E)‖ ^ 2 = s ^ 2 + (1 - s ^ 2) * height e x ^ 2 := by
  rw [dilation_norm_sq, projection_norm_height, perpendicular_norm_sq]
  ring

/-- Outside a small double ball, the transverse component has a uniform
positive lower bound. -/
theorem perpendicular_lower_outside_doubleBall (e x : Sphere E) (r : ℝ)
    (hr : 0 < r) (hx : x ∉ doubleBall e r) :
    r / 2 ≤ ‖(x : E) - axisProjection e (x : E)‖ := by
  have hh : height e x < 1 - r ^ 2 / 2 :=
    lt_of_not_ge (fun h => hx ((mem_doubleBall_iff_height e x r hr.le).mpr h))
  have hsq := perpendicular_norm_sq e x
  have hh0 := height_nonneg e x
  have hh1 := height_le_one e x
  have hn := norm_nonneg ((x : E) - axisProjection e (x : E))
  nlinarith [sq_nonneg (1 - r), mul_nonneg (sub_nonneg.mpr hh.le) (add_nonneg hh0 (by nlinarith : 0 ≤ 1 - r ^ 2 / 2))]

variable [FiniteDimensional ℝ E] [Nontrivial E]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- At transverse expansion factors at least one, the kernel is monotone
in the absolute axial coordinate. -/
theorem kernel_mono_height (e x y : Sphere E) (s : ℝ) (hs : 1 ≤ s)
    (hxy : height e x ≤ height e y) : kernel e s x ≤ kernel e s y := by
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hx := dilation_norm_height e x s
  have hy := dilation_norm_height e y s
  have ha : height e x ^ 2 ≤ height e y ^ 2 := by nlinarith [height_nonneg e x, height_nonneg e y]
  have hnorm : ‖dilation e s (y : E)‖ ≤ ‖dilation e s (x : E)‖ := by
    nlinarith [norm_nonneg (dilation e s (x : E)), norm_nonneg (dilation e s (y : E)),
      mul_nonneg (by nlinarith : 0 ≤ s ^ 2 - 1) (sub_nonneg.mpr ha)]
  have hyn : 0 < ‖dilation e s (y : E)‖ := by
    rw [norm_pos_iff, ← dilationEquiv_coe e s hs0.ne']
    simpa only [ContinuousLinearEquiv.coe_coe, map_zero] using
      (dilationEquiv e s hs0.ne').injective.ne (unit_ne_zero y)
  unfold kernel
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) (inv_anti₀ hyn hnorm) _)
    (pow_nonneg hs0.le _)

variable [MeasurableSpace E] [BorelSpace E]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Every nonempty closed superlevel is an actual double ball, including
the possible radius-zero case. -/
theorem superlevel_doubleBall_data (e : Sphere E) (s u : ℝ) (hs : 1 ≤ s)
    (hne : {x : Sphere E | u ≤ kernel e s x}.Nonempty) :
    ∃ r ≥ 0, ∃ y : Sphere E, u ≤ kernel e s y ∧ r ^ 2 = 2 - 2 * height e y ∧
      {x : Sphere E | u ≤ kernel e s x} = doubleBall e r := by
  let : CompactSpace (Sphere E) := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E) 1)
  have hc : IsCompact {x : Sphere E | u ≤ kernel e s x} :=
    (isClosed_le continuous_const (kernel_continuous e s (zero_lt_one.trans_le hs))).isCompact
  obtain ⟨y, hy, hmin⟩ := hc.exists_isMinOn hne (height_continuous e).continuousOn
  let r := Real.sqrt (2 - 2 * height e y)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = 2 - 2 * height e y := Real.sq_sqrt (by linarith [height_le_one e y])
  refine ⟨r, hr, y, hy, hrsq, ?_⟩
  ext x
  rw [mem_doubleBall_iff_height e x r hr]
  constructor
  · intro hx
    have hm : height e y ≤ height e x := hmin hx
    linarith
  · intro hx
    have hheight : height e y ≤ height e x := by linarith
    exact hy.trans (kernel_mono_height e y x s hs hheight)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem superlevel_eq_doubleBall (e : Sphere E) (s u : ℝ) (hs : 1 ≤ s)
    (hne : {x : Sphere E | u ≤ kernel e s x}.Nonempty) :
    ∃ r ≥ 0, {x : Sphere E | u ≤ kernel e s x} = doubleBall e r := by
  obtain ⟨r, hr, _, _, _, heq⟩ := superlevel_doubleBall_data e s u hs hne
  exact ⟨r, hr, heq⟩

end ShadowVerification.CompressionLevels
#print axioms ShadowVerification.CompressionLevels.height_continuous
#print axioms ShadowVerification.CompressionLevels.height_nonneg
#print axioms ShadowVerification.CompressionLevels.projection_norm_height
#print axioms ShadowVerification.CompressionLevels.perpendicular_norm_sq
#print axioms ShadowVerification.CompressionLevels.height_le_one
#print axioms ShadowVerification.CompressionLevels.distance_sq
#print axioms ShadowVerification.CompressionLevels.distance_antipode_sq
#print axioms ShadowVerification.CompressionLevels.mem_doubleBall_iff_height
#print axioms ShadowVerification.CompressionLevels.dilation_norm_height
#print axioms ShadowVerification.CompressionLevels.perpendicular_lower_outside_doubleBall
#print axioms ShadowVerification.CompressionLevels.kernel_mono_height
#print axioms ShadowVerification.CompressionLevels.superlevel_doubleBall_data
#print axioms ShadowVerification.CompressionLevels.superlevel_eq_doubleBall

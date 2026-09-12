import LeanShadow.CompressionLevelSets
import LeanShadow.CompressionLayercake

/-! # Compression at a density-zero axis

The near-axis estimate uses layer cake and the exact double-ball superlevels.
The far-axis height is bounded by s^{-1} times a fixed constant. Together they
prove that actual compressed area tends to zero. Existence of a density-zero
axis is supplied by the spherical Besicovitch theorem, without an open-hole
or boundary-regularity assumption.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace ShadowVerification.CompressionConcentration
open Spherical Antipodal AntipodalDensity Compression CompressionJacobian CompressionTail CompressionLevels

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

/-- Density zero gives one relative-mass bound for all sufficiently small
double balls, including radius zero. -/
theorem small_doubleBall_mass_bound (A : Set (Sphere E))
    (hanti : IsAntipodal A) (e : Sphere E) (he : e ∉ A)
    (hd : Tendsto (fun r => probability mu (A ∩ doubleBall e r) / probability mu (doubleBall e r))
      (𝓝[>] 0) (𝓝 0)) (eps : ℝ) (heps : 0 < eps) :
    ∃ delta > 0, ∀ r, 0 ≤ r → r < delta →
      probability mu (A ∩ doubleBall e r) ≤ ENNReal.ofReal eps * probability mu (doubleBall e r) := by
  have hevent := hd.eventually (eventually_lt_nhds (ENNReal.ofReal_pos.mpr heps))
  obtain ⟨delta, hdelta, hsub⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp hevent
  refine ⟨delta, hdelta, ?_⟩
  intro r hr hrdelta
  by_cases hr0 : r = 0
  · subst r
    have he' : antipode e ∉ A := by
      intro h
      exact he (by simpa only [antipode_twice] using hanti _ h)
    have hz : A ∩ doubleBall e 0 = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      rcases hx with ⟨hx, hxball⟩
      simp only [doubleBall, closedBall_zero, mem_union, mem_singleton_iff] at hxball
      rcases hxball with rfl | rfl <;> contradiction
    rw [hz, measure_empty]
    exact bot_le
  · have hratio : probability mu (A ∩ doubleBall e r) / probability mu (doubleBall e r) ≤
        ENNReal.ofReal eps := (hsub ⟨lt_of_le_of_ne hr (Ne.symm hr0), hrdelta⟩).le
    exact (ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top)
      (Or.inl (measure_ne_top _ _))).mp hratio

omit [BorelSpace E] [mu.IsAddHaarMeasure] in
/-- High superlevels have the required small relative mass. This is the
geometric step linking density zero to the integral comparison. -/
theorem high_superlevel_mass_bound (A : Set (Sphere E)) (e : Sphere E)
    (eps delta : ℝ) (hdelta : 0 < delta)
    (hd : ∀ r, 0 ≤ r → r < delta → probability mu (A ∩ doubleBall e r) ≤
      ENNReal.ofReal eps * probability mu (doubleBall e r))
    (s u : ℝ) (hs : 1 ≤ s)
    (hu : s⁻¹ * (delta / 4)⁻¹ ^ Module.finrank ℝ E < u) :
    probability mu (A ∩ {x | u ≤ kernel e s x}) ≤
      ENNReal.ofReal eps * probability mu {x | u ≤ kernel e s x} := by
  by_cases hne : {x : Sphere E | u ≤ kernel e s x}.Nonempty
  · obtain ⟨r, hr, y, hy, hrsq, heq⟩ := superlevel_doubleBall_data e s u hs hne
    have hymem : y ∈ doubleBall e (delta / 2) := by
      by_contra hout
      have hperp := perpendicular_lower_outside_doubleBall e y (delta / 2) (by positivity) hout
      have hbound := kernel_le_away_axis e y s (delta / 4) (zero_lt_one.trans_le hs)
        (by positivity) (by linarith)
      linarith
    have hh := (mem_doubleBall_iff_height e y (delta / 2) (by positivity)).mp hymem
    have hrdelta : r < delta := by nlinarith
    rw [heq]
    exact hd r hr hrdelta
  · have hz := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hz]

/-- The full kernel integral over A vanishes at a density-zero axis. -/
theorem kernel_integral_tendsto_zero (A : Set (Sphere E))
    (hanti : IsAntipodal A) (e : Sphere E) (he : e ∉ A)
    (hd : Tendsto (fun r => probability mu (A ∩ doubleBall e r) / probability mu (doubleBall e r))
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun s => ∫ x in A, kernel e s x ∂probability mu) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact ha.trans_le (integral_nonneg (kernel_nonneg e s hs.le))
  · intro b hb
    obtain ⟨delta, hdelta, hsmall⟩ := small_doubleBall_mass_bound mu A hanti e he hd
      (b / 2) (by positivity)
    have hM : Tendsto (fun s : ℝ => s⁻¹ * (delta / 4)⁻¹ ^ Module.finrank ℝ E) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.mul_const ((delta / 4)⁻¹ ^ Module.finrank ℝ E)
    have hMsmall := hM.eventually (eventually_lt_nhds (show (0 : ℝ) < b / 2 by positivity))
    filter_upwards [eventually_ge_atTop (1 : ℝ), hMsmall] with s hs hMs
    have hs0 : 0 < s := zero_lt_one.trans_le hs
    have hbound := CompressionLayercake.integral_le_of_high_level_density (probability mu) A
      (kernel e s) (kernel_continuous e s hs0).measurable (kernel_integrable mu e s hs0)
      (kernel_nonneg e s hs0.le) (kernel_integral_one mu e s hs0) (b / 2)
      (s⁻¹ * (delta / 4)⁻¹ ^ Module.finrank ℝ E) (by positivity) (by positivity)
      (fun u hu => high_superlevel_mass_bound mu A e (b / 2) delta hdelta hsmall s u hs hu)
    linarith

/-- The limit concerns the previously constructed actual compression-area
function, with the square-root change of parameter fully accounted for. -/
theorem compressionArea_tendsto_zero (A : Set (Sphere E)) (hA : MeasurableSet A)
    (hanti : IsAntipodal A) (e : Sphere E) (he : e ∉ A)
    (hd : Tendsto (fun r => probability mu (A ∩ doubleBall e r) / probability mu (doubleBall e r))
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (compressionArea mu A e) atTop (𝓝 0) := by
  have h := (kernel_integral_tendsto_zero mu A hanti e he hd).comp Real.tendsto_sqrt_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [compressionArea_eq_transformedArea mu A hA e t ht]
  exact (transformedArea_kernel mu A hA e (Real.sqrt t) (Real.sqrt_pos.mpr ht)).symm

/-- Every Borel antipodal spherical set of area less than one has an actual
compression along which its area tends to zero. -/
theorem exists_zero_compression (A : Set (Sphere E)) (hA : MeasurableSet A)
    (hanti : IsAntipodal A) (hp : area mu A < 1) :
    ∃ e : Sphere E, Tendsto (compressionArea mu A e) atTop (𝓝 0) := by
  obtain ⟨e, he, hd⟩ := exists_doubleBall_density_zero mu A hA hanti hp
  exact ⟨e, compressionArea_tendsto_zero mu A hA hanti e he hd⟩

end ShadowVerification.CompressionConcentration
#print axioms ShadowVerification.CompressionConcentration.small_doubleBall_mass_bound
#print axioms ShadowVerification.CompressionConcentration.high_superlevel_mass_bound
#print axioms ShadowVerification.CompressionConcentration.kernel_integral_tendsto_zero
#print axioms ShadowVerification.CompressionConcentration.compressionArea_tendsto_zero
#print axioms ShadowVerification.CompressionConcentration.exists_zero_compression

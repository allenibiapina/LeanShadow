import LeanShadow.IncidenceAttainment
import Mathlib.Topology.Semicontinuity.Basic

/-! # Compactness of the actual feasible mass region

Both prescribed masses may vary. Compact incidence and density recovery
close the region of masses of Borel antipodal pointwise avoiding pairs.
This strengthens fixed-mass attainment and supplies the compact set needed
for the affine maximum argument for ordinary profile concavity.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.ProfileClosedness
open Spherical Antipodal Profile WeakIndicators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

def region : Set (ℝ × ℝ) :=
  {z | ∃ A B : Set (Sphere E), MeasurableSet A ∧ MeasurableSet B ∧
    IsAntipodal A ∧ IsAntipodal B ∧ Avoids A B ∧
    area mu A = z.1 ∧ area mu B = z.2}

theorem region_bounds {z : ℝ × ℝ} (hz : z ∈ region mu) :
    z ∈ Icc (0, 0) (1, 1) := by
  obtain ⟨A,B,_,_,_,_,_,hA,hB⟩ := hz
  exact ⟨⟨hA ▸ area_nonneg mu A, hB ▸ area_nonneg mu B⟩,
    ⟨hA ▸ area_le_one mu A, hB ▸ area_le_one mu B⟩⟩

theorem region_profile_bound {z : ℝ × ℝ} (hz : z ∈ region mu) :
    z.2 + profile mu z.1 ≤ 1 := by
  obtain ⟨A,B,hA,hB,ha,_,hAB,hmA,hmB⟩ := hz
  simpa only [hmA, hmB] using feasible_profile_bound mu A B hA hB ha hAB

theorem optimal_mem_region (hd : 2 < Module.finrank ℝ E)
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) : (p, 1 - profile mu p) ∈ region mu := by
  obtain ⟨A,B,h,_⟩ := IncidenceAttainment.exists_optimizer mu hd p hp.1 hp.2
  exact ⟨A,B,h.measurable_left,h.measurable_right,h.antipodal_left,
    h.antipodal_right,h.avoids,h.mass_left,h.mass_right⟩

set_option maxHeartbeats 800000 in
theorem region_closed (hd : 2 < Module.finrank ℝ E) : IsClosed (region mu) := by
  apply isSeqClosed_iff_isClosed.mp
  intro z w hz hw
  choose A B hA hB ha hb hAB hmA hmB using hz
  have hd' : 1 < Module.finrank ℝ E := by omega
  let I := OrthogonalIncidence.realization mu hd'
  obtain ⟨u,v,s,hs,hu,hv⟩ := exists_pair_weak_limits (probability mu) A B hA hB
  have hu0 := nonneg_ae (probability mu) (A ∘ s) (fun j => hA (s j)) u hu
  have hu1 := le_one_ae (probability mu) (A ∘ s) (fun j => hA (s j)) u hu
  have hv0 := nonneg_ae (probability mu) (B ∘ s) (fun j => hB (s j)) v hv
  have hv1 := le_one_ae (probability mu) (B ∘ s) (fun j => hB (s j)) v hv
  have hmu : (∫ x, u x ∂probability mu) = w.1 := by
    apply integral_eq_mass (probability mu) (A ∘ s) (fun j => hA (s j)) u hu
    change Tendsto (fun j => area mu (A (s j))) atTop (𝓝 w.1)
    simp only [hmA]
    exact hw.fst_nhds.comp hs.tendsto_atTop
  have hmv : (∫ x, v x ∂probability mu) = w.2 := by
    apply integral_eq_mass (probability mu) (B ∘ s) (fun j => hB (s j)) v hv
    change Tendsto (fun j => area mu (B (s j))) atTop (𝓝 w.2)
    simp only [hmB]
    exact hw.snd_nhds.comp hs.tendsto_atTop
  have hzuv : (∫ z, u z.1 * v z.2 ∂I.measure) = 0 := by
    rw [← Attainment.pairing mu I]
    exact HilbertWeak.inner_image_eq_zero (Attainment.operator mu I)
      (IncidenceAttainment.compact mu hd) _ _ u v hu hv 1 1
      (fun j => indicator_norm_le_one (probability mu) (A (s j)) (hA (s j)))
      (fun j => indicator_norm_le_one (probability mu) (B (s j)) (hB (s j)))
      (fun j => Attainment.pairing_zero_of_avoids mu I _ _ (hA (s j)) (hB (s j)) (hAB (s j)))
  have hzero := IncidenceRounding.positiveSupports_incidence_zero (probability mu)
    I.measure I.firstMarginal I.secondMarginal u v hu0 hv0 hzuv
  obtain ⟨D,C,hD,hC,hmD,hmC,hDC⟩ := IncidenceRecovery.pointwiseRecovery mu hd'
    _ _ (positiveSupport_measurable (probability mu) u)
    (positiveSupport_measurable (probability mu) v) hzero
  have hlargeD : w.1 ≤ area mu (symmetrize D) := by
    rw [← hmu]
    exact (integral_le_positiveSupport (probability mu) u hu0 hu1).trans
      (by change area mu {x | 0 < u x} ≤ _; rw [← hmD]; exact measureReal_mono (subset_symmetrize D))
  have hlargeC : w.2 ≤ area mu (symmetrize C) := by
    rw [← hmv]
    exact (integral_le_positiveSupport (probability mu) v hv0 hv1).trans
      (by change area mu {x | 0 < v x} ≤ _; rw [← hmC]; exact measureReal_mono (subset_symmetrize C))
  have hw0 : (0,0) ≤ w := ge_of_tendsto hw
    (Eventually.of_forall fun j => ⟨hmA j ▸ area_nonneg mu (A j), hmB j ▸ area_nonneg mu (B j)⟩)
  obtain ⟨D',hD'D,hD',haD',hmD'⟩ := AntipodalTrimming.exists_subset_area mu hd'
    (symmetrize D) (symmetrize_measurable D hD) (symmetrize_antipodal D) w.1 hw0.1 hlargeD
  obtain ⟨C',hC'C,hC',haC',hmC'⟩ := AntipodalTrimming.exists_subset_area mu hd'
    (symmetrize C) (symmetrize_measurable C hC) (symmetrize_antipodal C) w.2 hw0.2 hlargeC
  exact ⟨D',C',hD',hC',haD',haC',
    fun x hx y hy => Attainment.symmetrized_avoids D C hDC x (hD'D hx) y (hC'C hy),hmD',hmC'⟩

theorem region_compact (hd : 2 < Module.finrank ℝ E) : IsCompact (region mu) :=
  isCompact_Icc.of_isClosed_subset (region_closed mu hd) (fun _ h => region_bounds mu h)

theorem profile_monotone (hd : 1 < Module.finrank ℝ E) :
    MonotoneOn (profile mu) (Icc 0 1) := by
  intro p hp q hq hpq
  apply le_csInf (ProfileSequence.shadowValues_nonempty mu hd q hq.1 hq.2)
  rintro r ⟨A,hA,ha,hmA,hr⟩
  obtain ⟨D,hDA,hD,haD,hmD⟩ := AntipodalTrimming.exists_subset_area mu hd A hA ha p hp.1
    (by simpa only [hmA] using hpq)
  have hsub : shadow D ⊆ shadow A := by
    rintro y ⟨x,hx,hxy⟩
    exact ⟨x,hDA hx,hxy⟩
  calc
    profile mu p = profile mu (area mu D) := by rw [hmD]
    _ ≤ area mu (shadow D) := profile_le_shadow mu D hD haD
    _ ≤ area mu (shadow A) := measureReal_mono hsub
    _ = r := hr

end ShadowVerification.ProfileClosedness
#print axioms ShadowVerification.ProfileClosedness.region_bounds
#print axioms ShadowVerification.ProfileClosedness.region_profile_bound
#print axioms ShadowVerification.ProfileClosedness.optimal_mem_region
#print axioms ShadowVerification.ProfileClosedness.region_closed
#print axioms ShadowVerification.ProfileClosedness.region_compact
#print axioms ShadowVerification.ProfileClosedness.profile_monotone

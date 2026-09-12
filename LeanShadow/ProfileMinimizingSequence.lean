import LeanShadow.ShadowProfile
import LeanShadow.AntipodalTrimming
import Mathlib.Topology.Order.IsLUB

/-! # Actual fixed-mass competitors and minimizing avoiding pairs

The profile is the infimum of shadow outer measures of Borel antipodal sets.
Exact trimming first shows that this infimum is over a nonempty class.
Its minimizing sequence is paired with the already constructed Borel
antipodal avoiding partners, with exact complementary shadow masses.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace ShadowVerification.ProfileSequence
open Spherical Antipodal Profile

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

theorem shadowValues_nonempty (hd : 1 < Module.finrank ℝ E)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : (shadowValues mu p).Nonempty := by
  obtain ⟨A, hA, hanti, hm⟩ := AntipodalTrimming.exists_set_area mu hd p hp hp1
  exact ⟨area mu (shadow A), A, hA, hanti, hm, rfl⟩

theorem profile_bounds (hd : 1 < Module.finrank ℝ E)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ profile mu p ∧ profile mu p ≤ 1 := by
  obtain ⟨A, hA, hanti, hm⟩ := AntipodalTrimming.exists_set_area mu hd p hp hp1
  rw [← hm]
  exact ⟨profile_nonneg_at_competitor mu A hA hanti,
    profile_le_one_at_competitor mu A hA hanti⟩

/-- A minimizing sequence consists of actual Borel antipodal spherical sets. -/
theorem exists_minimizing_sequence (hd : 1 < Module.finrank ℝ E)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ A : ℕ → Set (Sphere E),
      (∀ j, MeasurableSet (A j) ∧ IsAntipodal (A j) ∧ area mu (A j) = p) ∧
      Antitone (fun j => area mu (shadow (A j))) ∧
      Tendsto (fun j => area mu (shadow (A j))) atTop (𝓝 (profile mu p)) := by
  obtain ⟨q, hqanti, hq, hmem⟩ := exists_seq_tendsto_sInf
    (shadowValues_nonempty mu hd p hp hp1) (shadowValues_bddBelow mu p)
  choose A hA ha hm hs using hmem
  refine ⟨A, fun j => ⟨hA j, ha j, hm j⟩, ?_, ?_⟩
  · simpa only [hs] using hqanti
  · simpa only [hs, profile] using hq

/-- Both sequences avoid pointwise before taking weak limits. -/
theorem exists_minimizing_pairs (hd : 1 < Module.finrank ℝ E)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ A B : ℕ → Set (Sphere E),
      (∀ j, MeasurableSet (A j) ∧ MeasurableSet (B j) ∧
        IsAntipodal (A j) ∧ IsAntipodal (B j) ∧ Avoids (A j) (B j) ∧
        area mu (A j) = p ∧ area mu (B j) = 1 - area mu (shadow (A j))) ∧
      Tendsto (fun j => area mu (shadow (A j))) atTop (𝓝 (profile mu p)) ∧
      Tendsto (fun j => area mu (B j)) atTop (𝓝 (1 - profile mu p)) := by
  obtain ⟨A, hA, _, ht⟩ := exists_minimizing_sequence mu hd p hp hp1
  refine ⟨A, fun j => avoidingPartner mu (A j), ?_, ht, ?_⟩
  · intro j
    exact ⟨(hA j).1, avoidingPartner_measurable mu (A j), (hA j).2.1,
      avoidingPartner_antipodal mu (A j), avoids_avoidingPartner mu (A j),
      (hA j).2.2, avoidingPartner_area mu (A j)⟩
  · simpa only [avoidingPartner_area] using tendsto_const_nhds.sub ht

/-- It suffices to recover a pointwise avoiding pair with at least the desired
masses. The proved symmetric trimming restores exact masses and optimality. -/
theorem optimizer_of_large_avoiding_pair (hd : 1 < Module.finrank ℝ E)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (D C : Set (Sphere E)) (hD : MeasurableSet D) (hC : MeasurableSet C)
    (hDa : IsAntipodal D) (hCa : IsAntipodal C) (havoid : Avoids D C)
    (hmD : p ≤ area mu D) (hmC : 1 - profile mu p ≤ area mu C) :
    ∃ A B : Set (Sphere E), IsOptimalPair mu p A B ∧ IsOptimizer mu p A := by
  obtain ⟨A, hAD, hA, hAa, hmA⟩ :=
    AntipodalTrimming.exists_subset_area mu hd D hD hDa p hp hmD
  obtain ⟨B, hBC, hB, hBa, hmB⟩ :=
    AntipodalTrimming.exists_subset_area mu hd C hC hCa (1 - profile mu p)
      (sub_nonneg.mpr (profile_bounds mu hd p hp hp1).2) hmC
  have hpair : IsOptimalPair mu p A B :=
    ⟨hA, hB, hAa, hBa, hmA, fun x hx y hy => havoid x (hAD hx) y (hBC hy), hmB⟩
  exact ⟨A, B, hpair, optimizer_of_optimalPair mu p A B hpair⟩

end ShadowVerification.ProfileSequence
#print axioms ShadowVerification.ProfileSequence.shadowValues_nonempty
#print axioms ShadowVerification.ProfileSequence.profile_bounds
#print axioms ShadowVerification.ProfileSequence.exists_minimizing_sequence
#print axioms ShadowVerification.ProfileSequence.exists_minimizing_pairs
#print axioms ShadowVerification.ProfileSequence.optimizer_of_large_avoiding_pair

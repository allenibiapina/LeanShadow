import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic

/-! # Inner measure and full-measure sigma-compact subsets

The inner measure is the supremum of measures of actual compact subsets.
All approximation is from inside the specified representative.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.CompactInner

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

def innerMeasure (ν : Measure X) (A : Set X) : ℝ≥0∞ :=
  ⨆ (K : Set X) (_ : K ⊆ A) (_ : IsCompact K), ν K

theorem innerMeasure_mono (ν : Measure X) {A B : Set X} (h : A ⊆ B) :
    innerMeasure ν A ≤ innerMeasure ν B := by
  apply iSup_le
  intro K
  apply iSup_le
  intro hK
  apply iSup_le
  intro hc
  exact le_iSup_of_le K (le_iSup_of_le (hK.trans h) (le_iSup_of_le hc le_rfl))

theorem innerMeasure_le (ν : Measure X) (A : Set X) : innerMeasure ν A ≤ ν A := by
  exact iSup_le fun K => iSup_le fun hK => iSup_le fun _ => measure_mono hK

theorem compact_le_innerMeasure (ν : Measure X) {K A : Set X}
    (hK : IsCompact K) (hKA : K ⊆ A) : ν K ≤ innerMeasure ν A :=
  le_iSup_of_le K (le_iSup_of_le hKA (le_iSup_of_le hK le_rfl))

theorem innerMeasure_eq (ν : Measure X) [Measure.InnerRegular ν]
    (A : Set X) (hA : NullMeasurableSet A ν) : innerMeasure ν A = ν A := by
  obtain ⟨B,hBA,hB,hBAe⟩ := hA.exists_measurable_subset_ae_eq
  apply le_antisymm (innerMeasure_le ν A)
  rw [← measure_congr hBAe,hB.measure_eq_iSup_isCompact]
  exact iSup_le fun K => iSup_le fun hK => iSup_le fun hc =>
    compact_le_innerMeasure ν hc (hK.trans hBA)

theorem measurable_le_innerMeasure (ν : Measure X) [Measure.InnerRegular ν]
    {B A : Set X} (hB : MeasurableSet B) (hBA : B ⊆ A) : ν B ≤ innerMeasure ν A := by
  rw [← innerMeasure_eq ν B hB.nullMeasurableSet]
  exact innerMeasure_mono ν hBA

variable [T2Space X] [OpensMeasurableSpace X]

theorem sigmaCompact_measurable {A : Set X} (hA : IsSigmaCompact A) : MeasurableSet A := by
  obtain ⟨K,hK,rfl⟩ := hA
  exact MeasurableSet.iUnion fun n => (hK n).measurableSet

theorem exists_sigmaCompact_subset_ae_eq (ν : Measure X) [IsFiniteMeasure ν]
    [Measure.InnerRegular ν] (A : Set X) (hA : NullMeasurableSet A ν) :
    ∃ B : Set X, B ⊆ A ∧ IsSigmaCompact B ∧ B =ᵐ[ν] A := by
  obtain ⟨C,hCA,hC,hCAe⟩ := hA.exists_measurable_subset_ae_eq
  have hex : ∀ n : ℕ, ∃ K : Set X, K ⊆ C ∧ IsCompact K ∧ ν (C \ K) < (n : ℝ≥0∞)⁻¹ := by
    intro n
    exact hC.exists_isCompact_sdiff_lt (measure_ne_top _ _) (by simp)
  choose K hKC hK hsmall using hex
  let B : Set X := ⋃ n, K n
  have hBC : B ⊆ C := iUnion_subset hKC
  have hB : IsSigmaCompact B := ⟨K,hK,rfl⟩
  have hzero : ν (C \ B) = 0 := by
    apply le_antisymm _ bot_le
    apply ge_of_tendsto ENNReal.tendsto_inv_nat_nhds_zero
    apply Eventually.of_forall
    intro n
    have hsub : C \ B ⊆ C \ K n := fun x hx =>
      ⟨hx.1,fun hn => hx.2 (mem_iUnion.mpr ⟨n,hn⟩)⟩
    exact (measure_mono hsub).trans (hsmall n).le
  have hBCae : B =ᵐ[ν] C := by
    rw [ae_eq_set]
    exact ⟨by rw [sdiff_eq_empty.mpr hBC,measure_empty],hzero⟩
  exact ⟨B,hBC.trans hCA,hB,hBCae.trans hCAe⟩

end ShadowVerification.CompactInner
#print axioms ShadowVerification.CompactInner.innerMeasure_mono
#print axioms ShadowVerification.CompactInner.innerMeasure_le
#print axioms ShadowVerification.CompactInner.compact_le_innerMeasure
#print axioms ShadowVerification.CompactInner.innerMeasure_eq
#print axioms ShadowVerification.CompactInner.measurable_le_innerMeasure
#print axioms ShadowVerification.CompactInner.sigmaCompact_measurable
#print axioms ShadowVerification.CompactInner.exists_sigmaCompact_subset_ae_eq

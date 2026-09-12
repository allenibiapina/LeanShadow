import LeanShadow.HilbertWeakCompactness

/-! # Compactness of a self-adjoint operator from compactness of its square

This supplies the last functional-analytic step of the manuscript's proposed
kernel proof of Funk compactness. It does not identify the Funk square kernel.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped Topology
namespace ShadowVerification.CompactSquare

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A weak limit stays in the same closed Hilbert ball. -/
theorem weak_limit_norm_le (u : ℕ → H) (v : H) (hu : HilbertWeak.Converges u v)
    (R : ℝ) (hR : ∀ j, ‖u j‖ ≤ R) : ‖v‖ ≤ R := by
  have hp : 0 ≤ R := (norm_nonneg (u 0)).trans (hR 0)
  have h := le_of_tendsto (hu v) (Filter.Eventually.of_forall fun j =>
    (real_inner_le_norm (u j) v).trans (mul_le_mul_of_nonneg_right (hR j) (norm_nonneg v)))
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg v]

variable [CompleteSpace H]

omit [CompleteSpace H] in
/-- The identity `‖T x‖² = ⟨x,T²x⟩` upgrades strong convergence under `T²`
to strong convergence under `T` along a bounded weakly convergent sequence. -/
theorem image_tendsto_of_square (T : H →L[ℝ] H) (hT : T.toLinearMap.IsSymmetric)
    (u : ℕ → H) (v : H) (hu : HilbertWeak.Converges u v)
    (R : ℝ) (hR : ∀ j, ‖u j‖ ≤ R)
    (ht : Tendsto (fun j => T (T (u j))) atTop (𝓝 (T (T v)))) :
    Tendsto (fun j => T (u j)) atTop (𝓝 (T v)) := by
  have hweak : HilbertWeak.Converges (fun j => u j - v) 0 := by
    intro z
    simpa only [inner_sub_left, sub_self, inner_zero_left] using (hu z).sub_const (inner ℝ v z)
  have hbound (j : ℕ) : ‖u j - v‖ ≤ R + ‖v‖ := by
    have h := norm_sub_le (u j) v
    linarith [hR j]
  have hstrong : Tendsto (fun j => T (T (u j - v))) atTop (𝓝 0) := by
    simpa only [map_sub, sub_self] using ht.sub_const (T (T v))
  have hp := HilbertWeak.inner_tendsto hweak hstrong (R + ‖v‖) hbound
  have heq (j : ℕ) : inner ℝ (u j - v) (T (T (u j - v))) = ‖T (u j) - T v‖ ^ 2 := by
    rw [← hT.apply_clm (u j - v) (T (u j - v)), real_inner_self_eq_norm_sq, map_sub]
  have hsq : Tendsto (fun j => ‖T (u j) - T v‖ ^ 2) atTop (𝓝 0) := by
    simpa only [heq, inner_zero_left] using hp
  have hn := (Real.continuous_sqrt.tendsto 0).comp hsq
  change Tendsto (fun j => Real.sqrt (‖T (u j) - T v‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at hn
  have hn' : Tendsto (fun j => ‖T (u j) - T v‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn'

/-- For a self-adjoint operator on a separable real Hilbert space,
compactness of its square implies compactness of the operator itself. -/
theorem compact_of_comp_self [TopologicalSpace.SeparableSpace H]
    (T : H →L[ℝ] H) (hT : T.toLinearMap.IsSymmetric)
    (hcompact : IsCompactOperator (T.comp T)) : IsCompactOperator T := by
  have hseq : IsSeqCompact (T '' closedBall (0 : H) 1) := by
    intro a ha
    choose u hu hTu using ha
    have hub (j : ℕ) : ‖u j‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hu j
    obtain ⟨v, s, hs, hv⟩ := HilbertWeak.exists_weak_subsequence u 1 hub
    obtain ⟨t, ht, hsq⟩ := HilbertWeak.exists_strong_image_subsequence (T.comp T) hcompact
      (u ∘ s) v hv 1 (fun j => hub (s j))
    have hvb := weak_limit_norm_le (u ∘ s) v hv 1 (fun j => hub (s j))
    refine ⟨T v, ⟨v, by simpa only [mem_closedBall, dist_zero_right] using hvb, rfl⟩,
      s ∘ t, hs.comp ht, ?_⟩
    have himg := image_tendsto_of_square T hT (u ∘ (s ∘ t)) v
      (HilbertWeak.subsequence hv t ht) 1 (fun j => hub (s (t j))) hsq
    change Tendsto (fun j => a (s (t j))) atTop (𝓝 (T v))
    simpa only [Function.comp_apply, hTu] using himg
  apply (isCompactOperator_iff_image_closedBall_subset_compact T.toLinearMap
    (show (0 : ℝ) < 1 by norm_num)).mpr
  exact ⟨T '' closedBall 0 1, hseq.isCompact, Subset.rfl⟩

end ShadowVerification.CompactSquare
#print axioms ShadowVerification.CompactSquare.weak_limit_norm_le
#print axioms ShadowVerification.CompactSquare.image_tendsto_of_square
#print axioms ShadowVerification.CompactSquare.compact_of_comp_self

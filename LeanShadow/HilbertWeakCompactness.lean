import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-! # The Hilbert-space compactness step in the direct method

Weak convergence is expressed by testing inner products. Sequential
Banach--Alaoglu and the Riesz representation theorem produce weak limits.
A compact operator then gives a strongly convergent image subsequence,
which permits passage to a bilinear incidence constraint.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped Topology
namespace ShadowVerification.HilbertWeak

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def Converges (u : ℕ → H) (v : H) : Prop :=
  ∀ z : H, Tendsto (fun j => inner ℝ (u j) z) atTop (𝓝 (inner ℝ v z))

theorem subsequence {u : ℕ → H} {v : H} (hu : Converges u v)
    (s : ℕ → ℕ) (hs : StrictMono s) : Converges (u ∘ s) v :=
  fun z => (hu z).comp hs.tendsto_atTop

variable [CompleteSpace H]

/-- Weak convergence tests every continuous linear functional. -/
theorem test_clm {u : ℕ → H} {v : H} (hu : Converges u v) (l : H →L[ℝ] ℝ) :
    Tendsto (fun j => l (u j)) atTop (𝓝 (l v)) := by
  have h := hu ((InnerProductSpace.toDual ℝ H).symm l)
  have he (x : H) : inner ℝ x ((InnerProductSpace.toDual ℝ H).symm l) = l x := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  simpa only [he] using h

/-- Sequential weak compactness of a bounded Hilbert-space sequence. -/
theorem exists_weak_subsequence [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H) (R : ℝ) (hR : ∀ j, ‖u j‖ ≤ R) :
    ∃ v : H, ∃ s : ℕ → ℕ, StrictMono s ∧ Converges (u ∘ s) v := by
  let d : ℕ → WeakDual ℝ H := fun j =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (u j))
  have hd (j : ℕ) : d j ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ H) R := by
    simpa only [mem_preimage, mem_closedBall, dist_zero_right, d,
      StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hR j
  obtain ⟨l, _, s, hs, ht⟩ := (WeakDual.isSeqCompact_closedBall ℝ H 0 R) hd
  refine ⟨(InnerProductSpace.toDual ℝ H).symm l.toStrongDual, s, hs, ?_⟩
  intro z
  have hz := ((WeakDual.eval_continuous z).tendsto l).comp ht
  change Tendsto (fun j => inner ℝ (u (s j)) z) atTop (𝓝 (l z)) at hz
  simpa only [Function.comp_apply, InnerProductSpace.toDual_symm_apply,
    WeakDual.toStrongDual_apply] using hz

/-- Two bounded sequences have weak limits along one common subsequence. -/
theorem exists_pair_weak_subsequence [TopologicalSpace.SeparableSpace H]
    (u v : ℕ → H) (R S : ℝ) (hu : ∀ j, ‖u j‖ ≤ R) (hv : ∀ j, ‖v j‖ ≤ S) :
    ∃ a b : H, ∃ s : ℕ → ℕ, StrictMono s ∧
      Converges (u ∘ s) a ∧ Converges (v ∘ s) b := by
  obtain ⟨a, s, hs, hsa⟩ := exists_weak_subsequence u R hu
  obtain ⟨b, t, ht, htb⟩ := exists_weak_subsequence (v ∘ s) S (fun j => hv (s j))
  exact ⟨a, b, s ∘ t, hs.comp ht, subsequence hsa t ht, htb⟩

/-- A compact operator turns a bounded weakly convergent sequence into a
strongly convergent subsequence with the expected image limit. -/
theorem exists_strong_image_subsequence (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (u : ℕ → H) (v : H) (hu : Converges u v) (R : ℝ) (hR : ∀ j, ‖u j‖ ≤ R) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ Tendsto (fun j => T (u (s j))) atTop (𝓝 (T v)) := by
  obtain ⟨K, hK, hTK⟩ := hT.image_closedBall_subset_compact (f := T.toLinearMap) R
  have hmem (j : ℕ) : T (u j) ∈ K :=
    hTK ⟨u j, by simpa only [mem_closedBall, dist_zero_right] using hR j, rfl⟩
  obtain ⟨w, _, s, hs, hw⟩ := hK.tendsto_subseq hmem
  have heq : w = T v := by
    apply ext_inner_right ℝ
    intro z
    have hweak := test_clm (subsequence hu s hs) ((innerSL ℝ z).comp T)
    have hstrong := ((innerSL ℝ z).continuous.tendsto w).comp hw
    have he := tendsto_nhds_unique hstrong hweak
    change inner ℝ z w = inner ℝ z (T v) at he
    calc
      inner ℝ w z = inner ℝ z w := real_inner_comm _ _
      _ = inner ℝ z (T v) := he
      _ = inner ℝ (T v) z := real_inner_comm _ _
  exact ⟨s, hs, heq ▸ hw⟩

omit [CompleteSpace H] in
/-- Bounded weak convergence in one factor and norm convergence in the other
are sufficient for convergence of their inner products. -/
theorem inner_tendsto {u v : ℕ → H} {a b : H}
    (hu : Converges u a) (hv : Tendsto v atTop (𝓝 b))
    (R : ℝ) (hR : ∀ j, ‖u j‖ ≤ R) :
    Tendsto (fun j => inner ℝ (u j) (v j)) atTop (𝓝 (inner ℝ a b)) := by
  have hzero : Tendsto (fun j => R * ‖v j - b‖) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := R)).mul ((hv.sub_const b).norm)
  have hdiff : Tendsto (fun j => inner ℝ (u j) (v j - b)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun j => (norm_inner_le_norm (u j) (v j - b)).trans
      (mul_le_mul_of_nonneg_right (hR j) (norm_nonneg _))) hzero
  have h := hdiff.add (hu b)
  simpa only [inner_sub_right, sub_add_cancel, zero_add] using h

/-- Compactness closes the zero-incidence constraint after extracting a
common weakly convergent subsequence. -/
theorem inner_image_eq_zero (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (u v : ℕ → H) (a b : H) (hu : Converges u a) (hv : Converges v b)
    (R S : ℝ) (hR : ∀ j, ‖u j‖ ≤ R) (hS : ∀ j, ‖v j‖ ≤ S)
    (hzero : ∀ j, inner ℝ (u j) (T (v j)) = 0) : inner ℝ a (T b) = 0 := by
  obtain ⟨s, hs, ht⟩ := exists_strong_image_subsequence T hT v b hv S hS
  have h := inner_tendsto (subsequence hu s hs) ht R (fun j => hR (s j))
  have hz : Tendsto (fun j => inner ℝ (u (s j)) (T (v (s j)))) atTop (𝓝 0) := by
    simp only [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique h hz

end ShadowVerification.HilbertWeak
#print axioms ShadowVerification.HilbertWeak.subsequence
#print axioms ShadowVerification.HilbertWeak.test_clm
#print axioms ShadowVerification.HilbertWeak.exists_weak_subsequence
#print axioms ShadowVerification.HilbertWeak.exists_pair_weak_subsequence
#print axioms ShadowVerification.HilbertWeak.exists_strong_image_subsequence
#print axioms ShadowVerification.HilbertWeak.inner_tendsto
#print axioms ShadowVerification.HilbertWeak.inner_image_eq_zero

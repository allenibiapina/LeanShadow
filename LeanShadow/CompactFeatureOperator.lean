import LeanShadow.CompactSelfAdjointSquare
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Compact operators obtained from a continuous family of Hilbert vectors

For a continuous map `k : X → H` on a compact finite measure space, the
operator `u ↦ (x ↦ ⟪u,k x⟫)` from `H` to `L²(X)` is compact. The proof
uses weak sequential compactness and dominated convergence for squared
norms. This supplies continuous-kernel compactness without assuming a
Hilbert--Schmidt theorem or a finite-rank approximation theorem.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace ShadowVerification.CompactFeature

variable {X H : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def continuousLinear (k : C(X,H)) : H →L[ℝ] C(X,ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨fun x => inner ℝ u (k x), by fun_prop⟩
      map_add' := by intros; ext; simp [inner_add_left]
      map_smul' := by intros; ext; simp [real_inner_smul_left] }
    ‖k‖ (fun u => by
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      intro x
      exact (norm_inner_le_norm u (k x)).trans
        (by nlinarith [k.norm_coe_le_norm x, norm_nonneg u]))

variable (mu : Measure X) [IsFiniteMeasure mu]

def operator (k : C(X,H)) : H →L[ℝ] Lp ℝ 2 mu :=
  (ContinuousMap.toLp 2 mu ℝ).comp (continuousLinear k)

theorem coe_ae (k : C(X,H)) (u : H) :
    (operator mu k u : X → ℝ) =ᵐ[mu] (fun x => inner ℝ u (k x)) :=
  ContinuousMap.coeFn_toLp mu (continuousLinear k u)

theorem norm_sq (k : C(X,H)) (u : H) :
    ‖operator mu k u‖ ^ 2 = ∫ x, (inner ℝ u (k x)) ^ 2 ∂mu := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_ae mu k u] with x hx
  simp [hx, pow_two]

/-- Weak convergence becomes pointwise convergence against every feature vector;
boundedness and finite measure upgrade this to strong L² convergence. -/
theorem weak_to_strong (k : C(X,H)) (u : ℕ → H) (v : H)
    (hu : HilbertWeak.Converges u v) (R : ℝ) (hR : ∀ j, ‖u j‖ ≤ R) :
    Tendsto (fun j => operator mu k (u j)) atTop (𝓝 (operator mu k v)) := by
  have hR0 : 0 ≤ R := (norm_nonneg (u 0)).trans (hR 0)
  let B : ℝ := (R + ‖v‖) * ‖k‖
  have hB : 0 ≤ B := mul_nonneg (by positivity) (norm_nonneg k)
  have hb (j : ℕ) (x : X) : |inner ℝ (u j - v) (k x)| ≤ B := by
    have hn : ‖u j - v‖ ≤ R + ‖v‖ := (norm_sub_le _ _).trans (by linarith [hR j])
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul hn (k.norm_coe_le_norm x) (norm_nonneg _) (by positivity))
  have ht : Tendsto (fun j => ∫ x, (inner ℝ (u j - v) (k x)) ^ 2 ∂mu)
      atTop (𝓝 (∫ _x : X, (0 : ℝ) ∂mu)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => B ^ 2)
    · intro j
      exact (show Continuous (fun x => (inner ℝ (u j - v) (k x)) ^ 2) by
        fun_prop).aestronglyMeasurable
    · exact integrable_const _
    · intro j
      exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [hb j x, abs_nonneg (inner ℝ (u j - v) (k x)),
          sq_abs (inner ℝ (u j - v) (k x))]
    · exact Eventually.of_forall fun x => by
        have h := ((hu (k x)).sub_const (inner ℝ v (k x))).pow 2
        simpa only [inner_sub_left, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h
  have hs : Tendsto (fun j => ‖operator mu k (u j) - operator mu k v‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [← norm_sq mu k, map_sub, integral_zero] using ht
  have hn := (Real.continuous_sqrt.tendsto 0).comp hs
  change Tendsto (fun j => Real.sqrt (‖operator mu k (u j) - operator mu k v‖ ^ 2))
    atTop (𝓝 (Real.sqrt 0)) at hn
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

/-- Compactness is a conclusion, derived from weak compactness of the Hilbert ball. -/
theorem compact [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (k : C(X,H)) :
    IsCompactOperator (operator mu k) := by
  have hseq : IsSeqCompact (operator mu k '' closedBall (0 : H) 1) := by
    intro a ha
    choose u hu hTu using ha
    have hub (j : ℕ) : ‖u j‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hu j
    obtain ⟨v, s, hs, hv⟩ := HilbertWeak.exists_weak_subsequence u 1 hub
    have hvb := CompactSquare.weak_limit_norm_le (u ∘ s) v hv 1 (fun j => hub (s j))
    refine ⟨operator mu k v,
      ⟨v, by simpa only [mem_closedBall, dist_zero_right] using hvb, rfl⟩, s, hs, ?_⟩
    change Tendsto (fun j => a (s j)) atTop (𝓝 (operator mu k v))
    simpa only [Function.comp_apply, hTu] using
      weak_to_strong mu k (u ∘ s) v hv 1 (fun j => hub (s j))
  apply (isCompactOperator_iff_image_closedBall_subset_compact (operator mu k).toLinearMap
    (show (0 : ℝ) < 1 by norm_num)).mpr
  exact ⟨_, hseq.isCompact, Subset.rfl⟩

end ShadowVerification.CompactFeature
#print axioms ShadowVerification.CompactFeature.coe_ae
#print axioms ShadowVerification.CompactFeature.norm_sq
#print axioms ShadowVerification.CompactFeature.weak_to_strong
#print axioms ShadowVerification.CompactFeature.compact

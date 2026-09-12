import LeanShadow.ProfileMinimizingSequence
import LeanShadow.CouplingOperator
import LeanShadow.CompactSelfAdjointSquare

/-! # The direct-method proof of attainment, with geometric inputs exposed

This file proves the passage from compact incidence to the actual optimal
shadow profile, including fractional weak limits, positive supports,
antipodal symmetrization and exact trimming.

This module isolates the geometric inputs as explicit hypotheses.
`OrthogonalIncidence` now constructs the spherical `IncidenceRealization`,
and `SphericalIncidenceOperator` supplies it to the theorems below.
Compactness of that concrete operator and `PointwiseRecovery` for its
measure remain necessary for unconditional attainment.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.Attainment
open Spherical Antipodal Profile WeakIndicators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

/-- Geometric data to be constructed for the spherical orthogonality operator.
The measure has spherical marginals and is concentrated on orthogonal pairs. -/
structure IncidenceRealization where
  measure : Measure (Sphere E × Sphere E)
  firstMarginal : MeasurePreserving Prod.fst measure (probability mu)
  secondMarginal : MeasurePreserving Prod.snd measure (probability mu)
  orthogonal : ∀ᵐ z ∂measure, inner ℝ (z.1 : E) (z.2 : E) = 0

/-- The operator is constructed from the incidence measure, not supplied. -/
noncomputable def operator (I : IncidenceRealization mu) :
    Lp ℝ 2 (probability mu) →L[ℝ] Lp ℝ 2 (probability mu) :=
  CouplingOperator.operator (probability mu) I.measure I.firstMarginal I.secondMarginal

omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [mu.IsAddHaarMeasure] in
theorem pairing (I : IncidenceRealization mu) (u v : Lp ℝ 2 (probability mu)) :
    inner ℝ u (operator mu I v) = ∫ z, u z.1 * v z.2 ∂I.measure :=
  CouplingOperator.pairing (probability mu) I.measure I.firstMarginal I.secondMarginal u v

/-- The precise conclusion needed from the density-point incidence lemma.
It is not true for arbitrary representatives without a geometric argument. -/
def PointwiseRecovery (rho : Measure (Sphere E × Sphere E)) : Prop :=
  ∀ D C : Set (Sphere E), MeasurableSet D → MeasurableSet C → rho (D ×ˢ C) = 0 →
    ∃ A B : Set (Sphere E), MeasurableSet A ∧ MeasurableSet B ∧
      area mu A = area mu D ∧ area mu B = area mu C ∧ Avoids A B

/-- Literal avoiding pairs have zero pairing for a realized incidence operator. -/
theorem pairing_zero_of_avoids (I : IncidenceRealization mu)
    (A B : Set (Sphere E)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Avoids A B) :
    inner ℝ (indicator (probability mu) A hA) ((operator mu I) (indicator (probability mu) B hB)) = 0 := by
  rw [pairing mu I, IncidenceRounding.indicator_product_integral (probability mu)
    I.measure I.firstMarginal I.secondMarginal A B hA hB]
  have hz := IncidenceRounding.incidence_zero_of_avoids I.measure
    (fun x y : Sphere E => inner ℝ (x : E) (y : E) = 0) I.orthogonal A B hAB
  simp only [measureReal_def, hz, ENNReal.toReal_zero]

set_option maxHeartbeats 800000 in
/-- Actual minimizing sequences yield fractional limits of the exact two
masses and zero incidence. Weak compactness is proved, not hypothesized. -/
theorem exists_fractional_pair (I : IncidenceRealization mu)
    (hcompact : IsCompactOperator (operator mu I))
    (hd : 1 < Module.finrank ℝ E) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ u v : Lp ℝ 2 (probability mu),
      (∀ᵐ x ∂probability mu, 0 ≤ u x ∧ u x ≤ 1) ∧
      (∀ᵐ x ∂probability mu, 0 ≤ v x ∧ v x ≤ 1) ∧
      (∫ x, u x ∂probability mu) = p ∧
      (∫ x, v x ∂probability mu) = 1 - profile mu p ∧
      (∫ z, u z.1 * v z.2 ∂I.measure) = 0 := by
  obtain ⟨A, B, hpair, _, hBt⟩ := ProfileSequence.exists_minimizing_pairs mu hd p hp hp1
  let hA := fun j => (hpair j).1
  let hB := fun j => (hpair j).2.1
  obtain ⟨u, v, s, hs, hu, hv⟩ := exists_pair_weak_limits (probability mu) A B hA hB
  have hu0 := nonneg_ae (probability mu) (A ∘ s) (fun j => hA (s j)) u hu
  have hu1 := le_one_ae (probability mu) (A ∘ s) (fun j => hA (s j)) u hu
  have hv0 := nonneg_ae (probability mu) (B ∘ s) (fun j => hB (s j)) v hv
  have hv1 := le_one_ae (probability mu) (B ∘ s) (fun j => hB (s j)) v hv
  refine ⟨u, v, hu0.and hu1, hv0.and hv1, ?_, ?_, ?_⟩
  · apply integral_eq_mass (probability mu) (A ∘ s) (fun j => hA (s j)) u hu p
    have hm (j : ℕ) : (probability mu).real (A (s j)) = p := (hpair (s j)).2.2.2.2.2.1
    simp only [Function.comp_apply, hm]
    exact tendsto_const_nhds
  · exact integral_eq_mass (probability mu) (B ∘ s) (fun j => hB (s j)) v hv _ (hBt.comp hs.tendsto_atTop)
  · rw [← pairing mu I]
    exact HilbertWeak.inner_image_eq_zero (operator mu I) hcompact _ _ u v hu hv 1 1
      (fun j => indicator_norm_le_one (probability mu) (A (s j)) (hA (s j)))
      (fun j => indicator_norm_le_one (probability mu) (B (s j)) (hB (s j)))
      (fun j => pairing_zero_of_avoids mu I (A (s j)) (B (s j)) (hA (s j)) (hB (s j))
        (hpair (s j)).2.2.2.2.1)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
/-- No antipodality of a chosen L² representative is needed: once its positive
supports have been repaired, symmetrizing the two sets preserves avoidance. -/
theorem symmetrized_avoids (A B : Set (Sphere E)) (hAB : Avoids A B) :
    Avoids (symmetrize A) (symmetrize B) := by
  apply avoids_symmetrize_right
  rw [avoids_iff_disjoint_shadow, shadow_symmetrize]
  exact (avoids_iff_disjoint_shadow A B).mp hAB

/-- The whole direct method is now a proved implication from the compact Funk
operator and the geometric density-point recovery lemma. -/
theorem exists_optimalPair_of_compact_incidence (I : IncidenceRealization mu)
    (hcompact : IsCompactOperator (operator mu I)) (hrecover : PointwiseRecovery mu I.measure)
    (hd : 1 < Module.finrank ℝ E) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ A B : Set (Sphere E), IsOptimalPair mu p A B ∧ IsOptimizer mu p A := by
  obtain ⟨u, v, hu, hv, hmu, hmv, hz⟩ := exists_fractional_pair mu I hcompact hd p hp hp1
  let D := {x | 0 < u x}
  let C := {x | 0 < v x}
  have hD : MeasurableSet D := positiveSupport_measurable (probability mu) u
  have hC : MeasurableSet C := positiveSupport_measurable (probability mu) v
  have hzero : I.measure (D ×ˢ C) = 0 :=
    IncidenceRounding.positiveSupports_incidence_zero (probability mu) I.measure
      I.firstMarginal I.secondMarginal u v (hu.mono fun _ h => h.1) (hv.mono fun _ h => h.1) hz
  obtain ⟨A, B, hA, hB, hAD, hBC, hAB⟩ := hrecover D C hD hC hzero
  apply ProfileSequence.optimizer_of_large_avoiding_pair mu hd p hp hp1
    (symmetrize A) (symmetrize B) (symmetrize_measurable A hA) (symmetrize_measurable B hB)
    (symmetrize_antipodal A) (symmetrize_antipodal B) (symmetrized_avoids A B hAB)
  · have h := integral_le_positiveSupport (probability mu) u
      (hu.mono fun _ h => h.1) (hu.mono fun _ h => h.2)
    rw [hmu] at h
    calc
      p ≤ area mu D := h
      _ = area mu A := hAD.symm
      _ ≤ area mu (symmetrize A) := measureReal_mono (subset_symmetrize A)
  · have h := integral_le_positiveSupport (probability mu) v
      (hv.mono fun _ h => h.1) (hv.mono fun _ h => h.2)
    rw [hmv] at h
    calc
      1 - profile mu p ≤ area mu C := h
      _ = area mu B := hBC.symm
      _ ≤ area mu (symmetrize B) := measureReal_mono (subset_symmetrize B)

set_option maxHeartbeats 800000 in
/-- The manuscript's kernel route needs compactness only of the square,
once exchange symmetry of the incidence measure has been established. -/
theorem exists_optimalPair_of_compact_square (I : IncidenceRealization mu)
    (hswap : MeasurePreserving Prod.swap I.measure I.measure)
    (hsquare : IsCompactOperator ((operator mu I).comp (operator mu I)))
    (hrecover : PointwiseRecovery mu I.measure)
    (hd : 1 < Module.finrank ℝ E) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ A B : Set (Sphere E), IsOptimalPair mu p A B ∧ IsOptimizer mu p A := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hsym : (operator mu I).toLinearMap.IsSymmetric :=
    CouplingOperator.symmetric (probability mu) I.measure I.firstMarginal I.secondMarginal hswap
  exact exists_optimalPair_of_compact_incidence mu I
    (CompactSquare.compact_of_comp_self (operator mu I) hsym hsquare) hrecover hd p hp hp1

omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [mu.IsAddHaarMeasure] in
/-- The zero-mass endpoint is attained without any incidence inputs. -/
theorem empty_optimizer : IsOptimizer mu 0 (∅ : Set (Sphere E)) := by
  have hanti : IsAntipodal (∅ : Set (Sphere E)) := by intro x hx; exact hx.elim
  have ha : area mu (∅ : Set (Sphere E)) = 0 := by simp [area]
  have hs : shadow (∅ : Set (Sphere E)) = ∅ := by ext y; simp [shadow]
  have hlo := profile_nonneg_at_competitor mu ∅ MeasurableSet.empty hanti
  have hhi := profile_le_shadow mu ∅ MeasurableSet.empty hanti
  rw [ha] at hlo hhi
  rw [hs, ha] at hhi
  exact ⟨MeasurableSet.empty, hanti, ha, by rw [hs, ha]; exact (le_antisymm hhi hlo).symm⟩

end ShadowVerification.Attainment
#print axioms ShadowVerification.Attainment.pairing_zero_of_avoids
#print axioms ShadowVerification.Attainment.exists_fractional_pair
#print axioms ShadowVerification.Attainment.symmetrized_avoids
#print axioms ShadowVerification.Attainment.exists_optimalPair_of_compact_incidence
#print axioms ShadowVerification.Attainment.empty_optimizer

#print axioms ShadowVerification.Attainment.pairing
#print axioms ShadowVerification.Attainment.exists_optimalPair_of_compact_square

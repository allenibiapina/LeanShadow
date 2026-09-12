import LeanShadow.OrthogonalFrame
import LeanShadow.SphericalDensityPoint
import LeanShadow.SphericalSingularKernel
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated

/-! # Measurable density representatives obtained from the orthogonal group

Use balls in the operator-norm metric of the compact orthogonal group.
Besicovitch differentiation applies to Haar measure after its embedding
in the finite-dimensional space of endomorphisms. Right translations are
isometries, so these density averages descend to measurable spherical
representatives. No local volume or submersion formula is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.HaarDensity
open Spherical OrthogonalHaar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

def lift (A : Set (Sphere E)) (x : Sphere E) : Set (OrthogonalHaar.Group E) :=
  (fun R => rotate R x) ⁻¹' A

omit [Nontrivial E] in
theorem lift_measurable (A : Set (Sphere E)) (hA : MeasurableSet A) (x : Sphere E) :
    MeasurableSet (lift A x) :=
  hA.preimage (rotate_continuous.comp (continuous_id.prodMk continuous_const)).measurable

def average (A : Set (Sphere E)) (x : Sphere E) (r : ℝ) : ℝ≥0∞ :=
  haar E (lift A x ∩ closedBall 1 r) / haar E (closedBall 1 r)

def representative (A : Set (Sphere E)) : Set (Sphere E) :=
  {x | Tendsto (fun j => average A x (SingularKernel.scale j)) atTop (𝓝 1)}

/-- Measurability follows by integrating the jointly measurable incidence indicator. -/
theorem average_measurable (A : Set (Sphere E)) (hA : MeasurableSet A) (r : ℝ) :
    Measurable (fun x => average A x r) := by
  have hrot : Measurable (fun z : Sphere E × OrthogonalHaar.Group E => rotate z.2 z.1) :=
    (rotate_continuous.comp continuous_swap).measurable
  have hset : MeasurableSet {z : Sphere E × OrthogonalHaar.Group E |
      rotate z.2 z.1 ∈ A ∧ z.2 ∈ closedBall 1 r} :=
    (hA.preimage hrot).inter (isClosed_closedBall.measurableSet.preimage measurable_snd)
  have hi := (measurable_const.indicator hset : Measurable
    (fun z : Sphere E × OrthogonalHaar.Group E =>
      {z : Sphere E × OrthogonalHaar.Group E |
        rotate z.2 z.1 ∈ A ∧ z.2 ∈ closedBall 1 r}.indicator (fun _ => (1 : ℝ≥0∞)) z )).lintegral_prod_right' (ν := haar E)
  have he (x : Sphere E) :
      (∫⁻ R, {z : Sphere E × OrthogonalHaar.Group E |
        rotate z.2 z.1 ∈ A ∧ z.2 ∈ closedBall 1 r}.indicator (fun _ => (1 : ℝ≥0∞)) (x,R) ∂haar E) =
      haar E (lift A x ∩ closedBall 1 r) := by
    change (∫⁻ R, (lift A x ∩ closedBall 1 r).indicator (fun _ => (1 : ℝ≥0∞)) R ∂haar E) = _
    rw [lintegral_indicator ((lift_measurable A hA x).inter isClosed_closedBall.measurableSet)]
    simp
  simp_rw [he] at hi
  exact hi.div measurable_const

theorem representative_measurable (A : Set (Sphere E)) (hA : MeasurableSet A) :
    MeasurableSet (representative A) :=
  measurableSet_tendsto (𝓝 (1 : ℝ≥0∞)) (fun j => average_measurable A hA (SingularKernel.scale j))

/-- Translating the averaging ball identifies the orbit average with a density ratio on the group. -/
theorem average_rotate (A : Set (Sphere E)) (hA : MeasurableSet A)
    (x : Sphere E) (S : OrthogonalHaar.Group E) (r : ℝ) :
    average A (rotate S x) r =
      haar E (lift A x ∩ closedBall S r) / haar E (closedBall S r) := by
  have hp : MeasurePreserving (fun R : OrthogonalHaar.Group E => R * S) (haar E) (haar E) :=
    ⟨(continuous_mul_const S).measurable, haar_map_right E S⟩
  have hb : (fun R : OrthogonalHaar.Group E => R * S) ⁻¹' closedBall S r = closedBall 1 r := by
    ext R
    simp only [mem_preimage, mem_closedBall]
    rw [show dist (R * S) S = dist R 1 by
      simpa only [one_mul] using OrthogonalFrame.dist_mul_right R 1 S]
  have hl : (fun R : OrthogonalHaar.Group E => R * S) ⁻¹' lift A x = lift A (rotate S x) := by
    ext R
    simp only [lift, mem_preimage, rotate_mul]
  rw [← hp.measure_preimage ((lift_measurable A hA x).inter isClosed_closedBall.measurableSet).nullMeasurableSet,
    ← hp.measure_preimage isClosed_closedBall.measurableSet.nullMeasurableSet, preimage_inter, hb, hl]
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
/-- Haar differentiation is obtained from the ambient finite-dimensional density theorem. -/
theorem ae_group_density (A : Set (OrthogonalHaar.Group E)) (hA : MeasurableSet A) :
    ∀ᵐ R ∂haar E, Tendsto
      (fun r => haar E (A ∩ closedBall R r) / haar E (closedBall R r)) (𝓝[>] 0)
      (𝓝 (A.indicator 1 R)) := by
  let j : OrthogonalHaar.Group E → (E →L[ℝ] E) := Subtype.val
  have hjc : Topology.IsClosedEmbedding j := isClosed_unitary.isClosedEmbedding_subtypeVal
  have hj : MeasurableEmbedding j := hjc.measurableEmbedding
  have himage : MeasurableSet (j '' A) := hj.measurableSet_image.mpr hA
  have hd := Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet ((haar E).map j) himage
  have hp := ae_of_ae_map hj.measurable.aemeasurable hd
  filter_upwards [hp] with R hR
  have he (r : ℝ) :
      ((haar E).map j) (j '' A ∩ closedBall (j R) r) /
        ((haar E).map j) (closedBall (j R) r) =
      haar E (A ∩ closedBall R r) / haar E (closedBall R r) := by
    rw [Measure.map_apply hj.measurable (himage.inter isClosed_closedBall.measurableSet),
      Measure.map_apply hj.measurable isClosed_closedBall.measurableSet,
      preimage_inter, preimage_image_eq A hj.injective]
    rfl
  have hm : j R ∈ j '' A ↔ R ∈ A := by
    simp only [mem_image, hj.injective.eq_iff, exists_eq_right]
  have hv : (j '' A).indicator (1 : (E →L[ℝ] E) → ℝ≥0∞) (j R) = A.indicator 1 R := by
    by_cases ha : R ∈ A
    · simp [indicator_of_mem ha, indicator_of_mem (hm.mpr ha)]
    · simp [indicator_of_notMem ha, indicator_of_notMem (mt hm.mp ha)]
  simpa only [he, hv] using hR

variable (mu : Measure E) [mu.IsAddHaarMeasure]

/-- The descended representative agrees with the original set almost everywhere. -/
theorem representative_ae (A : Set (Sphere E)) (hA : MeasurableSet A) (x : Sphere E) :
    representative A =ᵐ[probability mu] A := by
  have hd := ae_group_density (lift A x) (lift_measurable A hA x)
  have hs : Tendsto SingularKernel.scale atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨SingularKernel.scale_tendsto,
      Eventually.of_forall SingularKernel.scale_pos⟩
  have he : ∀ᵐ R ∂haar E, (rotate R x ∈ representative A ↔ rotate R x ∈ A) := by
    filter_upwards [hd] with R hR
    have ht := hR.comp hs
    simp_rw [← average_rotate A hA x R] at ht
    change Tendsto (fun j => average A (rotate R x) (SingularKernel.scale j)) atTop
      (𝓝 ((lift A x).indicator 1 R)) at ht
    by_cases hm : rotate R x ∈ A
    · have hl : R ∈ lift A x := hm
      simp only [indicator_of_mem hl, Pi.one_apply] at ht
      exact ⟨fun _ => hm, fun _ => ht⟩
    · have hl : R ∉ lift A x := hm
      simp only [indicator_of_notMem hl] at ht
      refine ⟨fun h => ?_, fun h => (hm h).elim⟩
      have hz : (1 : ℝ≥0∞) = 0 := tendsto_nhds_unique h ht
      exact (one_ne_zero hz).elim
  have hm : Measurable (fun R : OrthogonalHaar.Group E => rotate R x) :=
    (rotate_continuous.comp (continuous_id.prodMk continuous_const)).measurable
  rw [← SphericalRotation.orbit_map_probability mu x]
  have hP : MeasurableSet {y | y ∈ representative A ↔ y ∈ A} :=
    (representative_measurable A hA).iff hA
  have hf := (ae_map_iff hm.aemeasurable hP).mpr he
  filter_upwards [hf] with y hy
  exact propext hy

theorem representative_area (A : Set (Sphere E)) (hA : MeasurableSet A) (x : Sphere E) :
    area mu (representative A) = area mu A := by
  unfold area Measure.real
  rw [measure_congr (representative_ae mu A hA x)]

end ShadowVerification.HaarDensity
#print axioms ShadowVerification.HaarDensity.lift_measurable
#print axioms ShadowVerification.HaarDensity.average_measurable
#print axioms ShadowVerification.HaarDensity.representative_measurable
#print axioms ShadowVerification.HaarDensity.average_rotate
#print axioms ShadowVerification.HaarDensity.ae_group_density
#print axioms ShadowVerification.HaarDensity.representative_ae
#print axioms ShadowVerification.HaarDensity.representative_area

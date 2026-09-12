import LeanShadow.ContinuousKernelOperator
import LeanShadow.KernelMeasureBound
import LeanShadow.SphericalIncidenceOperator

/-! # Continuous truncations of the proposed spherical square kernel

The singular kernel is multiplied by `s/(s+delta)`, where
`s = max 0 (1 - inner(x,y)^2)`. These are actual continuous
kernels and actual compact L² operators. Rotation invariance proves that
every row has the same integral, and symmetry gives the column identity.
This module does not assert that the untruncated kernel represents F².
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace ShadowVerification.SphericalKernel
open Spherical OrthogonalHaar SphericalRotation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

/-- Joint rotational invariance makes every row integral identical. -/
theorem row_integral_eq (k : Sphere E × Sphere E → ℝ) (hk : Measurable k)
    (hi : ∀ R : OrthogonalHaar.Group E, ∀ x y : Sphere E,
      k (rotate R x, rotate R y) = k (x,y)) (x z : Sphere E) :
    (∫ y, k (x,y) ∂probability mu) = ∫ y, k (z,y) ∂probability mu := by
  obtain ⟨R, hR, _⟩ := exists_exchange x z
  have hf : StronglyMeasurable (fun y : Sphere E => k (z,y)) :=
    (hk.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable
  have h := integral_map_of_stronglyMeasurable (μ := probability mu)
    (measurePreserving_rotate mu R).measurable hf
  rw [(measurePreserving_rotate mu R).map_eq] at h
  calc
    (∫ y, k (x,y) ∂probability mu) = ∫ y, k (z,rotate R y) ∂probability mu := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by simpa only [hR] using (hi R x y).symm
    _ = ∫ y, k (z,y) ∂probability mu := h.symm

/-- Integrability of one row propagates to every row by a measure-preserving rotation. -/
theorem row_integrable (k : Sphere E × Sphere E → ℝ)
    (hi : ∀ R : OrthogonalHaar.Group E, ∀ x y : Sphere E,
      k (rotate R x, rotate R y) = k (x,y)) (z : Sphere E)
    (hz : Integrable (fun y => k (z,y)) (probability mu)) (x : Sphere E) :
    Integrable (fun y => k (x,y)) (probability mu) := by
  obtain ⟨R, hR, _⟩ := exists_exchange x z
  have h := (measurePreserving_rotate mu R).integrable_comp_of_integrable hz
  have he : (fun y => k (z,y)) ∘ rotate R = (fun y => k (x,y)) := by
    funext y
    simpa only [Function.comp_apply, hR] using hi R x y
  rwa [he] at h

def gap (z : Sphere E × Sphere E) : ℝ :=
  max 0 (1 - (inner ℝ (z.1 : E) (z.2 : E)) ^ 2)

def cutoff (beta delta : ℝ) (z : Sphere E × Sphere E) : ℝ :=
  beta * Real.sqrt (gap z) / (gap z + delta)

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem cutoff_continuous (beta delta : ℝ) (hd : 0 < delta) :
    Continuous (cutoff (E := E) beta delta) := by
  have hg : Continuous (gap (E := E)) := by unfold gap; fun_prop
  exact (continuous_const.mul (Real.continuous_sqrt.comp hg)).div
    (hg.add continuous_const) (fun z => (add_pos_of_nonneg_of_pos (le_max_left _ _) hd).ne')

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem cutoff_nonneg (beta delta : ℝ) (hb : 0 ≤ beta) (hd : 0 < delta)
    (z : Sphere E × Sphere E) : 0 ≤ cutoff beta delta z :=
  div_nonneg (mul_nonneg hb (Real.sqrt_nonneg _))
    (add_nonneg (le_max_left _ _) hd.le)

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem cutoff_symm (beta delta : ℝ) (x y : Sphere E) :
    cutoff beta delta (x,y) = cutoff beta delta (y,x) := by
  simp only [cutoff, gap, real_inner_comm (x : E) (y : E)]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem cutoff_invariant (beta delta : ℝ) (R : OrthogonalHaar.Group E) (x y : Sphere E) :
    cutoff beta delta (rotate R x,rotate R y) = cutoff beta delta (x,y) := by
  simp only [cutoff, gap, rotate_inner]

def continuousCutoff (beta delta : ℝ) (hd : 0 < delta) : C(Sphere E × Sphere E,ℝ) :=
  ⟨cutoff beta delta, cutoff_continuous beta delta hd⟩

def operator (beta delta : ℝ) (hd : 0 < delta) :
    Lp ℝ 2 (probability mu) →L[ℝ] Lp ℝ 2 (probability mu) :=
  ContinuousKernel.operator (probability mu) (probability mu) (continuousCutoff beta delta hd)

theorem compact (beta delta : ℝ) (hd : 0 < delta) : IsCompactOperator (operator mu beta delta hd) :=
  ContinuousKernel.compact _ _ _

theorem pairing (beta delta : ℝ) (hd : 0 < delta) (u v : Lp ℝ 2 (probability mu)) :
    inner ℝ u (operator mu beta delta hd v) = ∫ z : Sphere E × Sphere E,
      cutoff beta delta z * (u z.1 * v z.2) ∂(probability mu).prod (probability mu) :=
  ContinuousKernel.pairing _ _ _ u v

theorem cutoff_row_integrable (beta delta : ℝ) (hd : 0 < delta) (x : Sphere E) :
    Integrable (fun y => cutoff beta delta (x,y)) (probability mu) :=
  memLp_one_iff_integrable.mp
    (((continuousCutoff beta delta hd).curry x).memLp ℝ (p := 1) (μ := probability mu))

theorem cutoff_row_eq (beta delta : ℝ) (hd : 0 < delta) (x z : Sphere E) :
    (∫ y, cutoff beta delta (x,y) ∂probability mu) =
      ∫ y, cutoff beta delta (z,y) ∂probability mu :=
  row_integral_eq mu _ (cutoff_continuous beta delta hd).measurable (cutoff_invariant beta delta) x z

/-- The compact truncation operator is controlled by its common row mass. -/
theorem norm_le_row (beta delta : ℝ) (hb : 0 ≤ beta) (hd : 0 < delta) (x : Sphere E) :
    ‖operator mu beta delta hd‖ ≤ ∫ y, cutoff beta delta (x,y) ∂probability mu := by
  apply KernelMeasure.norm_le (probability mu) (cutoff beta delta)
    (cutoff_continuous beta delta hd).measurable (cutoff_nonneg beta delta hb hd) _
    (integral_nonneg fun y => cutoff_nonneg beta delta hb hd (x,y))
    (cutoff_row_integrable mu beta delta hd)
  · intro y
    simp_rw [cutoff_symm beta delta _ y]
    exact cutoff_row_integrable mu beta delta hd y
  · intro z
    exact cutoff_row_eq mu beta delta hd z x
  · intro z
    simp_rw [cutoff_symm beta delta _ z]
    exact cutoff_row_eq mu beta delta hd z x
  · exact pairing mu beta delta hd

end ShadowVerification.SphericalKernel
#print axioms ShadowVerification.SphericalKernel.row_integral_eq
#print axioms ShadowVerification.SphericalKernel.cutoff_continuous
#print axioms ShadowVerification.SphericalKernel.cutoff_nonneg
#print axioms ShadowVerification.SphericalKernel.cutoff_symm
#print axioms ShadowVerification.SphericalKernel.cutoff_invariant
#print axioms ShadowVerification.SphericalKernel.compact
#print axioms ShadowVerification.SphericalKernel.pairing
#print axioms ShadowVerification.SphericalKernel.cutoff_row_integrable
#print axioms ShadowVerification.SphericalKernel.cutoff_row_eq
#print axioms ShadowVerification.SphericalKernel.norm_le_row
#print axioms ShadowVerification.SphericalKernel.row_integrable

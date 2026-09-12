import LeanShadow.SphericalRotation
import LeanShadow.AttainmentReduction

/-! # Construction of spherical orthogonality incidence

Rotate a fixed orthonormal pair by normalized Haar measure. The resulting
probability measure has the prescribed spherical marginals, is concentrated
on orthogonal pairs, and is unchanged by exchanging its coordinates.
The final definition fills every field of `Attainment.IncidenceRealization`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.OrthogonalIncidence
open Spherical OrthogonalHaar SphericalRotation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

def frame (x y : Sphere E) (R : OrthogonalHaar.Group E) : Sphere E × Sphere E :=
  (rotate R x, rotate R y)

omit [Nontrivial E] in
theorem frame_continuous (x y : Sphere E) : Continuous (frame x y) :=
  (rotate_continuous.comp (continuous_id.prodMk continuous_const)).prodMk
    (rotate_continuous.comp (continuous_id.prodMk continuous_const))

variable [MeasurableSpace E] [BorelSpace E]

def measure (x y : Sphere E) : Measure (Sphere E × Sphere E) :=
  (haar E).map (frame x y)

instance incidenceProbability (x y : Sphere E) : IsProbabilityMeasure (measure x y) :=
  Measure.isProbabilityMeasure_map (frame_continuous x y).measurable.aemeasurable

/-- Every sampled frame is orthogonal; the resulting measure is supported there. -/
theorem orthogonal_ae (x y : Sphere E) (hxy : inner ℝ (x : E) (y : E) = 0) :
    ∀ᵐ z ∂measure x y, inner ℝ (z.1 : E) (z.2 : E) = 0 := by
  apply (ae_map_iff (frame_continuous x y).measurable.aemeasurable
    (isClosed_eq (by fun_prop) continuous_const).measurableSet).mpr
  exact Filter.Eventually.of_forall (fun R => (rotate_inner R x y).trans hxy)

/-- Exchange symmetry follows by right multiplication by a reflection. -/
theorem measurePreserving_swap (x y : Sphere E) :
    MeasurePreserving Prod.swap (measure x y) (measure x y) := by
  refine ⟨measurable_swap, ?_⟩
  obtain ⟨S, hx, hy⟩ := exists_exchange x y
  unfold measure
  rw [Measure.map_map measurable_swap (frame_continuous x y).measurable]
  have heq : Prod.swap ∘ frame x y = frame x y ∘ (fun R => R * S) := by
    funext R
    simp only [Function.comp_apply, frame, Prod.swap, rotate_mul, hx, hy]
  rw [heq, ← Measure.map_map (frame_continuous x y).measurable
    (continuous_mul_const S).measurable, haar_map_right]

/-- Simultaneous rotation of the two coordinates preserves the incidence law. -/
theorem measurePreserving_diagonal (x y : Sphere E) (S : OrthogonalHaar.Group E) :
    MeasurePreserving (fun z : Sphere E × Sphere E => (rotate S z.1, rotate S z.2))
      (measure x y) (measure x y) := by
  have hm : Measurable (fun z : Sphere E × Sphere E => (rotate S z.1, rotate S z.2)) :=
    ((rotate_continuous.comp (continuous_const.prodMk continuous_fst)).prodMk
      (rotate_continuous.comp (continuous_const.prodMk continuous_snd))).measurable
  refine ⟨hm, ?_⟩
  unfold measure
  rw [Measure.map_map hm (frame_continuous x y).measurable]
  change (haar E).map (frame x y ∘ (fun R => S * R)) = (haar E).map (frame x y)
  rw [← Measure.map_map (frame_continuous x y).measurable
    (continuous_const_mul S).measurable, map_mul_left_eq_self]

variable (mu : Measure E) [mu.IsAddHaarMeasure]

theorem firstMarginal (x y : Sphere E) :
    MeasurePreserving Prod.fst (measure x y) (probability mu) := by
  refine ⟨measurable_fst, ?_⟩
  rw [measure, Measure.map_map measurable_fst (frame_continuous x y).measurable]
  exact orbit_map_probability mu x

theorem secondMarginal (x y : Sphere E) :
    MeasurePreserving Prod.snd (measure x y) (probability mu) := by
  refine ⟨measurable_snd, ?_⟩
  rw [measure, Measure.map_map measurable_snd (frame_continuous x y).measurable]
  exact orbit_map_probability mu y

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- In dimension at least two an orthonormal pair is obtained from a basis. -/
theorem exists_orthogonal_pair (hd : 1 < Module.finrank ℝ E) :
    ∃ x y : Sphere E, inner ℝ (x : E) (y : E) = 0 := by
  let b := stdOrthonormalBasis ℝ E
  let i : Fin (Module.finrank ℝ E) := ⟨0, by omega⟩
  let j : Fin (Module.finrank ℝ E) := ⟨1, hd⟩
  refine ⟨⟨b i, mem_sphere_zero_iff_norm.mpr (b.norm_eq_one i)⟩,
    ⟨b j, mem_sphere_zero_iff_norm.mpr (b.norm_eq_one j)⟩, ?_⟩
  exact b.inner_eq_zero (by simp [i, j])

def firstPoint (hd : 1 < Module.finrank ℝ E) : Sphere E :=
  (exists_orthogonal_pair hd).choose

def secondPoint (hd : 1 < Module.finrank ℝ E) : Sphere E :=
  (exists_orthogonal_pair hd).choose_spec.choose

/-- The orthogonality incidence measure is now constructed, with no incidence hypotheses. -/
def realization (hd : 1 < Module.finrank ℝ E) : Attainment.IncidenceRealization mu where
  measure := measure (firstPoint hd) (secondPoint hd)
  firstMarginal := firstMarginal mu _ _
  secondMarginal := secondMarginal mu _ _
  orthogonal := orthogonal_ae _ _ (exists_orthogonal_pair hd).choose_spec.choose_spec

theorem realization_swap (hd : 1 < Module.finrank ℝ E) :
    MeasurePreserving Prod.swap (realization mu hd).measure (realization mu hd).measure :=
  measurePreserving_swap _ _

end ShadowVerification.OrthogonalIncidence
#print axioms ShadowVerification.OrthogonalIncidence.frame_continuous
#print axioms ShadowVerification.OrthogonalIncidence.orthogonal_ae
#print axioms ShadowVerification.OrthogonalIncidence.measurePreserving_swap
#print axioms ShadowVerification.OrthogonalIncidence.measurePreserving_diagonal
#print axioms ShadowVerification.OrthogonalIncidence.firstMarginal
#print axioms ShadowVerification.OrthogonalIncidence.secondMarginal
#print axioms ShadowVerification.OrthogonalIncidence.exists_orthogonal_pair
#print axioms ShadowVerification.OrthogonalIncidence.realization_swap

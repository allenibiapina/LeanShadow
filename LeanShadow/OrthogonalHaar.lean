import LeanShadow.InvariantArea
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! # Normalized Haar measure on the real orthogonal group

We realize the orthogonal group as the unitary elements of the real algebra
of continuous linear endomorphisms. Compactness follows from closedness and
the operator-norm bound one. Haar measure is normalized on the whole group.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.OrthogonalHaar
open Spherical

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

abbrev Group := unitary (E →L[ℝ] E)

instance groupCompact : CompactSpace (Group E) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_iff_isClosed_bounded).mpr
  refine ⟨isClosed_unitary, ?_⟩
  exact (isBounded_iff_forall_norm_le).mpr ⟨1, fun u hu =>
    le_of_eq (CStarRing.norm_of_mem_unitary hu)⟩

instance groupMeasurableSpace : MeasurableSpace (Group E) := borel (Group E)
instance groupBorelSpace : BorelSpace (Group E) := ⟨rfl⟩

noncomputable def haar : Measure (Group E) :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (Group E))

instance haarProbability : IsProbabilityMeasure (haar E) := by
  constructor
  exact Measure.haarMeasure_self

instance haarLeftInvariant : (haar E).IsMulLeftInvariant := by
  unfold haar
  infer_instance

instance haarIsHaar : (haar E).IsHaarMeasure := by
  unfold haar
  infer_instance

/-- Normalization and uniqueness of Haar measure imply right invariance. -/
theorem haar_map_right (R : Group E) : (haar E).map (· * R) = haar E := by
  have hm : Measurable (fun U : Group E => U * R) := (continuous_mul_const R).measurable
  let : IsProbabilityMeasure ((haar E).map (· * R)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

instance haarRightInvariant : (haar E).IsMulRightInvariant := ⟨haar_map_right E⟩

variable {E}
omit [Nontrivial E]

/-- Orthogonal transformations act on the actual unit sphere without normalization. -/
noncomputable def rotate (R : Group E) (x : Sphere E) : Sphere E :=
  ⟨(R : E →L[ℝ] E) x, by
    rw [mem_sphere_zero_iff_norm, Unitary.norm_map]
    exact mem_sphere_zero_iff_norm.mp x.property⟩

theorem rotate_mul (R S : Group E) (x : Sphere E) :
    rotate (R * S) x = rotate R (rotate S x) := rfl

theorem rotate_continuous : Continuous (fun z : Group E × Sphere E => rotate z.1 z.2) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).clm_apply
    (continuous_subtype_val.comp continuous_snd)

theorem rotate_inner (R : Group E) (x y : Sphere E) :
    inner ℝ (rotate R x : E) (rotate R y : E) = inner ℝ (x : E) (y : E) :=
  Unitary.inner_map_map R x y

/-- A reflection exchanges any two vectors of equal norm, including equal vectors. -/
theorem exists_exchange (x y : Sphere E) :
    ∃ R : Group E, rotate R x = y ∧ rotate R y = x := by
  let L := (ℝ ∙ ((x : E) - (y : E)))ᗮ.reflection
  let R : Group E := Unitary.linearIsometryEquiv.symm L
  have hn : ‖(x : E)‖ = ‖(y : E)‖ := by
    rw [mem_sphere_zero_iff_norm.mp x.property, mem_sphere_zero_iff_norm.mp y.property]
  have hx : L x = (y : E) := Submodule.reflection_sub hn
  refine ⟨R, Subtype.ext hx, Subtype.ext ?_⟩
  change L y = (x : E)
  rw [← hx]
  exact Submodule.reflection_reflection _ _

end ShadowVerification.OrthogonalHaar
#print axioms ShadowVerification.OrthogonalHaar.haar_map_right
#print axioms ShadowVerification.OrthogonalHaar.rotate_mul
#print axioms ShadowVerification.OrthogonalHaar.rotate_continuous
#print axioms ShadowVerification.OrthogonalHaar.rotate_inner
#print axioms ShadowVerification.OrthogonalHaar.exists_exchange

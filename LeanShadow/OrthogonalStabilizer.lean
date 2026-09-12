import LeanShadow.OrthogonalFrame
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # The compact stabilizer of an axis and its normalized Haar measure -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.AxisStabilizer
open Spherical OrthogonalHaar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

omit [Nontrivial E] in
theorem rotate_one (x : Sphere E) : rotate (1 : OrthogonalHaar.Group E) x = x := by
  apply Subtype.ext
  rfl

def subgroup (x : Sphere E) : Subgroup (OrthogonalHaar.Group E) where
  carrier := {R | rotate R x = x}
  one_mem' := rotate_one x
  mul_mem' := by
    intro R S hR hS
    change rotate (R * S) x = x
    rw [rotate_mul, hS, hR]
  inv_mem' := by
    intro R hR
    change rotate R⁻¹ x = x
    rw [← hR, ← rotate_mul, inv_mul_cancel, rotate_one]
    exact hR.symm

omit [Nontrivial E] in
theorem subgroup_closed (x : Sphere E) : IsClosed (subgroup x : Set (OrthogonalHaar.Group E)) :=
  isClosed_eq (rotate_continuous.comp (continuous_id.prodMk continuous_const)) continuous_const

instance stabilizerCompact (x : Sphere E) : CompactSpace (subgroup x) :=
  isCompact_iff_compactSpace.mp (subgroup_closed x).isCompact

instance stabilizerMeasurable (x : Sphere E) : MeasurableSpace (subgroup x) := borel (subgroup x)
instance stabilizerBorel (x : Sphere E) : BorelSpace (subgroup x) := ⟨rfl⟩

def haar (x : Sphere E) : Measure (subgroup x) :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (subgroup x))

instance haarProbability (x : Sphere E) : IsProbabilityMeasure (haar x) :=
  ⟨Measure.haarMeasure_self⟩

instance haarLeftInvariant (x : Sphere E) : (haar x).IsMulLeftInvariant := by
  unfold haar
  infer_instance

instance haarIsHaar (x : Sphere E) : (haar x).IsHaarMeasure := by
  unfold haar
  infer_instance

theorem haar_map_right (x : Sphere E) (S : subgroup x) : (haar x).map (· * S) = haar x := by
  have hm : Measurable (fun R : subgroup x => R * S) := (continuous_mul_const S).measurable
  let : IsProbabilityMeasure ((haar x).map (· * S)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

instance haarRightInvariant (x : Sphere E) : (haar x).IsMulRightInvariant := ⟨haar_map_right x⟩

omit [Nontrivial E] in
theorem fixed (x : Sphere E) (R : subgroup x) : rotate R.1 x = x := R.2

omit [Nontrivial E] in
theorem exists_latitude (x y z : Sphere E)
    (h : inner ℝ (x : E) (y : E) = inner ℝ (x : E) (z : E)) :
    ∃ R : subgroup x, rotate R.1 y = z := by
  obtain ⟨R, hR, hz⟩ := OrthogonalFrame.exists_exchange_latitude x y z h
  exact ⟨⟨R, hR⟩, hz⟩

omit [Nontrivial E] in
/-- Equal images of the axis differ by right multiplication in its stabilizer. -/
theorem same_axis (x : Sphere E) (R S : OrthogonalHaar.Group E)
    (h : rotate R x = rotate S x) : ∃ U : subgroup x, R = S * U.1 := by
  have hu : rotate (S⁻¹ * R) x = x := by
    rw [rotate_mul, h, ← rotate_mul, inv_mul_cancel, rotate_one]
  refine ⟨⟨S⁻¹ * R, hu⟩, ?_⟩
  simp

end ShadowVerification.AxisStabilizer
#print axioms ShadowVerification.AxisStabilizer.rotate_one
#print axioms ShadowVerification.AxisStabilizer.subgroup_closed
#print axioms ShadowVerification.AxisStabilizer.haar_map_right
#print axioms ShadowVerification.AxisStabilizer.fixed
#print axioms ShadowVerification.AxisStabilizer.exists_latitude
#print axioms ShadowVerification.AxisStabilizer.same_axis

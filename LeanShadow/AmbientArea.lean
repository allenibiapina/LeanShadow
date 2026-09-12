import LeanShadow.FullProjectiveFrame
import LeanShadow.AreaCoordinateVariations
import LeanShadow.DualFlow

/-! # Actual area functions in the full Euclidean matrix coordinates

The coordinate map is a constructed continuous linear equivalence. The
exponential of a left-multiplication field is identified with the actual
matrix path by convergence of its power series. Area regularity is then
transported from the previously proved operator-coordinate theorem.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Matrix MeasureTheory
open scoped BigOperators Topology
namespace ShadowVerification.AmbientArea
open FullFrame Coordinates Spherical Projective Regularity AreaCoordinates
open _root_.ShadowVerification.Frame _root_.ShadowVerification.Dual

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def matrixOperator : Matrix n n ℝ ≃ₗ[ℝ]
    (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) :=
  Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap

noncomputable def coordinateEquiv : Ambient n ≃L[ℝ]
    (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) :=
  (flatten.symm.trans matrixOperator).toContinuousLinearEquiv

theorem matrixOperator_apply (H : Matrix n n ℝ) : matrixOperator H = operator H := rfl

theorem coordinateEquiv_apply (x : Ambient n) : coordinateEquiv x = operator (flatten.symm x) := rfl

theorem operator_mul (H K : Matrix n n ℝ) : operator (H * K) = operator H * operator K := by
  ext x i
  change ((H * K) *ᵥ ⇑x) i = (H *ᵥ (K *ᵥ ⇑x)) i
  rw [Matrix.mulVec_mulVec]

theorem operator_one : operator (1 : Matrix n n ℝ) = 1 := by
  ext x i
  change ((1 : Matrix n n ℝ) *ᵥ ⇑x) i = x i
  simp

/-- Coordinate left multiplication is exactly multiplication of operators. -/
theorem coordinate_leftField (H : Matrix n n ℝ) (x : Ambient n) :
    coordinateEquiv (leftField H x) = operator H * coordinateEquiv x := by
  rw [coordinateEquiv_apply, leftField_apply, LinearEquiv.symm_apply_apply, operator_mul]
  rfl

/-- Compatibility for every power, needed for the actual exponential series. -/
theorem coordinate_power (H : Matrix n n ℝ) (t : ℝ) (x : Ambient n) (k : ℕ) :
    coordinateEquiv (((t • leftField H) ^ k) x) = (t • operator H) ^ k * coordinateEquiv x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, _root_.smul_apply, map_smul,
      coordinate_leftField, ih, pow_succ']
    simp only [mul_assoc]
    rfl

/-- The exponential paths agree as actual functions, not just to second order. -/
theorem coordinate_flow (H : Matrix n n ℝ) (t : ℝ) (x : Ambient n) :
    coordinateEquiv (flow (leftField H) x t) =
      NormedSpace.exp (t • operator H) * coordinateEquiv x := by
  have h1 := (coordinateEquiv (n := n)).toContinuousLinearMap.hasSum
    ((ContinuousLinearMap.apply ℝ (Ambient n) x).hasSum
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • leftField H)))
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • operator H)).mul_right
    (coordinateEquiv x)
  simp only [ContinuousLinearMap.apply_apply, map_smul,
    ContinuousLinearEquiv.coe_coe, coordinate_power, smul_mul_assoc] at h1 h2
  exact h1.unique h2

/-- The linear coordinate map transports the geometric operator topology. -/
theorem coordinate_base : coordinateEquiv (base (n := n)) = 1 := by
  rw [coordinateEquiv_apply, base, LinearEquiv.symm_apply_apply, operator_one]

/-- The parameter point representing an invertible geometric transformation. -/
noncomputable def point (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) : Ambient n :=
  coordinateEquiv.symm (T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)

theorem coordinate_point (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) :
    coordinateEquiv (point T) = (T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) :=
  ContinuousLinearEquiv.apply_symm_apply _ _

/-- Every field flow through an invertible point remains a geometric transformation. -/
theorem flow_point (H : Matrix n n ℝ) (t : ℝ)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) :
    flow (leftField H) (point T) t = point (T.trans (flowEquiv (operator H) t)) := by
  apply coordinateEquiv.injective
  rw [coordinate_flow, coordinate_point, coordinate_point, trans_flow_to_operator]
  rfl

variable [Nonempty n] [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]

noncomputable def primal (A : Set (Sphere (EuclideanSpace ℝ n))) (x : Ambient n) : ℝ :=
  areaExtension mu A (coordinateEquiv x)

noncomputable def dual (B : Set (Sphere (EuclideanSpace ℝ n))) (x : Ambient n) : ℝ :=
  dualAreaExtension mu B (coordinateEquiv x)

theorem primal_point (A : Set (Sphere (EuclideanSpace ℝ n))) (hA : MeasurableSet A)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) :
    primal mu A (point T) = transformedArea mu A T := by
  rw [primal, coordinate_point, transformedArea_eq_extension mu A hA]

theorem dual_point (B : Set (Sphere (EuclideanSpace ℝ n))) (hB : MeasurableSet B)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) :
    dual mu B (point T) = transformedArea mu B (dualEquiv T) := by
  rw [dual, coordinate_point, transformedDualArea_eq_extension mu B hB]

/-- Joint C² regularity of actual primal area in the full Euclidean coordinates. -/
theorem primal_contDiffAt (A : Set (Sphere (EuclideanSpace ℝ n)))
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) :
    ContDiffAt ℝ 2 (primal mu A) (point T) := by
  have h : ContDiffAt ℝ 2 (areaExtension mu A) (coordinateEquiv (point T)) := by
    rw [coordinate_point]
    exact contDiffAt_areaExtension mu A T
  exact h.comp (point T) (coordinateEquiv (n := n)).contDiff.contDiffAt

/-- The inverse-adjoint area has the same joint coordinate regularity. -/
theorem dual_contDiffAt (B : Set (Sphere (EuclideanSpace ℝ n)))
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) :
    ContDiffAt ℝ 2 (dual mu B) (point T) := by
  have h : ContDiffAt ℝ 2 (dualAreaExtension mu B) (coordinateEquiv (point T)) := by
    rw [coordinate_point]
    exact contDiffAt_dualAreaExtension mu B T
  exact h.comp (point T) (coordinateEquiv (n := n)).contDiff.contDiffAt

end ShadowVerification.AmbientArea
#print axioms ShadowVerification.AmbientArea.matrixOperator_apply
#print axioms ShadowVerification.AmbientArea.coordinateEquiv_apply
#print axioms ShadowVerification.AmbientArea.operator_mul
#print axioms ShadowVerification.AmbientArea.operator_one
#print axioms ShadowVerification.AmbientArea.coordinate_leftField
#print axioms ShadowVerification.AmbientArea.coordinate_power
#print axioms ShadowVerification.AmbientArea.coordinate_flow
#print axioms ShadowVerification.AmbientArea.coordinate_base
#print axioms ShadowVerification.AmbientArea.coordinate_point
#print axioms ShadowVerification.AmbientArea.flow_point
#print axioms ShadowVerification.AmbientArea.primal_point
#print axioms ShadowVerification.AmbientArea.dual_point
#print axioms ShadowVerification.AmbientArea.primal_contDiffAt
#print axioms ShadowVerification.AmbientArea.dual_contDiffAt

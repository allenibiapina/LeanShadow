import LeanShadow.EuclideanMatrix
import LeanShadow.MatrixBochner
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Integrated moment and contraction identities on the actual sphere

Every continuous density is proved integrable for any finite Borel measure
on the unit sphere. In particular the results apply to normalized spherical
measure restricted to an arbitrary Borel set. The integrated contraction and
first-variation reconstruction are conclusions, not assumptions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open Matrix MeasureTheory Set Module
namespace ShadowVerification.Integrated
open Spherical Coordinates MatrixIntegral
open _root_.ShadowVerification.Frame

variable {n : Type*} [Fintype n] [DecidableEq n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]

abbrev UnitSphere (n : Type*) [Fintype n] := Sphere (EuclideanSpace ℝ n)

noncomputable def momentDensity (x : n → ℝ) : Matrix n n ℝ :=
  1 - (Fintype.card n : ℝ) • vecMulVec x x

variable {ι : Type*} [Fintype ι]

noncomputable def firstDensity (H : ι → Matrix n n ℝ) (x : n → ℝ) : ι → ℝ :=
  fun i => -(Fintype.card n : ℝ) * (x ⬝ᵥ (H i *ᵥ x))

omit [DecidableEq n] [MeasurableSpace (EuclideanSpace ℝ n)]
    [BorelSpace (EuclideanSpace ℝ n)] [Fintype ι] in
theorem continuous_firstDensity (H : ι → Matrix n n ℝ) :
    Continuous (fun x : UnitSphere n => firstDensity H ⇑(x : EuclideanSpace ℝ n)) := by
  unfold firstDensity dotProduct Matrix.mulVec
  fun_prop

omit [DecidableEq n] [MeasurableSpace (EuclideanSpace ℝ n)]
    [BorelSpace (EuclideanSpace ℝ n)] [Fintype ι] in
theorem continuous_pointwiseKernel (H : ι → Matrix n n ℝ) :
    Continuous (fun x : UnitSphere n => pointwiseKernel H ⇑(x : EuclideanSpace ℝ n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp_rw [pointwiseKernel_apply]
  unfold dotProduct Matrix.mulVec
  fun_prop

omit [Fintype ι] [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)] in
theorem continuous_momentDensity :
    Continuous (fun x : UnitSphere n => momentDensity ⇑(x : EuclideanSpace ℝ n)) := by
  unfold momentDensity Matrix.vecMulVec
  fun_prop

omit [DecidableEq n] [Fintype ι] in
theorem sphere_integrable_continuous {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (nu : Measure (UnitSphere n)) [IsFiniteMeasure nu] (f : UnitSphere n → F)
    (hf : Continuous f) : Integrable f nu := by
  let : CompactSpace (UnitSphere n) := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

variable (nu : Measure (UnitSphere n)) [IsFiniteMeasure nu]

noncomputable def integratedKernel (H : ι → Matrix n n ℝ) : Matrix ι ι ℝ :=
  ∫ x, pointwiseKernel H ⇑(x : EuclideanSpace ℝ n) ∂nu

noncomputable def gradientMatrix : Matrix n n ℝ :=
  ∫ x, momentDensity ⇑(x : EuclideanSpace ℝ n) ∂nu

noncomputable def firstCoefficients (H : ι → Matrix n n ℝ) : ι → ℝ :=
  ∫ x, firstDensity H ⇑(x : EuclideanSpace ℝ n) ∂nu

omit [DecidableEq n] in
theorem integratedKernel_entry (H : ι → Matrix n n ℝ) (i j : ι) :
    integratedKernel nu H i j = ∫ x, pointwiseKernel H ⇑(x : EuclideanSpace ℝ n) i j ∂nu := by
  exact integral_entry nu _ (sphere_integrable_continuous nu _ (continuous_pointwiseKernel H)) i j

omit [DecidableEq n] in
theorem firstCoefficients_entry (H : ι → Matrix n n ℝ) (i : ι) :
    firstCoefficients nu H i =
      ∫ x, -(Fintype.card n : ℝ) *
        (⇑(x : EuclideanSpace ℝ n) ⬝ᵥ (H i *ᵥ ⇑(x : EuclideanSpace ℝ n))) ∂nu := by
  exact eval_integral
    (fun i => (sphere_integrable_continuous nu _ (continuous_firstDensity H)).eval i) i

omit [Fintype ι] in
/-- The gradient matrix is the actual centered second-moment matrix. -/
theorem gradientMatrix_eq :
    gradientMatrix nu = nu.real univ • (1 : Matrix n n ℝ) -
      (Fintype.card n : ℝ) •
        ∫ x, vecMulVec ⇑(x : EuclideanSpace ℝ n) ⇑(x : EuclideanSpace ℝ n) ∂nu := by
  have hp : Integrable (fun x : UnitSphere n =>
      vecMulVec ⇑(x : EuclideanSpace ℝ n) ⇑(x : EuclideanSpace ℝ n)) nu :=
    sphere_integrable_continuous nu _ (by unfold Matrix.vecMulVec; fun_prop)
  ext i j
  rw [gradientMatrix, integral_entry nu _
    (sphere_integrable_continuous nu _ continuous_momentDensity)]
  simp only [momentDensity, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [integral_entry nu _ hp]
  rw [integral_sub (integrable_const _)
    (((hp.eval i).eval j).const_mul (Fintype.card n : ℝ)), integral_const, integral_const_mul]
  rfl

variable [Nonempty n]

/-- Integrating the proved pointwise identity gives the full matrix contraction. -/
theorem integrated_contraction (b : Basis ι ℝ (symZero (n := n))) (hb : IsOrthonormal b) :
    manuscriptContraction (frame b) (integratedKernel nu (frame b)) =
      (-((Fintype.card n : ℝ) - 2) / 2) • gradientMatrix nu := by
  rw [integratedKernel, contraction_integral nu _ _
    (sphere_integrable_continuous nu _ (continuous_pointwiseKernel (frame b)))]
  simp_rw [pointwise_contraction b hb _ (sphere_dot_self _)]
  rw [gradientMatrix, ← integral_smul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  ext i j
  simp only [momentDensity, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- The integrated first derivatives reconstruct the centered moment matrix. -/
theorem integrated_first_reconstruction
    (b : Basis ι ℝ (symZero (n := n))) (hb : IsOrthonormal b) :
    (∑ i, firstCoefficients nu (frame b) i • frame b i) = gradientMatrix nu := by
  change synthesis (frame b) (∫ x, firstDensity (frame b) ⇑(x : EuclideanSpace ℝ n) ∂nu) = _
  rw [synthesis_integral nu _ _
    (sphere_integrable_continuous nu _ (continuous_firstDensity (frame b))), gradientMatrix]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  exact first_variation_reconstruction b hb _ (sphere_dot_self x)

theorem integrated_trace_zero (b : Basis ι ℝ (symZero (n := n))) (hb : IsOrthonormal b) :
    (integratedKernel nu (frame b)).trace = 0 := by
  rw [integratedKernel, integral_trace nu _
    (sphere_integrable_continuous nu _ (continuous_pointwiseKernel (frame b)))]
  simp_rw [pointwise_trace b hb _ (sphere_dot_self _)]
  exact integral_zero _ _

omit [Fintype ι] [Nonempty n] in
theorem gradient_trace_zero : (gradientMatrix nu).trace = 0 := by
  rw [gradientMatrix, integral_trace nu _
    (sphere_integrable_continuous nu _ continuous_momentDensity)]
  have hzero : ∀ x : UnitSphere n, (momentDensity ⇑(x : EuclideanSpace ℝ n)).trace = 0 := by
    intro x
    simp [momentDensity, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_vecMulVec, sphere_dot_self x]
  simp_rw [hzero]
  exact integral_zero _ _

omit [Fintype ι] [Nonempty n] in
theorem gradient_symmetric : (gradientMatrix nu).IsSymm := by
  apply integral_isSymm nu _ (sphere_integrable_continuous nu _ continuous_momentDensity)
  intro x
  change (momentDensity ⇑(x : EuclideanSpace ℝ n))ᵀ = _
  simp [momentDensity, Matrix.transpose_sub, Matrix.transpose_smul, transpose_vecMulVec]

end ShadowVerification.Integrated
#print axioms ShadowVerification.Integrated.continuous_firstDensity
#print axioms ShadowVerification.Integrated.continuous_pointwiseKernel
#print axioms ShadowVerification.Integrated.continuous_momentDensity
#print axioms ShadowVerification.Integrated.sphere_integrable_continuous
#print axioms ShadowVerification.Integrated.integratedKernel_entry
#print axioms ShadowVerification.Integrated.firstCoefficients_entry
#print axioms ShadowVerification.Integrated.gradientMatrix_eq
#print axioms ShadowVerification.Integrated.integrated_contraction
#print axioms ShadowVerification.Integrated.integrated_first_reconstruction
#print axioms ShadowVerification.Integrated.integrated_trace_zero
#print axioms ShadowVerification.Integrated.gradient_trace_zero
#print axioms ShadowVerification.Integrated.gradient_symmetric

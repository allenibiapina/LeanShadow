import LeanShadow.PointwiseContraction
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Normed

/-! # Matrix operations commute with Bochner integration

All linear maps below are defined using the actual finite matrix sums.
Their continuity follows from finite dimensionality. Integrability remains
explicit in these general-purpose lemmas; the spherical application proves it.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open Matrix MeasureTheory
namespace ShadowVerification.MatrixIntegral

variable {n ι : Type*} [Fintype n] [Fintype ι]

noncomputable def contractionLinear (H : ι → Matrix n n ℝ) :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix n n ℝ where
  toFun := manuscriptContraction H
  map_add' Q R := by
    classical
    simp only [manuscriptContraction, Matrix.add_apply, add_div, add_smul,
      Finset.sum_add_distrib]
  map_smul' r Q := manuscriptContraction_smul H Q r

noncomputable def synthesis (H : ι → Matrix n n ℝ) : (ι → ℝ) →ₗ[ℝ] Matrix n n ℝ where
  toFun v := ∑ i, v i • H i
  map_add' u v := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, RingHom.id_apply]

variable {X : Type*} [MeasurableSpace X] (mu : Measure X)

theorem contraction_integral (H : ι → Matrix n n ℝ) (Q : X → Matrix ι ι ℝ)
    (hQ : Integrable Q mu) :
    manuscriptContraction H (∫ x, Q x ∂mu) = ∫ x, manuscriptContraction H (Q x) ∂mu := by
  exact ((contractionLinear H).toContinuousLinearMap.integral_comp_comm hQ).symm

theorem synthesis_integral (H : ι → Matrix n n ℝ) (v : X → ι → ℝ)
    (hv : Integrable v mu) :
    synthesis H (∫ x, v x ∂mu) = ∫ x, synthesis H (v x) ∂mu := by
  exact ((synthesis H).toContinuousLinearMap.integral_comp_comm hv).symm

omit [Fintype ι] in
theorem integral_entry (Q : X → Matrix n n ℝ) (hQ : Integrable Q mu) (i j : n) :
    (∫ x, Q x ∂mu) i j = ∫ x, Q x i j ∂mu := by
  rw [eval_integral (fun i => hQ.eval i) i,
    eval_integral (fun j => (hQ.eval i).eval j) j]

omit [Fintype ι] in
theorem integral_trace (Q : X → Matrix n n ℝ) (hQ : Integrable Q mu) :
    (∫ x, Q x ∂mu).trace = ∫ x, (Q x).trace ∂mu := by
  unfold Matrix.trace Matrix.diag
  simp_rw [integral_entry mu Q hQ]
  exact (integral_finsetSum Finset.univ (fun i _ => (hQ.eval i).eval i)).symm

omit [Fintype ι] in
theorem integral_isSymm (Q : X → Matrix n n ℝ) (hQ : Integrable Q mu)
    (hs : ∀ x, (Q x).IsSymm) : (∫ x, Q x ∂mu).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp_rw [integral_entry mu Q hQ]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => (hs x).apply i j)

end ShadowVerification.MatrixIntegral
#print axioms ShadowVerification.MatrixIntegral.contraction_integral
#print axioms ShadowVerification.MatrixIntegral.synthesis_integral
#print axioms ShadowVerification.MatrixIntegral.integral_entry
#print axioms ShadowVerification.MatrixIntegral.integral_trace
#print axioms ShadowVerification.MatrixIntegral.integral_isSymm

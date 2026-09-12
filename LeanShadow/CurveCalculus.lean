import LeanShadow.EllipticMaximum
import LeanShadow.ProjectiveJacobian
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # From exponential variations to a coordinate differential operator

A second derivative along a curved path has two terms: the Hessian evaluated
on its velocity, and the first derivative evaluated on its acceleration.
This module proves that chain rule for an actual `C²` function and applies
it to the actual operator exponential. The resulting finite sum is exactly
the coordinate operator used in `EllipticMaximum`, including its drift.

These are calculus identities. They do not assert that the geometric area
function is jointly `C²`, nor that a particular frame is elliptic.
-/

set_option autoImplicit false
open Filter
open scoped Topology BigOperators

namespace ShadowVerification.Curves

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The full second derivative along a curve, including its acceleration. -/
theorem second_deriv_comp (u : E → ℝ) (γ v : ℝ → E) (t : ℝ) (a : E)
    (hu : ContDiffAt ℝ 2 u (γ t))
    (hγ : ∀ s, HasDerivAt γ (v s) s) (hv : HasDerivAt v a t) :
    deriv (deriv (fun s => u (γ s))) t =
      (fderiv ℝ (fderiv ℝ u) (γ t) (v t)) (v t) +
        fderiv ℝ u (γ t) a := by
  have hnear : ∀ᶠ y in 𝓝 (γ t), DifferentiableAt ℝ u y := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    exact hy.differentiableAt (by norm_num)
  have heq : deriv (fun s => u (γ s)) =ᶠ[𝓝 t]
      fun s => fderiv ℝ u (γ s) (v s) := by
    filter_upwards [(hγ t).continuousAt.tendsto.eventually hnear] with s hs
    exact (hs.hasFDerivAt.comp_hasDerivAt s (hγ s)).deriv
  rw [heq.deriv_eq]
  have hDu : DifferentiableAt ℝ (fderiv ℝ u) (γ t) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact ((hDu.hasFDerivAt.comp_hasDerivAt t (hγ t)).clm_apply hv).deriv

/-- The line derivative used in the maximum principle is the Fréchet derivative. -/
theorem firstLine_eq_fderiv (u : E → ℝ) (x v : E)
    (hu : DifferentiableAt ℝ u x) :
    Elliptic.firstLine u x v = fderiv ℝ u x v := by
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  exact (hu.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)).deriv

/-- A straight line has zero acceleration, so only the Hessian term remains. -/
theorem secondLine_eq_fderiv (u : E → ℝ) (x v : E)
    (hu : ContDiffAt ℝ 2 u x) :
    Elliptic.secondLine u x v = (fderiv ℝ (fderiv ℝ u) x v) v := by
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v t := by
    intro t
    simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const v).const_add x
  simpa [Elliptic.secondLine] using
    second_deriv_comp u (fun s : ℝ => x + s • v) (fun _ => v) 0 0
      (by simpa using hu) hline (hasDerivAt_const 0 v)

end ShadowVerification.Curves

namespace ShadowVerification.Curves

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual exponential curve has initial velocity `H x`. -/
theorem flow_first_deriv (u : E → ℝ) (H : E →L[ℝ] E) (x : E)
    (hu : DifferentiableAt ℝ u x) :
    deriv (fun t => u (Projective.flow H x t)) 0 =
      Elliptic.firstLine u x (H x) := by
  rw [firstLine_eq_fderiv u x (H x) hu]
  simpa only [Projective.flow_zero, Function.comp_def] using
    (hu.hasFDerivAt.comp_hasDerivAt_of_eq 0
      (Projective.flow_hasDeriv H x 0) (Projective.flow_zero H x).symm).deriv

/-- An exponential curve has acceleration `H (H x)`, which gives the drift. -/
theorem flow_second_deriv (u : E → ℝ) (H : E →L[ℝ] E) (x : E)
    (hu : ContDiffAt ℝ 2 u x) :
    deriv (deriv (fun t => u (Projective.flow H x t))) 0 =
      Elliptic.secondLine u x (H x) + Elliptic.firstLine u x (H (H x)) := by
  rw [secondLine_eq_fderiv u x (H x) hu,
    firstLine_eq_fderiv u x (H (H x)) (hu.differentiableAt (by norm_num))]
  simpa only [Projective.flow_zero] using
    second_deriv_comp u (Projective.flow H x) (Projective.flow H (H x)) 0
      (H (H x)) (by simpa only [Projective.flow_zero] using hu)
      (Projective.flow_hasDeriv H x)
      (by simpa only [Projective.flow_zero] using Projective.flow_hasDeriv H (H x) 0)

/-- Polarizing exponential variations gives the symmetrized mixed Hessian
and the symmetrized mixed acceleration. No symmetry of the two operators is
assumed, and the order of their products is retained. -/
theorem polarized_flow_second_deriv (u : E → ℝ) (H K : E →L[ℝ] E) (x : E)
    (hu : ContDiffAt ℝ 2 u x) :
    (deriv (deriv (fun t => u (Projective.flow (H + K) x t))) 0 -
      deriv (deriv (fun t => u (Projective.flow H x t))) 0 -
      deriv (deriv (fun t => u (Projective.flow K x t))) 0) / 2 =
      ((fderiv ℝ (fderiv ℝ u) x (H x)) (K x) +
        (fderiv ℝ (fderiv ℝ u) x (K x)) (H x)) / 2 +
      fderiv ℝ u x ((1 / 2 : ℝ) • (H (K x) + K (H x))) := by
  simp_rw [flow_second_deriv u _ x hu, secondLine_eq_fderiv u x _ hu,
    firstLine_eq_fderiv u x _ (hu.differentiableAt (by norm_num))]
  simp only [add_apply, map_add, map_smul, smul_eq_mul]
  ring

/-- A finite sum of exponential second variations is the coordinate frame
operator with the sum of the individual accelerations as drift. -/
theorem sum_flow_second_eq_frameOp {ι : Type*} [Fintype ι]
    (u : E → ℝ) (H : ι → E →L[ℝ] E) (x : E) (hu : ContDiffAt ℝ 2 u x) :
    (∑ i, deriv (deriv (fun t => u (Projective.flow (H i) x t))) 0) =
      Elliptic.frameOp (fun i y => H i y) (fun y => ∑ i, H i (H i y)) u x := by
  simp_rw [flow_second_deriv u _ x hu]
  rw [Finset.sum_add_distrib]
  unfold Elliptic.frameOp
  congr 1
  simp_rw [firstLine_eq_fderiv u x _ (hu.differentiableAt (by norm_num))]
  rw [map_sum]

/-- The proved maximum principle can now be applied with a subsolution
inequality stated directly in terms of exponential-flow second derivatives.
Ellipticity and coefficient bounds are still explicit hypotheses. -/
theorem local_strong_maximum_of_flow {ι : Type*} [Fintype ι] [ProperSpace E]
    (H : ι → E →L[ℝ] E) (u : E → ℝ) (x₀ : E) (R lam C B : ℝ)
    (hR : 0 < R) (hlam : 0 < lam) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hc : Continuous u)
    (hmax : ∀ x, ‖x - x₀‖ < R → u x ≤ u x₀)
    (hsmooth : ∀ x, ‖x - x₀‖ < R → ContDiffAt ℝ 2 u x)
    (hsub : ∀ x, ‖x - x₀‖ < R →
      0 ≤ ∑ i, deriv (deriv (fun t => u (Projective.flow (H i) x t))) 0)
    (hell : ∀ x, ‖x - x₀‖ < R → ∀ v : E,
      lam * ‖v‖ ^ 2 ≤ ∑ i, (inner ℝ v (H i x)) ^ 2)
    (htrace : ∀ x, ‖x - x₀‖ < R → (∑ i, ‖H i x‖ ^ 2) ≤ C)
    (hdrift : ∀ x, ‖x - x₀‖ < R → ‖∑ i, H i (H i x)‖ ≤ B) :
    ∀ y, ‖y - x₀‖ < R / 4 → u y = u x₀ := by
  apply Elliptic.local_strong_maximum
    (fun i x => H i x) (fun x => ∑ i, H i (H i x)) u x₀
    R lam C B hR hlam hC hB hc hmax
  · intro x hx v
    have hl : ContDiff ℝ 2 (fun t : ℝ => x + t • v) :=
      contDiff_const.add (contDiff_id.smul contDiff_const)
    have hu : ContDiffAt ℝ 2 u (x + (0 : ℝ) • v) := by
      simpa using hsmooth x hx
    exact hu.comp 0 hl.contDiffAt
  · intro x hx
    rw [← sum_flow_second_eq_frameOp u H x (hsmooth x hx)]
    exact hsub x hx
  · exact hell
  · exact htrace
  · exact hdrift

end ShadowVerification.Curves

#print axioms ShadowVerification.Curves.second_deriv_comp
#print axioms ShadowVerification.Curves.firstLine_eq_fderiv
#print axioms ShadowVerification.Curves.secondLine_eq_fderiv
#print axioms ShadowVerification.Curves.flow_first_deriv
#print axioms ShadowVerification.Curves.flow_second_deriv
#print axioms ShadowVerification.Curves.polarized_flow_second_deriv
#print axioms ShadowVerification.Curves.sum_flow_second_eq_frameOp
#print axioms ShadowVerification.Curves.local_strong_maximum_of_flow

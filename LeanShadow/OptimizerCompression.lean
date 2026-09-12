import LeanShadow.ProjectiveCompression
import LeanShadow.CompressionConcentration

/-! # Compression consequences for the actual optimal shadow profile

The contact maximum, weighted elliptic argument, passage to full derivative
vanishing, and analyticity along the actual compression family are all supplied
by preceding theorems. The final theorem supplies the zero compression limit
from the actual set's positive complement measure. Its remaining hypotheses
are an actual optimizer, an interior area, and a positive-slope second-order
expansion of the actual optimal profile.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace ShadowVerification.OptimizerCompression
open Spherical Integrated Compression AmbientArea FullFrame

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def path (e : UnitSphere n) (t : ℝ) : Ambient n :=
  coordinateEquiv.symm (compressionOperator e t)

theorem path_continuous (e : UnitSphere n) : Continuous (path e) :=
  coordinateEquiv.symm.continuous.comp (compressionOperator_continuous e)

theorem path_one (e : UnitSphere n) : path e 1 = base := by
  apply coordinateEquiv.injective
  rw [path, ContinuousLinearEquiv.apply_symm_apply, compressionOperator_one, coordinate_base]

theorem path_eq_point (e : UnitSphere n) (t : ℝ) (ht : 0 < t) :
    path e t = point (compressionEquiv e t ht) := rfl

variable [Nonempty n] [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]

omit [Nonempty n] [BorelSpace (EuclideanSpace ℝ n)] [mu.IsAddHaarMeasure] in
theorem primal_path (A : Set (UnitSphere n)) (e : UnitSphere n) (t : ℝ) :
    primal mu A (path e t) = compressionArea mu A e t := by
  simp only [primal, path, compressionArea, ContinuousLinearEquiv.apply_symm_apply]

theorem compressionArea_one (A : Set (UnitSphere n)) (hA : MeasurableSet A) (e : UnitSphere n) :
    compressionArea mu A e 1 = area mu A := by
  rw [← primal_path, path_one, ProfileContact.primal_base mu A hA]

/-- Analytic continuation propagates local constancy through every positive
compression parameter in every axis direction. -/
theorem constant_compression_of_locally_constant (A : Set (UnitSphere n)) (p : ℝ)
    (hlocal : primal mu A =ᶠ[𝓝 (base (n := n))] (fun _ => p))
    (e : UnitSphere n) (t : ℝ) (ht : 0 < t) : compressionArea mu A e t = p := by
  have hp : Tendsto (path e) (𝓝 1) (𝓝 (base (n := n))) := by
    simpa only [path_one] using (path_continuous e).continuousAt.tendsto (x := (1 : ℝ))
  have hnear : compressionArea mu A e =ᶠ[𝓝 1] (fun _ => p) := by
    filter_upwards [hp.eventually hlocal] with s hs
    simpa only [primal_path] using hs
  exact (analytic_compressionArea mu A e).eqOn_of_preconnected_of_eventuallyEq
    (fun _ _ => analyticAt_const) (convex_Ioi (0 : ℝ)).isPreconnected
    (by norm_num : (1 : ℝ) ∈ Ioi 0) hnear ht

/-- An isotropic actual optimizer would keep its mass under arbitrarily
strong compression about every axis. -/
theorem isotropic_optimizer_compression_constant (p : ℝ) (A : Set (UnitSphere n))
    (hA : Profile.IsOptimizer mu p A) (k rho : ℝ)
    (hexp : ProfileSupport.HasQuadraticExpansion (Profile.profile mu) p k rho)
    (hk : 0 < k) (hn : (2 : ℝ) < Fintype.card n) (hiso : Paired.actualMoment mu A = 0)
    (e : UnitSphere n) (t : ℝ) (ht : 0 < t) : compressionArea mu A e t = p :=
  constant_compression_of_locally_constant mu A p
    (LocalArea.isotropic_optimizer_area_constant_near mu p A hA k rho hexp hk hn hiso) e t ht

/-- A zero compression limit is incompatible with positive constant mass. -/
theorem nonisotropic_of_zero_compression_limit (p : ℝ) (A : Set (UnitSphere n))
    (hA : Profile.IsOptimizer mu p A) (k rho : ℝ)
    (hexp : ProfileSupport.HasQuadraticExpansion (Profile.profile mu) p k rho)
    (hk : 0 < k) (hn : (2 : ℝ) < Fintype.card n) (hp : 0 < p)
    (e : UnitSphere n)
    (hlimit : Tendsto (compressionArea mu A e) atTop (𝓝 0)) : Paired.actualMoment mu A ≠ 0 := by
  intro hiso
  have he : compressionArea mu A e =ᶠ[atTop] (fun _ => p) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact isotropic_optimizer_compression_constant mu p A hA k rho hexp hk hn hiso e t ht
  have hc : Tendsto (compressionArea mu A e) atTop (𝓝 p) := tendsto_const_nhds.congr' he.symm
  exact hp.ne' (tendsto_nhds_unique hc hlimit)

/-- Nonisotropy of an actual optimizer at an interior second-order profile
point. The contact maximum, local constancy implication, analytic continuation,
and density-point compression limit are all proved dependencies. -/
theorem optimizer_nonisotropic (p : ℝ) (A : Set (UnitSphere n))
    (hA : Profile.IsOptimizer mu p A) (k rho : ℝ)
    (hexp : ProfileSupport.HasQuadraticExpansion (Profile.profile mu) p k rho)
    (hk : 0 < k) (hn : (2 : ℝ) < Fintype.card n) (hp : 0 < p) (hp1 : p < 1) :
    Paired.actualMoment mu A ≠ 0 := by
  obtain ⟨e, hlimit⟩ := CompressionConcentration.exists_zero_compression mu A
    hA.measurable hA.antipodal (by simpa only [hA.mass] using hp1)
  exact nonisotropic_of_zero_compression_limit mu p A hA k rho hexp hk hn hp e hlimit

/-- In particular, actual area has a nonzero full first derivative at the
identity. This rules out first-order stationary area under all projective motions. -/
theorem optimizer_area_fderiv_ne_zero (p : ℝ) (A : Set (UnitSphere n))
    (hA : Profile.IsOptimizer mu p A) (k rho : ℝ)
    (hexp : ProfileSupport.HasQuadraticExpansion (Profile.profile mu) p k rho)
    (hk : 0 < k) (hn : (2 : ℝ) < Fintype.card n) (hp : 0 < p) (hp1 : p < 1) :
    fderiv ℝ (primal mu A) (base (n := n)) ≠ 0 := by
  intro hz
  apply optimizer_nonisotropic mu p A hA k rho hexp hk hn hp hp1
  rw [← ActualLocal.moment_base mu A hA.measurable, MomentField.moment, hz]
  simp

end ShadowVerification.OptimizerCompression
#print axioms ShadowVerification.OptimizerCompression.path_continuous
#print axioms ShadowVerification.OptimizerCompression.path_one
#print axioms ShadowVerification.OptimizerCompression.path_eq_point
#print axioms ShadowVerification.OptimizerCompression.primal_path
#print axioms ShadowVerification.OptimizerCompression.compressionArea_one
#print axioms ShadowVerification.OptimizerCompression.constant_compression_of_locally_constant
#print axioms ShadowVerification.OptimizerCompression.isotropic_optimizer_compression_constant
#print axioms ShadowVerification.OptimizerCompression.nonisotropic_of_zero_compression_limit
#print axioms ShadowVerification.OptimizerCompression.optimizer_nonisotropic
#print axioms ShadowVerification.OptimizerCompression.optimizer_area_fderiv_ne_zero

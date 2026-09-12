import LeanShadow.OptimizerCompression

/-! # Affine contact maxima and the dual compression path

The already proved weighted source specializes to zero quadratic coefficient
and zero weight parameter. It proves local constancy of an affine contact at
a local maximum, for arbitrary slope and without an isotropy hypothesis.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology Matrix.Norms.Frobenius
namespace ShadowVerification.AffineContact
open Spherical Integrated FullFrame AmbientArea ActualContact MomentField ContactOperator
open Compression OptimizerCompression
open _root_.ShadowVerification.Dual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem dilation_inner (e : Sphere E) (s : ℝ) (x y : E) :
    inner ℝ (dilation e s x) y = inner ℝ x (dilation e s y) := by
  simp only [dilation_apply, axisProjection_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right]
  rw [real_inner_comm x (e : E)]
  ring

variable [FiniteDimensional ℝ E]

theorem dual_compression (e : Sphere E) (t : ℝ) (ht : 0 < t) :
    dualEquiv (compressionEquiv e t ht) = compressionEquiv e t⁻¹ (inv_pos.mpr ht) := by
  symm
  apply DualFlow.dual_unique
  intro x y
  change inner ℝ (dilation e (Real.sqrt t) x) (dilation e (Real.sqrt t⁻¹) y) = _
  rw [dilation_inner, dilation_comp, Real.sqrt_inv,
    mul_inv_cancel₀ (Real.sqrt_pos.mpr ht).ne', dilation_one]
  rfl

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]

theorem affine_local_constant (A B : Set (UnitSphere n))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (q p k : ℝ)
    (hmax : IsLocalMax (contact mu A B q p k 0) (base (n := n))) :
    contact mu A B q p k 0 =ᶠ[𝓝 (base (n := n))]
      (fun _ => contact mu A B q p k 0 base) := by
  let T := ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ n)
  have hp : point T = base := ActualLocal.point_identity
  have hnear : ∀ᶠ x in 𝓝 (base (n := n)),
      ContDiffAt ℝ 2 (contact mu A B q p k 0) x ∧
      (coefficients mu A 0 x).PosSemidef ∧
      (1 : ℝ) * ‖(0 : ℝ)‖ ^ 2 ≤ WeightedFrame.op (coefficients mu A 0)
        (fun i x => fullFields i x) (drift mu A 0) (contact mu A B q p k 0) x := by
    filter_upwards [hp ▸ eventually_point T] with x hx
    obtain ⟨U,rfl⟩ := hx
    refine ⟨contact_contDiffAt mu A B q p k 0 U,
      (FullWeight.geometricWeight_posDef (moment mu A) 0 _ le_rfl (by simp)).posSemidef, ?_⟩
    simpa using variable_source mu A B hA hB q p k 0 0 U le_rfl le_rfl (by simp) (by simp)
  have h := WeightedOpen.source_zero_near_local_maximum
    (coefficients mu A 0) (fun i x => fullFields i x) (drift mu A 0)
    (contact mu A B q p k 0) (fun _ => (0 : ℝ)) base 1 zero_lt_one
    (fun i j => by simpa only [hp] using coefficients_continuousAt mu A 0 T i j)
    (fun i => (fullFields i).continuous.continuousAt)
    (by simpa only [hp] using drift_continuousAt mu A 0 T)
    (FullWeight.geometricWeight_posDef (moment mu A) 0 _ le_rfl (by simp))
    fields_separate_at_base hmax hnear
  exact h.mono fun _ hx => hx.1

theorem dual_path (B : Set (UnitSphere n)) (hB : MeasurableSet B)
    (e : UnitSphere n) (t : ℝ) (ht : 0 < t) :
    dual mu B (path e t) = compressionArea mu B e t⁻¹ := by
  rw [path_eq_point e t ht, dual_point mu B hB, dual_compression,
    compressionArea_eq_transformedArea mu B hB e t⁻¹ (inv_pos.mpr ht)]

theorem contact_path (A B : Set (UnitSphere n)) (hB : MeasurableSet B)
    (q p k : ℝ) (e : UnitSphere n) (t : ℝ) (ht : 0 < t) :
    contact mu A B q p k 0 (path e t) =
      compressionArea mu B e t⁻¹ + q + k * (compressionArea mu A e t - p) := by
  rw [contact, dual_path mu B hB e t ht, primal_path]
  simp [Contact.support, add_assoc]

omit [DecidableEq n] in
theorem analytic_affine_path (A B : Set (UnitSphere n)) (q p k : ℝ) (e : UnitSphere n) :
    AnalyticOnNhd ℝ
      (fun t => compressionArea mu B e t⁻¹ + q + k * (compressionArea mu A e t - p))
      (Ioi 0) := by
  intro t ht
  change 0 < t at ht
  have hB := (analytic_compressionArea mu B e t⁻¹ (inv_pos.mpr ht)).comp
    (analyticAt_id.inv ht.ne')
  exact (hB.add analyticAt_const).add
    (analyticAt_const.mul ((analytic_compressionArea mu A e t ht).sub analyticAt_const))

theorem affine_compression_constant (A B : Set (UnitSphere n))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (q p k : ℝ)
    (hmax : IsLocalMax (contact mu A B q p k 0) (base (n := n)))
    (e : UnitSphere n) (t : ℝ) (ht : 0 < t) :
    contact mu A B q p k 0 (path e t) = contact mu A B q p k 0 base := by
  have hp : Tendsto (path e) (𝓝 1) (𝓝 (base (n := n))) := by
    simpa only [path_one] using (path_continuous e).continuousAt.tendsto (x := (1 : ℝ))
  have hnear := hp.eventually (affine_local_constant mu A B hA hB q p k hmax)
  have he : (fun s => compressionArea mu B e s⁻¹ + q + k * (compressionArea mu A e s - p))
      =ᶠ[𝓝 1] (fun _ => contact mu A B q p k 0 base) := by
    filter_upwards [hnear, isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi 0 by norm_num)] with s hs hpos
    rw [← contact_path mu A B hB q p k e s hpos]
    exact hs
  rw [contact_path mu A B hB q p k e t ht]
  exact (analytic_affine_path mu A B q p k e).eqOn_of_preconnected_of_eventuallyEq
    (fun _ _ => analyticAt_const) (convex_Ioi (0 : ℝ)).isPreconnected
    (by norm_num : (1 : ℝ) ∈ Ioi 0) he ht

end ShadowVerification.AffineContact
#print axioms ShadowVerification.AffineContact.dilation_inner
#print axioms ShadowVerification.AffineContact.dual_compression
#print axioms ShadowVerification.AffineContact.affine_local_constant
#print axioms ShadowVerification.AffineContact.dual_path
#print axioms ShadowVerification.AffineContact.contact_path
#print axioms ShadowVerification.AffineContact.analytic_affine_path
#print axioms ShadowVerification.AffineContact.affine_compression_constant

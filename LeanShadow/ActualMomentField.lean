import LeanShadow.ActualContactOperator

/-! # A continuous extension of the actual transformed moment field

The extension is defined by the first Fréchet derivatives of actual primal
area. At every invertible parameter the previously checked reconstruction
identifies it with the centered moment of the transformed set. Its local
continuity follows from joint C² area regularity. No boundary regularity or
continuity of a family of optimizing sets is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set MeasureTheory Filter
open scoped BigOperators Topology Matrix.Norms.Frobenius
namespace ShadowVerification.MomentField
open ActualContact ContactOperator FullFrame Coordinates Spherical Projective AmbientArea Integrated
open WeightedFlow WeightedFrame FullWeight
open _root_.ShadowVerification.Frame _root_.ShadowVerification.Dual

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]

noncomputable def moment (A : Set (UnitSphere n)) (x : Ambient n) : Matrix n n ℝ :=
  ∑ i : FrobeniusIndex n,
    fderiv ℝ (primal mu A) x (symmetricFields i x) • frame (frobeniusBasis (n := n)) i

theorem moment_point (A : Set (UnitSphere n)) (hA : MeasurableSet A)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) :
    moment mu A (point T) = Paired.actualMoment mu (action T '' A) := by
  have ha := (primal_contDiffAt mu A T).differentiableAt (by norm_num)
  have he (i : FrobeniusIndex n) :
      fderiv ℝ (primal mu A) (point T) (symmetricFields i (point T)) =
        Paired.actualFirst mu (action T '' A) i := by
    rw [← Curves.firstLine_eq_fderiv _ _ _ ha, ← Curves.flow_first_deriv _ _ _ ha]
    exact first_primal mu A hA T _
  simp only [moment, he]
  exact Paired.actual_first_reconstruction mu _ (measurable_action_image T A hA)

theorem moment_continuousAt (A : Set (UnitSphere n))
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) :
    ContinuousAt (moment mu A) (point T) := by
  have hder : ContinuousAt (fderiv ℝ (primal mu A)) (point T) :=
    ((primal_contDiffAt mu A T).fderiv_right (m := 1) (by norm_num)).continuousAt
  have hterm (i : FrobeniusIndex n) : ContinuousAt
      (fun x => fderiv ℝ (primal mu A) x (symmetricFields i x) •
        frame (frobeniusBasis (n := n)) i) (point T) :=
    (hder.clm_apply (symmetricFields i).continuous.continuousAt).smul continuousAt_const
  unfold moment
  fun_prop

noncomputable def coefficients (A : Set (UnitSphere n)) (L : ℝ) :
    Ambient n → Matrix (FullIndex n) (FullIndex n) ℝ := geometricWeight (moment mu A) L

noncomputable def drift (A : Set (UnitSphere n)) (L : ℝ) (x : Ambient n) : Ambient n :=
  acceleration (coefficients mu A L) fullFields x +
    traceDrift (1 - L • moment mu A x) (((Fintype.card n : ℝ) - 2) / 2) x

theorem coefficients_continuousAt (A : Set (UnitSphere n)) (L : ℝ)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) (i j : FullIndex n) :
    ContinuousAt (fun x => coefficients mu A L x i j) (point T) :=
  geometricWeight_continuousAt (moment mu A) L _ (moment_continuousAt mu A T) i j

theorem drift_continuousAt (A : Set (UnitSphere n)) (L : ℝ)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) :
    ContinuousAt (drift mu A L) (point T) := by
  have hc := coefficients_continuousAt mu A L T
  have hm (i j : n) : ContinuousAt (fun x => moment mu A x i j) (point T) :=
    (matrix_entry_continuous i j).continuousAt.comp (moment_continuousAt mu A T)
  unfold drift acceleration traceDrift Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

/-- The source bound holds for the actual variable coefficients at every
invertible point, with no assumed operator-identification formula. -/
theorem variable_source (A B : Set (UnitSphere n))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (q p k rho L : ℝ)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n)
    (hrho : 0 ≤ rho) (hL : 0 ≤ L)
    (hcoefficient : 2 * rho ≤ ((Fintype.card n : ℝ) - 2) * L *
      Contact.slope p k rho (primal mu A (point T)))
    (hsmall : L * ‖moment mu A (point T)‖ ≤ 1 / 2) :
    rho / 2 * ‖moment mu A (point T)‖ ^ 2 ≤
      op (coefficients mu A L) (fun i x => fullFields i x) (drift mu A L)
        (contact mu A B q p k rho) (point T) := by
  have hh := actual_full_source mu A B hA hB q p k rho L T hrho hL hcoefficient
    (by simpa only [moment_point mu A hA T] using hsmall)
  simpa only [op, drift, acceleration, coefficients, geometricWeight, moment_point mu A hA T] using hh

omit [Nonempty n] [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)] in
/-- Every nearby parameter is represented by an actual invertible map. -/
theorem eventually_point (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) :
    ∀ᶠ x in 𝓝 (point T), ∃ U : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n, point U = x := by
  have hT : coordinateEquiv (point T) ∈ Regularity.invertibleDomain := by
    rw [coordinate_point]
    exact Regularity.equiv_mem_invertibleDomain T
  have hh := (coordinateEquiv (n := n)).continuous.continuousAt.preimage_mem_nhds
    (Regularity.isOpen_invertibleDomain.mem_nhds hT)
  filter_upwards [hh] with x hx
  obtain ⟨u, hu⟩ := hx
  refine ⟨ContinuousLinearEquiv.ofUnit u, ?_⟩
  apply coordinateEquiv.injective
  rw [coordinate_point]
  exact hu

/-- Isotropy and a positive support slope supply actual local source data.
The neighborhood and the positive weight scale are conclusions. -/
theorem local_source_at_isotropic (A B : Set (UnitSphere n))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (q p k rho : ℝ)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n)
    (hn : (2 : ℝ) < Fintype.card n) (hrho : 0 < rho)
    (hslope : 0 < Contact.slope p k rho (primal mu A (point T)))
    (hiso : moment mu A (point T) = 0) :
    ∃ L > 0, ∀ᶠ x in 𝓝 (point T),
      (coefficients mu A L x).PosDef ∧ ContDiffAt ℝ 2 (contact mu A B q p k rho) x ∧
      rho / 2 * ‖moment mu A x‖ ^ 2 ≤
        op (coefficients mu A L) (fun i y => fullFields i y) (drift mu A L)
          (contact mu A B q p k rho) x := by
  let d := (Fintype.card n : ℝ) - 2
  let s := Contact.slope p k rho (primal mu A (point T))
  have hd : 0 < d := sub_pos.mpr hn
  have hs : 0 < s := hslope
  let L := 4 * rho / (d * s)
  have hL : 0 < L := by dsimp [L]; positivity
  have hval : d * L * s = 4 * rho := by
    dsimp [L]
    field_simp
  have hgap : 2 * rho < d * L * s := by rw [hval]; linarith
  have ha := (primal_contDiffAt mu A T).continuousAt
  have hc : ContinuousAt (fun x => d * L * Contact.slope p k rho (primal mu A x)) (point T) := by
    unfold Contact.slope
    fun_prop
  have hnearC : ∀ᶠ x in 𝓝 (point T), 2 * rho < d * L * Contact.slope p k rho (primal mu A x) :=
    hc.eventually (eventually_gt_nhds hgap)
  have hm : ContinuousAt (fun x => L * ‖moment mu A x‖) (point T) :=
    continuousAt_const.mul (moment_continuousAt mu A T).norm
  have hsmall : L * ‖moment mu A (point T)‖ < 1 / 2 := by rw [hiso]; norm_num
  have hnearM := hm.eventually (eventually_lt_nhds hsmall)
  refine ⟨L, hL, ?_⟩
  filter_upwards [eventually_point T, hnearC, hnearM] with x hx hcx hmx
  obtain ⟨U, rfl⟩ := hx
  refine ⟨geometricWeight_posDef (moment mu A) L _ hL.le hmx.le,
    contact_contDiffAt mu A B q p k rho U, ?_⟩
  exact variable_source mu A B hA hB q p k rho L U hrho.le hL.le hcx.le hmx.le

end ShadowVerification.MomentField
#print axioms ShadowVerification.MomentField.moment_point
#print axioms ShadowVerification.MomentField.moment_continuousAt
#print axioms ShadowVerification.MomentField.coefficients_continuousAt
#print axioms ShadowVerification.MomentField.drift_continuousAt
#print axioms ShadowVerification.MomentField.variable_source

#print axioms ShadowVerification.MomentField.eventually_point
#print axioms ShadowVerification.MomentField.local_source_at_isotropic

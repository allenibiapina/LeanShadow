import LeanShadow.CompactFrechetIntegral

/-! # Joint regularity supplies the derivative families needed for integration

Partial derivatives below are actual Fréchet derivatives. Their joint
regularity is derived from that of the original integrand. A continuous
map from a compact measured space into the second variable allows the
result to apply to the unit sphere without choosing charts on the sphere.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology

namespace ShadowVerification.Joint

variable {P Y F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def partialDerivative (F₀ : P → Y → F) (p : P) (y : Y) : P →L[ℝ] F :=
  fderiv ℝ (fun q => F₀ q y) p

/-- Taking the partial derivative in the first variable loses one order of
joint regularity. The second variable is retained as a genuine parameter. -/
theorem contDiffAt_partialDerivative (k : ℕ) (F₀ : P → Y → F) (p : P) (y : Y)
    (hF : ContDiffAt ℝ (k + 1) (Function.uncurry F₀) (p, y)) :
    ContDiffAt ℝ k (Function.uncurry (partialDerivative F₀)) (p, y) := by
  have hlift : ContDiffAt ℝ (k + 1)
      (Function.uncurry (fun z : P × Y => fun q : P => F₀ q z.2)) ((p, y), p) := by
    exact hF.comp ((p, y), p) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact hlift.fderiv contDiffAt_fst (by simp)

/-- The partial derivative is a derivative of the actual fixed-fibre function. -/
theorem hasFDerivAt_fibre (F₀ : P → Y → F) (p : P) (y : Y)
    (hF : ContDiffAt ℝ 1 (Function.uncurry F₀) (p, y)) :
    HasFDerivAt (fun q => F₀ q y) (partialDerivative F₀ p y) p := by
  have hc : ContDiffAt ℝ 1 (fun q => F₀ q y) p :=
    hF.comp p (contDiffAt_id.prodMk contDiffAt_const)
  exact (hc.differentiableAt (by norm_num)).hasFDerivAt

variable {X : Type*} [TopologicalSpace X]

omit [NormedSpace ℝ P] [NormedSpace ℝ Y] [NormedSpace ℝ F] in
/-- Pulling back a jointly continuous family along a continuous fibre map. -/
theorem continuousOn_fibre_pullback (U : Set P) (F₀ : P → Y → F)
    (e : X → Y) (he : Continuous e)
    (hF : ∀ p ∈ U, ∀ x, ContinuousAt (Function.uncurry F₀) (p, e x)) :
    ContinuousOn (fun z : P × X => F₀ z.1 (e z.2)) (U ×ˢ univ) := by
  intro z hz
  exact ((hF z.1 hz.1 z.2).comp
    (f := fun w : P × X => (w.1, e w.2))
    (continuousAt_fst.prodMk (he.continuousAt.comp continuousAt_snd))).continuousWithinAt

variable [ProperSpace P]
  [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

/-- Joint `C²` regularity of the actual integrand on an open parameter
domain gives `C²` regularity of its compact-fibre integral. All derivative
families and their domination bounds are constructed by the proof. -/
theorem contDiffOn_integral_joint (mu : Measure X) [IsFiniteMeasure mu]
    (U : Set P) (hU : IsOpen U) (F₀ : P → Y → F) (e : X → Y) (he : Continuous e)
    (hF : ∀ p ∈ U, ∀ x, ContDiffAt ℝ 2 (Function.uncurry F₀) (p, e x)) :
    ContDiffOn ℝ 2 (fun p => ∫ x, F₀ p (e x) ∂mu) U := by
  let D := partialDerivative F₀
  let DD := partialDerivative D
  have hD : ∀ p ∈ U, ∀ x, ContDiffAt ℝ 1 (Function.uncurry D) (p, e x) :=
    fun p hp x => contDiffAt_partialDerivative 1 F₀ p (e x) (hF p hp x)
  have hDD : ∀ p ∈ U, ∀ x, ContDiffAt ℝ 0 (Function.uncurry DD) (p, e x) :=
    fun p hp x => contDiffAt_partialDerivative 0 D p (e x) (hD p hp x)
  apply Parametric.contDiffOn_two_integral_compact mu U hU
    (fun p x => F₀ p (e x)) (fun p x => D p (e x)) (fun p x => DD p (e x))
  · exact continuousOn_fibre_pullback U F₀ e he (fun p hp x => (hF p hp x).continuousAt)
  · exact continuousOn_fibre_pullback U D e he (fun p hp x => (hD p hp x).continuousAt)
  · exact continuousOn_fibre_pullback U DD e he (fun p hp x => (hDD p hp x).continuousAt)
  · exact fun p hp x => hasFDerivAt_fibre F₀ p (e x) ((hF p hp x).of_le (by norm_num))
  · exact fun p hp x => hasFDerivAt_fibre D p (e x) (hD p hp x)

end ShadowVerification.Joint

#print axioms ShadowVerification.Joint.contDiffAt_partialDerivative
#print axioms ShadowVerification.Joint.hasFDerivAt_fibre
#print axioms ShadowVerification.Joint.continuousOn_fibre_pullback
#print axioms ShadowVerification.Joint.contDiffOn_integral_joint

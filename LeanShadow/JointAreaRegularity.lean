import LeanShadow.JointDifferentiation
import LeanShadow.AreaVariations

/-! # Joint C² regularity of actual transformed area

The parameter is the entire space of continuous linear operators, not a
single exponential direction. Invertible operators form an open domain.
On that domain the inverse-norm density is jointly smooth in the operator
and the nonzero vector. Compact-fibre integration therefore gives C²
regularity of its integral against any finite spherical measure.

Actual image area is represented by the ratio of the set's density integral
and the whole sphere's density integral. The proved change-of-measure formula
identifies this ratio with image measure and shows its denominator is nonzero.
Thus the C² statement concerns an explicit extension of actual image area.
No boundary regularity of the Borel set is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Topology

namespace ShadowVerification.Regularity
open Spherical Projective

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def invertibleDomain : Set (E →L[ℝ] E) := {L | IsUnit L}

/-- A unit in the operator algebra acts injectively on vectors. -/
theorem unit_operator_injective (L : E →L[ℝ] E) (hL : IsUnit L) :
    Function.Injective L := by
  rcases hL with ⟨u, rfl⟩
  exact (ContinuousLinearEquiv.ofUnit u).injective

theorem equiv_mem_invertibleDomain (T : E ≃L[ℝ] E) :
    (T : E →L[ℝ] E) ∈ invertibleDomain :=
  ⟨T.toUnit, rfl⟩

noncomputable def operatorDensity (N : ℕ) (L : E →L[ℝ] E) (x : E) : ℝ :=
  ‖L x‖⁻¹ ^ N

/-- The actual inverse-norm density is jointly C^k away from its zero locus. -/
theorem contDiffAt_operatorDensity (N k : ℕ) (L : E →L[ℝ] E) (x : E) (hx : L x ≠ 0) :
    ContDiffAt ℝ k (Function.uncurry (operatorDensity N)) (L, x) := by
  exact (((contDiffAt_fst.clm_apply contDiffAt_snd).norm ℝ hx).inv
    (norm_ne_zero_iff.mpr hx)).pow N

variable [FiniteDimensional ℝ E]

theorem isOpen_invertibleDomain : IsOpen (invertibleDomain (E := E)) := Units.isOpen

variable [MeasurableSpace E] [BorelSpace E]

noncomputable def operatorDensityIntegral (nu : Measure (Sphere E)) (N : ℕ)
    (L : E →L[ℝ] E) : ℝ :=
  ∫ x : Sphere E, operatorDensity N L (x : E) ∂nu

/-- Joint C² regularity holds for any finite Borel measure on the sphere. -/
theorem contDiffOn_operatorDensityIntegral (nu : Measure (Sphere E)) [IsFiniteMeasure nu]
    (N : ℕ) : ContDiffOn ℝ 2 (operatorDensityIntegral nu N) invertibleDomain := by
  let : CompactSpace (Sphere E) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E) 1)
  apply Joint.contDiffOn_integral_joint nu invertibleDomain isOpen_invertibleDomain
    (operatorDensity N) (fun x : Sphere E => (x : E)) continuous_subtype_val
  intro L hL x
  apply contDiffAt_operatorDensity
  simpa only [map_zero] using (unit_operator_injective L hL).ne (unit_ne_zero x)

theorem contDiffAt_operatorDensityIntegral (nu : Measure (Sphere E)) [IsFiniteMeasure nu]
    (N : ℕ) (T : E ≃L[ℝ] E) :
    ContDiffAt ℝ 2 (operatorDensityIntegral nu N) (T : E →L[ℝ] E) :=
  (contDiffOn_operatorDensityIntegral nu N).contDiffAt
    (isOpen_invertibleDomain.mem_nhds (equiv_mem_invertibleDomain T))

variable [Nontrivial E] (mu : Measure E) [mu.IsAddHaarMeasure]

/-- The whole-sphere formula provides the normalization at every invertible operator. -/
theorem whole_operator_integral_identity (T : E ≃L[ℝ] E) :
    |LinearMap.det (T : E →ₗ[ℝ] E)| *
      operatorDensityIntegral (probability mu) (Module.finrank ℝ E) (T : E →L[ℝ] E) = 1 := by
  have h := Radial.transformedArea_integral mu T univ MeasurableSet.univ
  simpa only [transformedArea_univ, setIntegral_univ, operatorDensityIntegral,
    operatorDensity] using! h.symm

theorem whole_operator_integral_ne_zero (T : E ≃L[ℝ] E) :
    operatorDensityIntegral (probability mu) (Module.finrank ℝ E) (T : E →L[ℝ] E) ≠ 0 := by
  intro hz
  have h := whole_operator_integral_identity mu T
  rw [hz, mul_zero] at h
  exact zero_ne_one h

/-- An explicit real-valued function on the entire operator space. Its
agreement with actual image area is proved on the invertible domain. -/
noncomputable def areaExtension (A : Set (Sphere E)) (L : E →L[ℝ] E) : ℝ :=
  operatorDensityIntegral ((probability mu).restrict A) (Module.finrank ℝ E) L /
    operatorDensityIntegral (probability mu) (Module.finrank ℝ E) L

theorem transformedArea_eq_extension (A : Set (Sphere E)) (hA : MeasurableSet A)
    (T : E ≃L[ℝ] E) :
    transformedArea mu A T = areaExtension mu A (T : E →L[ℝ] E) := by
  unfold areaExtension
  apply (eq_div_iff (whole_operator_integral_ne_zero mu T)).mpr
  rw [Radial.transformedArea_integral mu T A hA]
  change (_ * operatorDensityIntegral ((probability mu).restrict A)
    (Module.finrank ℝ E) (T : E →L[ℝ] E)) * _ = _
  rw [mul_right_comm, whole_operator_integral_identity, one_mul]

/-- Actual image area has an explicit jointly C² extension near every
invertible operator. This is stronger than smoothness on individual flows. -/
theorem contDiffAt_areaExtension (A : Set (Sphere E)) (T : E ≃L[ℝ] E) :
    ContDiffAt ℝ 2 (areaExtension mu A) (T : E →L[ℝ] E) := by
  exact (contDiffAt_operatorDensityIntegral ((probability mu).restrict A)
    (Module.finrank ℝ E) T).div
      (contDiffAt_operatorDensityIntegral (probability mu) (Module.finrank ℝ E) T)
      (whole_operator_integral_ne_zero mu T)

end ShadowVerification.Regularity

#print axioms ShadowVerification.Regularity.unit_operator_injective
#print axioms ShadowVerification.Regularity.equiv_mem_invertibleDomain
#print axioms ShadowVerification.Regularity.contDiffAt_operatorDensity
#print axioms ShadowVerification.Regularity.isOpen_invertibleDomain
#print axioms ShadowVerification.Regularity.contDiffOn_operatorDensityIntegral
#print axioms ShadowVerification.Regularity.contDiffAt_operatorDensityIntegral
#print axioms ShadowVerification.Regularity.whole_operator_integral_identity
#print axioms ShadowVerification.Regularity.whole_operator_integral_ne_zero
#print axioms ShadowVerification.Regularity.transformedArea_eq_extension
#print axioms ShadowVerification.Regularity.contDiffAt_areaExtension

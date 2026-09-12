import LeanShadow.RadialChange
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! # Null spherical sections of proper linear subspaces

Polar integration transfers the ambient Haar-nullity of a proper subspace to
the spherical measure. In dimension at least two, this proves that singletons
have zero spherical measure. No formula for the area of a cap is needed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ENNReal
namespace ShadowVerification.SphericalNull
open Spherical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

/-- A proper ambient linear subspace has a null spherical section. -/
theorem subspace_section_null (V : Submodule ℝ E) (hV : V ≠ ⊤) :
    probability mu {x : Sphere E | (x : E) ∈ V} = 0 := by
  let A : Set (Sphere E) := {x | (x : E) ∈ V}
  have hA : MeasurableSet A :=
    V.closed_of_finiteDimensional.measurableSet.preimage continuous_subtype_val.measurable
  have hc : Radial.cone A (fun _ => ⟨1, by norm_num⟩) ⊆ (V : Set E) := by
    rw [Radial.cone_as_image]
    rintro _ ⟨⟨x, r⟩, ⟨hx, _⟩, rfl⟩
    exact V.smul_mem r.val hx
  have hz := measure_mono_null hc (Measure.addHaar_submodule mu V hV)
  have hs := Radial.cone_one_measure mu A hA
  rw [hz, mul_zero] at hs
  change ((mu.toSphere univ)⁻¹ • mu.toSphere) A = 0
  simp only [Measure.smul_apply, smul_eq_mul, ← hs, mul_zero]

/-- Every spherical singleton is null when the ambient dimension exceeds one. -/
theorem singleton_null (hd : 1 < Module.finrank ℝ E) (x : Sphere E) :
    probability mu {x} = 0 := by
  let V : Submodule ℝ E := ℝ ∙ (x : E)
  have hV : V ≠ ⊤ := by
    intro heq
    have hf := finrank_span_singleton (K := ℝ) (unit_ne_zero x)
    change Module.finrank ℝ V = 1 at hf
    rw [heq, finrank_top] at hf
    omega
  apply measure_mono_null _ (subspace_section_null mu V hV)
  intro y hy
  have heq := mem_singleton_iff.mp hy
  subst y
  exact Submodule.mem_span_singleton_self (x : E)

/-- The nonatomicity input for exact trimming is supplied by spherical geometry. -/
theorem nullSingletonClass (hd : 1 < Module.finrank ℝ E) :
    NullSingletonClass (probability mu) :=
  ⟨singleton_null mu hd⟩

end ShadowVerification.SphericalNull
#print axioms ShadowVerification.SphericalNull.subspace_section_null
#print axioms ShadowVerification.SphericalNull.singleton_null
#print axioms ShadowVerification.SphericalNull.nullSingletonClass

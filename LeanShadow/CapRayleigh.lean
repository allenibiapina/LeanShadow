import LeanShadow.SphericalMomentBound
import LeanShadow.PairedAreaVariation

/-! # The sharp lower Rayleigh bound for the actual centered moment matrix -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
namespace ShadowVerification.CapRayleigh
open Spherical Integrated Paired SphericalCaps SphericalMomentBound CapFunctions
variable {n : Type*} [Fintype n] [DecidableEq n]

def rayleighLinear (z : n → ℝ) : Matrix n n ℝ →ₗ[ℝ] ℝ where
  toFun M := z ⬝ᵥ (M *ᵥ z)
  map_add' M N := by simp only [Matrix.add_mulVec,dotProduct_add]
  map_smul' c M := by simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul,RingHom.id_apply]

omit [DecidableEq n] in
theorem unit_rep (z : n → ℝ) (hz : z ⬝ᵥ z = 1) :
    ∃ a : UnitSphere n, ⇑(a : EuclideanSpace ℝ n) = z := by
  let v : EuclideanSpace ℝ n := WithLp.toLp 2 z
  have hv : ‖v‖ = 1 := by
    have h : inner ℝ v v = 1 := by simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial] using hz
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg v]
  exact ⟨⟨v,mem_sphere_zero_iff_norm.mpr hv⟩,rfl⟩

variable [Nonempty n] [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]

theorem rayleigh_identity (A : Set (UnitSphere n)) (a : UnitSphere n) :
    ⇑(a : EuclideanSpace ℝ n) ⬝ᵥ (actualMoment mu A *ᵥ ⇑(a : EuclideanSpace ℝ n)) =
      area mu A - (Fintype.card n : ℝ) *
        ∫ x in A, (inner ℝ (a : EuclideanSpace ℝ n) (x : EuclideanSpace ℝ n)) ^ 2 ∂probability mu := by
  let L := (rayleighLinear ⇑(a : EuclideanSpace ℝ n)).toContinuousLinearMap
  have hi := L.integral_comp_comm (sphere_integrable_continuous
    ((probability mu).restrict A) _ continuous_momentDensity)
  change L (∫ x in A, momentDensity ⇑(x : EuclideanSpace ℝ n) ∂probability mu) = _
  rw [← hi]
  have he : (fun x : UnitSphere n => L (momentDensity ⇑(x : EuclideanSpace ℝ n))) =
      fun x : UnitSphere n => 1 - (Fintype.card n : ℝ) * (inner ℝ (a : EuclideanSpace ℝ n) (x : EuclideanSpace ℝ n)) ^ 2 := by
    funext x
    change ⇑(a : EuclideanSpace ℝ n) ⬝ᵥ
      ((1 - (Fintype.card n : ℝ) • vecMulVec ⇑(x : EuclideanSpace ℝ n) ⇑(x : EuclideanSpace ℝ n)) *ᵥ
        ⇑(a : EuclideanSpace ℝ n)) = _
    simp only [Matrix.sub_mulVec,Matrix.one_mulVec,dotProduct_sub,Coordinates.sphere_dot_self,
      Matrix.smul_mulVec,Matrix.vecMulVec_mulVec,dotProduct_smul,smul_eq_mul,
      EuclideanSpace.inner_eq_star_dotProduct,star_trivial,op_smul_eq_mul]
    rw [dotProduct_comm ⇑(a : EuclideanSpace ℝ n) ⇑(x : EuclideanSpace ℝ n)]
    ring
  rw [he,integral_sub (integrable_const _) ((sphere_integrable_continuous
    ((probability mu).restrict A) _ (by fun_prop)).const_mul _),integral_const_mul]
  simp only [integral_const,smul_eq_mul,mul_one,measureReal_def,Measure.restrict_apply_univ,area]

theorem sharp_rayleigh (hd : 1 < Module.finrank ℝ (EuclideanSpace ℝ n))
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) (A : Set (UnitSphere n)) (hA : MeasurableSet A)
    (hmass : area mu A = capMass (Fintype.card n - 2) r)
    (z : n → ℝ) (hz : z ⬝ᵥ z = 1) :
    -momentBound (Fintype.card n - 2) r ≤ z ⬝ᵥ (actualMoment mu A *ᵥ z) := by
  obtain ⟨a,rfl⟩ := unit_rep z hz
  rw [rayleigh_identity,hmass]
  have h := moment_maximal mu hd a r hr A hA (by simpa using hmass)
  have he := moment_identity (Fintype.card n - 2) r
  have hn : Fintype.card n - 2 + 2 = Fintype.card n := by
    have hh : 1 < Fintype.card n := by simpa using hd
    omega
  rw [hn] at he
  simp only [finrank_euclideanSpace] at h
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card n)]

theorem sharp_rayleigh_equality (hd : 1 < Module.finrank ℝ (EuclideanSpace ℝ n))
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) (A : Set (UnitSphere n)) (hA : MeasurableSet A)
    (hmass : area mu A = capMass (Fintype.card n - 2) r)
    (a : UnitSphere n)
    (heq : ⇑(a : EuclideanSpace ℝ n) ⬝ᵥ (actualMoment mu A *ᵥ ⇑(a : EuclideanSpace ℝ n)) =
      -momentBound (Fintype.card n - 2) r) : A =ᵐ[probability mu] cap a r := by
  apply moment_equality mu hd a r hr A hA (by simpa using hmass)
  rw [rayleigh_identity,hmass] at heq
  have he := moment_identity (Fintype.card n - 2) r
  have hn : Fintype.card n - 2 + 2 = Fintype.card n := by
    have hh : 1 < Fintype.card n := by simpa using hd
    omega
  rw [hn] at he
  have hpos : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  simp only [finrank_euclideanSpace]
  nlinarith

end ShadowVerification.CapRayleigh
#print axioms ShadowVerification.CapRayleigh.unit_rep
#print axioms ShadowVerification.CapRayleigh.rayleigh_identity
#print axioms ShadowVerification.CapRayleigh.sharp_rayleigh
#print axioms ShadowVerification.CapRayleigh.sharp_rayleigh_equality

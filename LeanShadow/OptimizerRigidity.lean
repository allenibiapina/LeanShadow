import LeanShadow.SharpProfile

/-! # Every interior optimizer is a cap modulo a null set -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Matrix
open scoped Topology BigOperators
namespace ShadowVerification.OptimizerRigidity
open Spherical Profile Integrated Paired CapFunctions CapRadius CapModel

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]
  (hdim : 2 < Module.finrank ℝ (EuclideanSpace ℝ n))

include hdim

theorem optimizer_eq_cap (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (A : Set (UnitSphere n)) (hA : IsOptimizer mu p A) :
    ∃ a : UnitSphere n, A =ᵐ[probability mu] SphericalCaps.cap a (radius (Fintype.card n - 2) p) := by
  let m := Fintype.card n - 2
  have hn : 2 ≤ Fintype.card n := by simpa using hdim.le
  have hnpos : 0 < m := by
    have hh : 2 < Fintype.card n := by simpa using hdim
    dsimp [m]
    omega
  have hk := slope_pos m p hp
  have hD := bound_pos m p hp
  have hC : 0 < (m : ℝ) * slope m p := mul_pos (Nat.cast_pos.mpr hnpos) hk
  obtain ⟨d,z,hd,hz,heigen,hbound⟩ := ProfileVariations.optimizer_spectral_bound mu hdim p hp A hA
    (slope m p) ((m : ℝ) * slope m p / bound m p)
    (SharpProfile.profile_quadratic_expansion mu hdim p hp) hk
  have hcast : (Fintype.card n : ℝ) - 2 = (m : ℝ) := by
    simp only [m,Nat.cast_sub hn,Nat.cast_ofNat]
  rw [hcast] at hbound
  have hdD : d ≤ bound m p := rayleigh_bound_for_negative_eigenvalue _ z d (bound m p) hz heigen
    (ProfileCapInequality.moment_bound_at_mass mu (by omega) p ⟨hp.1.le,hp.2.le⟩ A hA.measurable hA.mass)
  have hDd : bound m p ≤ d := by
    have hh := (div_le_div_iff₀ hd hD).mp hbound
    nlinarith
  have heq : d = bound m p := le_antisymm hdD hDd
  obtain ⟨a,ha⟩ := CapRayleigh.unit_rep z hz
  refine ⟨a,CapRayleigh.sharp_rayleigh_equality mu (by omega) (radius m p)
    (radius_mem m p) A hA.measurable (hA.mass.trans (mass_radius m p ⟨hp.1.le,hp.2.le⟩).symm) a ?_⟩
  rw [ha,heigen,dotProduct_smul,hz,smul_eq_mul,mul_one,heq]
  rfl

theorem borel_shadow_bound (A : Set (UnitSphere n)) (hA : MeasurableSet A)
    (hanti : Antipodal.IsAntipodal A) :
    model (Fintype.card n - 2) (area mu A) ≤ area mu (shadow A) := by
  rw [← SharpProfile.profile_eq_model mu hdim _ ⟨area_nonneg mu A,area_le_one mu A⟩]
  exact profile_le_shadow mu A hA hanti

theorem borel_shadow_equality (A : Set (UnitSphere n)) (hA : MeasurableSet A)
    (hanti : Antipodal.IsAntipodal A) (hp : area mu A ∈ Ioo (0 : ℝ) 1)
    (heq : area mu (shadow A) = model (Fintype.card n - 2) (area mu A)) :
    ∃ a : UnitSphere n, A =ᵐ[probability mu] SphericalCaps.cap a (radius (Fintype.card n - 2) (area mu A)) := by
  apply optimizer_eq_cap mu hdim (area mu A) hp A
  refine ⟨hA,hanti,rfl,?_⟩
  exact heq.trans (SharpProfile.profile_eq_model mu hdim _ ⟨hp.1.le,hp.2.le⟩).symm

end ShadowVerification.OptimizerRigidity
#print axioms ShadowVerification.OptimizerRigidity.optimizer_eq_cap
#print axioms ShadowVerification.OptimizerRigidity.borel_shadow_bound
#print axioms ShadowVerification.OptimizerRigidity.borel_shadow_equality

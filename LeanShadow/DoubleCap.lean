import LeanShadow.SharpShadow

/-! # The double-cap bound, attaining independent examples, and rigidity -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.DoubleCap
open Spherical Antipodal ShadowRegularity CapFunctions CapRadius CapModel SphericalCaps

def delta (m : ℕ) : ℝ := capMass m (Real.pi/4)

theorem quarter_pi_mem : Real.pi/4 ∈ Ioo (0 : ℝ) (Real.pi/2) := by
  constructor <;> linarith [Real.pi_pos]

theorem delta_mem (m : ℕ) : delta m ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · have h := capMass_strictMono m ⟨le_rfl,by positivity⟩
      ⟨quarter_pi_mem.1.le,quarter_pi_mem.2.le⟩ quarter_pi_mem.1
    simpa only [capMass_zero,delta] using h
  · have h := capMass_strictMono m ⟨quarter_pi_mem.1.le,quarter_pi_mem.2.le⟩
      ⟨by positivity,le_rfl⟩ quarter_pi_mem.2
    simpa only [capMass_half_pi,delta] using h

theorem model_delta (m : ℕ) : model m (delta m) = 1 - delta m := by
  rw [delta,model_mass m _ ⟨quarter_pi_mem.1.le,quarter_pi_mem.2.le⟩,beltMass_complement]
  congr 2
  ring

theorem budget_implies_bound (m : ℕ) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (hbudget : model m p + p ≤ 1) : p ≤ delta m := by
  by_contra! h
  have hm := SharpProfile.model_strictMono m ⟨(delta_mem m).1.le,(delta_mem m).2.le⟩ hp h
  rw [model_delta] at hm
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem orthogonal_axis_sq_sum_le_one (a x y : Sphere E)
    (hxy : inner ℝ (x : E) (y : E) = 0) :
    (inner ℝ (a : E) (x : E))^2 + (inner ℝ (a : E) (y : E))^2 ≤ 1 := by
  have hunit (z : Sphere E) : inner ℝ (z : E) (z : E) = 1 := by
    rw [real_inner_self_eq_norm_sq,mem_sphere_zero_iff_norm.mp z.property]
    norm_num
  have h := @real_inner_self_nonneg E _ _
    ((a : E) - (inner ℝ (a : E) (x : E)) • (x : E) - (inner ℝ (a : E) (y : E)) • (y : E))
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right] at h
  rw [hunit a,hunit x,hunit y,hxy,real_inner_comm (a : E) (x : E),
    real_inner_comm (a : E) (y : E),real_inner_comm (x : E) (y : E),hxy] at h
  nlinarith

theorem open_caps_independent (a : Sphere E) : Avoids (cap a (Real.pi/4)) (cap a (Real.pi/4)) := by
  intro x hx y hy hxy
  have hx' := (SphericalMomentBound.cap_threshold a (Real.pi/4)
    ⟨quarter_pi_mem.1.le,quarter_pi_mem.2.le⟩ x).mp hx
  have hy' := (SphericalMomentBound.cap_threshold a (Real.pi/4)
    ⟨quarter_pi_mem.1.le,quarter_pi_mem.2.le⟩ y).mp hy
  have hc : Real.cos (Real.pi/4)^2 = 1/2 := by
    rw [Real.cos_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hc] at hx' hy'
  linarith [orthogonal_axis_sq_sum_le_one a x y hxy]

variable [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

theorem avoiding_inner_budget (A B : Set (Sphere E))
    (hB : NullMeasurableSet B (probability mu)) (hAB : Avoids A B) :
    innerArea mu (shadow A) + area mu B ≤ 1 := by
  have hsub : shadow A ⊆ Bᶜ := by
    rintro y ⟨x,hx,hxy⟩ hy
    exact hAB x hx y hy hxy
  have h : innerArea mu (shadow A) ≤ area mu Bᶜ :=
    (innerArea_le_area mu _).trans (measureReal_mono hsub)
  have hc : area mu Bᶜ = 1 - area mu B := probReal_compl_eq_one_sub₀ hB
  rw [hc] at h
  linarith

theorem open_caps_mass (hd : 1 < Module.finrank ℝ E) (a : Sphere E) :
    area mu (cap a (Real.pi/4)) = delta (Module.finrank ℝ E - 2) :=
  cap_area mu hd a _ ⟨quarter_pi_mem.1.le,quarter_pi_mem.2.le⟩

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]

theorem double_cap_bound (nu : Measure (EuclideanSpace ℝ n)) [nu.IsAddHaarMeasure]
    (hdim : 2 < Module.finrank ℝ (EuclideanSpace ℝ n))
    (A : Set (Sphere (EuclideanSpace ℝ n))) (hA : NullMeasurableSet A (probability nu))
    (hind : Avoids A A) : area nu A ≤ delta (Fintype.card n - 2) := by
  apply budget_implies_bound _ _ ⟨area_nonneg nu A,area_le_one nu A⟩
  have hlo := SharpShadow.arbitrary_shadow_inequality nu hdim A hA
  have hhi := avoiding_inner_budget nu A A hA hind
  linarith

theorem double_cap_equality (nu : Measure (EuclideanSpace ℝ n)) [nu.IsAddHaarMeasure]
    (hdim : 2 < Module.finrank ℝ (EuclideanSpace ℝ n))
    (A : Set (Sphere (EuclideanSpace ℝ n))) (hA : NullMeasurableSet A (probability nu))
    (hind : Avoids A A) (heq : area nu A = delta (Fintype.card n - 2)) :
    ∃ a : Sphere (EuclideanSpace ℝ n), A =ᵐ[probability nu] cap a (Real.pi/4) := by
  have hp : area nu A ∈ Ioo (0 : ℝ) 1 := heq.symm ▸ delta_mem _
  have hsh : innerArea nu (shadow A) = model (Fintype.card n - 2) (area nu A) := by
    apply le_antisymm _ (SharpShadow.arbitrary_shadow_inequality nu hdim A hA)
    have h := avoiding_inner_budget nu A A hA hind
    rw [heq,model_delta]
    rw [heq] at h
    linarith
  obtain ⟨a,ha⟩ := SharpShadow.arbitrary_shadow_equality nu hdim A hA hp hsh
  rw [heq,delta,radius_mass _ _ ⟨quarter_pi_mem.1.le,quarter_pi_mem.2.le⟩] at ha
  exact ⟨a,ha⟩

omit [DecidableEq n] in
theorem double_cap_attainment (nu : Measure (EuclideanSpace ℝ n)) [nu.IsAddHaarMeasure]
    (hdim : 2 < Module.finrank ℝ (EuclideanSpace ℝ n)) :
    ∃ A : Set (Sphere (EuclideanSpace ℝ n)), MeasurableSet A ∧ Avoids A A ∧
      area nu A = delta (Fintype.card n - 2) := by
  obtain ⟨a,ha⟩ : (Sphere (EuclideanSpace ℝ n)).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  let z : Sphere (EuclideanSpace ℝ n) := ⟨a,ha⟩
  exact ⟨cap z (Real.pi/4),cap_measurable _ _,open_caps_independent z,
    by simpa only [finrank_euclideanSpace] using open_caps_mass nu (by omega) z⟩

end ShadowVerification.DoubleCap
#print axioms ShadowVerification.DoubleCap.quarter_pi_mem
#print axioms ShadowVerification.DoubleCap.delta_mem
#print axioms ShadowVerification.DoubleCap.model_delta
#print axioms ShadowVerification.DoubleCap.budget_implies_bound
#print axioms ShadowVerification.DoubleCap.orthogonal_axis_sq_sum_le_one
#print axioms ShadowVerification.DoubleCap.open_caps_independent
#print axioms ShadowVerification.DoubleCap.avoiding_inner_budget
#print axioms ShadowVerification.DoubleCap.open_caps_mass
#print axioms ShadowVerification.DoubleCap.double_cap_bound
#print axioms ShadowVerification.DoubleCap.double_cap_equality
#print axioms ShadowVerification.DoubleCap.double_cap_attainment

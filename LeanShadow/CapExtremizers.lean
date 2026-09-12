import LeanShadow.DoubleCap
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Closed cap shadows, the extremal value, and the three-dimensional constant -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace ShadowVerification.CapExtremizers
open Spherical Antipodal ShadowRegularity CapFunctions CapRadius CapModel SphericalCaps DoubleCap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def closedCap (a : Sphere E) (r : ℝ) : Set (Sphere E) :=
  {x | Real.cos r ≤ |inner ℝ (a : E) (x : E)|}

theorem closedCap_closed (a : Sphere E) (r : ℝ) : IsClosed (closedCap a r) :=
  isClosed_le continuous_const (by fun_prop)

theorem closedCap_antipodal (a : Sphere E) (r : ℝ) : IsAntipodal (closedCap a r) := by
  intro x hx
  simpa only [closedCap,mem_ofPred_eq,antipode_coe,inner_neg_right,abs_neg] using hx

theorem shadow_closedCap_subset (a : Sphere E) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) :
    shadow (closedCap a r) ⊆ {y | |inner ℝ (a : E) (y : E)| ≤ Real.sin r} := by
  rintro y ⟨x,hx,hxy⟩
  have hb := orthogonal_axis_sq_sum_le_one a x y hxy
  have hc : 0 ≤ Real.cos r := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hr.1,Real.pi_pos],hr.2⟩
  have hs : 0 ≤ Real.sin r := Real.sin_nonneg_of_mem_Icc ⟨hr.1,by linarith [hr.2,Real.pi_pos]⟩
  change Real.cos r ≤ |inner ℝ (a : E) (x : E)| at hx
  change |inner ℝ (a : E) (y : E)| ≤ Real.sin r
  nlinarith [sq_abs (inner ℝ (a : E) (x : E)),sq_abs (inner ℝ (a : E) (y : E)),
    abs_nonneg (inner ℝ (a : E) (y : E)),Real.sin_sq_add_cos_sq r]

variable [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

theorem closedCap_ae_eq_open (hd : 1 < Module.finrank ℝ E) (a : Sphere E) (r : ℝ) :
    closedCap a r =ᵐ[probability mu] cap a r := by
  have hn : ∀ᵐ x : Sphere E ∂probability mu, |inner ℝ (a : E) (x : E)| ≠ Real.cos r := by
    simpa only [ae_iff,not_not] using SmallShadowCaps.abs_latitude_null mu hd a (Real.cos r)
  filter_upwards [hn] with x hx
  apply propext
  change Real.cos r ≤ |inner ℝ (a : E) (x : E)| ↔ Real.cos r < |inner ℝ (a : E) (x : E)|
  exact le_iff_lt_or_eq.trans (or_iff_left hx.symm)

theorem closedCap_mass (hd : 1 < Module.finrank ℝ E) (a : Sphere E) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) :
    area mu (closedCap a r) = capMass (Module.finrank ℝ E - 2) r := by
  change (probability mu).real _ = _
  rw [measureReal_congr (closedCap_ae_eq_open mu hd a r)]
  exact cap_area mu hd a r hr

theorem closed_belt_mass (hd : 1 < Module.finrank ℝ E) (a : Sphere E) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) :
    area mu {y : Sphere E | |inner ℝ (a : E) (y : E)| ≤ Real.sin r} =
      beltMass (Module.finrank ℝ E - 2) r := by
  have hn : ∀ᵐ y : Sphere E ∂probability mu, |inner ℝ (a : E) (y : E)| ≠ Real.sin r := by
    simpa only [ae_iff,not_not] using SmallShadowCaps.abs_latitude_null mu hd a (Real.sin r)
  have he : {y : Sphere E | |inner ℝ (a : E) (y : E)| ≤ Real.sin r} =ᵐ[probability mu]
      shadow (cap a r) := by
    rw [CapShadow.shadow_cap a r hr]
    filter_upwards [hn] with y hy
    exact propext (le_iff_lt_or_eq.trans (or_iff_left hy))
  change (probability mu).real _ = _
  rw [measureReal_congr he]
  exact CapShadow.shadow_cap_area mu hd a r hr

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]

theorem closedCap_attains (nu : Measure (EuclideanSpace ℝ n)) [nu.IsAddHaarMeasure]
    (hdim : 2 < Module.finrank ℝ (EuclideanSpace ℝ n))
    (a : Sphere (EuclideanSpace ℝ n)) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) :
    innerArea nu (shadow (closedCap a r)) =
      model (Fintype.card n - 2) (area nu (closedCap a r)) := by
  apply le_antisymm _ (SharpShadow.shadow_inequality nu hdim _
    (closedCap_closed a r).measurableSet.nullMeasurableSet (closedCap_antipodal a r))
  have hu := (innerArea_le_area nu (shadow (closedCap a r))).trans
    (show area nu (shadow (closedCap a r)) ≤ area nu {y | |inner ℝ (a : EuclideanSpace ℝ n) (y : EuclideanSpace ℝ n)| ≤ Real.sin r}
      from measureReal_mono (shadow_closedCap_subset a r hr))
  rw [closed_belt_mass nu (by omega) a r hr] at hu
  rw [closedCap_mass nu (by omega) a r hr]
  simpa only [finrank_euclideanSpace,model_mass _ r hr] using hu

def independentMasses (nu : Measure (EuclideanSpace ℝ n)) : Set ℝ :=
  {p | ∃ A : Set (Sphere (EuclideanSpace ℝ n)), NullMeasurableSet A (probability nu) ∧
    Avoids A A ∧ area nu A = p}

def alpha (nu : Measure (EuclideanSpace ℝ n)) : ℝ := sSup (independentMasses nu)

theorem double_cap_conjecture (nu : Measure (EuclideanSpace ℝ n)) [nu.IsAddHaarMeasure]
    (hdim : 2 < Module.finrank ℝ (EuclideanSpace ℝ n)) :
    IsGreatest (independentMasses nu) (delta (Fintype.card n - 2)) := by
  obtain ⟨A,hA,hi,hm⟩ := double_cap_attainment nu hdim
  refine ⟨⟨A,hA.nullMeasurableSet,hi,hm⟩,?_⟩
  rintro p ⟨B,hB,hBi,rfl⟩
  exact double_cap_bound nu hdim B hB hBi

theorem alpha_eq_delta (nu : Measure (EuclideanSpace ℝ n)) [nu.IsAddHaarMeasure]
    (hdim : 2 < Module.finrank ℝ (EuclideanSpace ℝ n)) : alpha nu = delta (Fintype.card n - 2) := by
  obtain ⟨A,hA,hi,hm⟩ := double_cap_attainment nu hdim
  have hmem : delta (Fintype.card n - 2) ∈ independentMasses nu := ⟨A,hA.nullMeasurableSet,hi,hm⟩
  have hbound : ∀ p ∈ independentMasses nu, p ≤ delta (Fintype.card n - 2) := by
    rintro p ⟨B,hB,hBi,rfl⟩
    exact double_cap_bound nu hdim B hB hBi
  exact le_antisymm (csSup_le ⟨_,hmem⟩ hbound) (le_csSup ⟨_,hbound⟩ hmem)

theorem capMass_dimension_three (r : ℝ) : capMass 1 r = 1 - Real.cos r := by
  simp only [capMass,normalizer,sinPrimitive,pow_one,integral_sin,Real.cos_zero,
    Real.cos_pi_div_two,sub_zero,inv_one,one_mul]

theorem delta_dimension_three : delta 1 = 1 - Real.sqrt 2 / 2 := by
  rw [delta,capMass_dimension_three,Real.cos_pi_div_four]

theorem beltMass_dimension_three (r : ℝ) : beltMass 1 r = Real.sin r := by
  simp only [beltMass,normalizer,sinPrimitive,cosPrimitive,pow_one,integral_sin,integral_cos,
    Real.cos_zero,Real.cos_pi_div_two,Real.sin_zero,sub_zero,inv_one,one_mul]

theorem model_dimension_three (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    model 1 p = Real.sqrt (p * (2 - p)) := by
  rw [model,beltMass_dimension_three]
  have hr := radius_mem 1 p
  have hs : 0 ≤ Real.sin (radius 1 p) :=
    Real.sin_nonneg_of_mem_Icc ⟨hr.1,by linarith [hr.2,Real.pi_pos]⟩
  have hm := mass_radius 1 p hp
  rw [capMass_dimension_three] at hm
  have he : p * (2-p) = Real.sin (radius 1 p)^2 := by
    have ht := Real.sin_sq_add_cos_sq (radius 1 p)
    rw [show Real.cos (radius 1 p) = 1-p by linarith] at ht
    nlinarith
  rw [he,Real.sqrt_sq hs]

theorem s2_double_cap_bound (nu : Measure (EuclideanSpace ℝ (Fin 3))) [nu.IsAddHaarMeasure]
    (A : Set (Sphere (EuclideanSpace ℝ (Fin 3)))) (hA : NullMeasurableSet A (probability nu))
    (hind : Avoids A A) : area nu A ≤ 1 - Real.sqrt 2 / 2 := by
  have h := double_cap_bound nu (by simp) A hA hind
  simpa only [Fintype.card_fin,Nat.reduceSub,delta_dimension_three] using h

end ShadowVerification.CapExtremizers
#print axioms ShadowVerification.CapExtremizers.closedCap_closed
#print axioms ShadowVerification.CapExtremizers.closedCap_antipodal
#print axioms ShadowVerification.CapExtremizers.shadow_closedCap_subset
#print axioms ShadowVerification.CapExtremizers.closedCap_ae_eq_open
#print axioms ShadowVerification.CapExtremizers.closedCap_mass
#print axioms ShadowVerification.CapExtremizers.closed_belt_mass
#print axioms ShadowVerification.CapExtremizers.closedCap_attains
#print axioms ShadowVerification.CapExtremizers.double_cap_conjecture
#print axioms ShadowVerification.CapExtremizers.alpha_eq_delta
#print axioms ShadowVerification.CapExtremizers.capMass_dimension_three
#print axioms ShadowVerification.CapExtremizers.delta_dimension_three
#print axioms ShadowVerification.CapExtremizers.beltMass_dimension_three
#print axioms ShadowVerification.CapExtremizers.model_dimension_three
#print axioms ShadowVerification.CapExtremizers.s2_double_cap_bound

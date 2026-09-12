import LeanShadow.CapFunctions
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! # The continuous inverse of normalized cap area -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Real
open scoped Topology
namespace ShadowVerification.CapRadius
open CapFunctions

theorem capMass_mem (m : ℕ) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) :
    capMass m r ∈ Icc (0 : ℝ) 1 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (Real.pi/2) := ⟨le_rfl, by positivity⟩
  have h1 : Real.pi/2 ∈ Icc (0 : ℝ) (Real.pi/2) := ⟨by positivity,le_rfl⟩
  constructor
  · simpa only [capMass_zero] using (capMass_strictMono m).monotoneOn h0 hr hr.1
  · simpa only [capMass_half_pi] using (capMass_strictMono m).monotoneOn hr h1 hr.2

theorem capMass_surj (m : ℕ) : SurjOn (capMass m) (Icc (0 : ℝ) (Real.pi/2)) (Icc (0 : ℝ) 1) := by
  have h := intermediate_value_Icc (show (0 : ℝ) ≤ Real.pi/2 by positivity) (capMass_continuous m).continuousOn
  intro p hp
  exact h (by simpa only [capMass_zero,capMass_half_pi] using hp)

def massMap (m : ℕ) (r : Icc (0 : ℝ) (Real.pi/2)) : Icc (0 : ℝ) 1 :=
  ⟨capMass m r,capMass_mem m r r.property⟩

theorem massMap_strictMono (m : ℕ) : StrictMono (massMap m) :=
  fun a b hab => capMass_strictMono m a.property b.property hab

theorem massMap_surjective (m : ℕ) : Function.Surjective (massMap m) := by
  intro p
  obtain ⟨r,hr,he⟩ := capMass_surj m p.property
  exact ⟨⟨r,hr⟩,Subtype.ext he⟩

def massIso (m : ℕ) : Icc (0 : ℝ) (Real.pi/2) ≃o Icc (0 : ℝ) 1 :=
  StrictMono.orderIsoOfRightInverse (massMap m) (massMap_strictMono m)
    (Function.surjInv (massMap_surjective m)) (Function.rightInverse_surjInv (massMap_surjective m))

def radius (m : ℕ) (p : ℝ) : ℝ :=
  (massIso m).symm (projIcc (0 : ℝ) 1 (by norm_num) p)

theorem radius_mem (m : ℕ) (p : ℝ) : radius m p ∈ Icc (0 : ℝ) (Real.pi/2) :=
  ((massIso m).symm (projIcc (0 : ℝ) 1 (by norm_num) p)).property

theorem mass_radius (m : ℕ) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) : capMass m (radius m p) = p := by
  have h := congrArg Subtype.val ((massIso m).apply_symm_apply (projIcc (0 : ℝ) 1 (by norm_num) p))
  change capMass m (radius m p) = (projIcc (0 : ℝ) 1 (by norm_num) p : ℝ) at h
  simpa only [projIcc_of_mem _ hp] using h

theorem radius_mass (m : ℕ) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (Real.pi/2)) : radius m (capMass m r) = r := by
  exact (capMass_strictMono m).injOn (radius_mem m _) hr (mass_radius m _ (capMass_mem m r hr))

theorem radius_continuous (m : ℕ) : Continuous (radius m) :=
  continuous_subtype_val.comp ((massIso m).symm.continuous.comp continuous_projIcc)

theorem radius_zero (m : ℕ) : radius m 0 = 0 := by
  have h := radius_mass m 0 ⟨le_rfl,by positivity⟩
  simpa only [capMass_zero] using h

theorem radius_one (m : ℕ) : radius m 1 = Real.pi/2 := by
  have h := radius_mass m (Real.pi/2) ⟨by positivity,le_rfl⟩
  simpa only [capMass_half_pi] using h

theorem radius_interior (m : ℕ) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    radius m p ∈ Ioo (0 : ℝ) (Real.pi/2) := by
  have hr := radius_mem m p
  have he := mass_radius m p ⟨hp.1.le,hp.2.le⟩
  constructor
  · apply lt_of_le_of_ne hr.1
    intro h
    rw [← h,capMass_zero] at he
    linarith [hp.1]
  · apply lt_of_le_of_ne hr.2
    intro h
    rw [h,capMass_half_pi] at he
    linarith [hp.2]

theorem radius_sin_pos (m : ℕ) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) : 0 < Real.sin (radius m p) :=
  Real.sin_pos_of_pos_of_lt_pi (radius_interior m p hp).1 (by linarith [(radius_interior m p hp).2,Real.pi_pos])

theorem radius_cos_pos (m : ℕ) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) : 0 < Real.cos (radius m p) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [(radius_interior m p hp).1,Real.pi_pos],(radius_interior m p hp).2⟩

theorem radius_hasDeriv (m : ℕ) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (radius m) (normalizer m * Real.sin (radius m p) ^ m)⁻¹ p := by
  apply HasDerivAt.of_local_left_inverse (radius_continuous m).continuousAt (capMass_hasDeriv m _)
    (mul_pos (normalizer_pos m) (pow_pos (radius_sin_pos m p hp) m)).ne'
  filter_upwards [isOpen_Ioo.mem_nhds hp] with q hq
  exact mass_radius m q ⟨hq.1.le,hq.2.le⟩

end ShadowVerification.CapRadius
#print axioms ShadowVerification.CapRadius.capMass_mem
#print axioms ShadowVerification.CapRadius.capMass_surj
#print axioms ShadowVerification.CapRadius.massMap_strictMono
#print axioms ShadowVerification.CapRadius.massMap_surjective
#print axioms ShadowVerification.CapRadius.radius_mem
#print axioms ShadowVerification.CapRadius.mass_radius
#print axioms ShadowVerification.CapRadius.radius_mass
#print axioms ShadowVerification.CapRadius.radius_continuous
#print axioms ShadowVerification.CapRadius.radius_zero
#print axioms ShadowVerification.CapRadius.radius_one
#print axioms ShadowVerification.CapRadius.radius_interior
#print axioms ShadowVerification.CapRadius.radius_sin_pos
#print axioms ShadowVerification.CapRadius.radius_cos_pos
#print axioms ShadowVerification.CapRadius.radius_hasDeriv

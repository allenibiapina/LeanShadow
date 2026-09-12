import LeanShadow.ProfileClosedness
import LeanShadow.AffineContact
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Slope

/-! # Ordinary concavity of the actual shadow profile

Maximize an affine functional on the compact region of feasible mass pairs,
restricted to a closed mass slab. A strict violation of a profile chord puts
the maximum at an interior mass. The actual elliptic theorem makes the
affine contact locally constant; analyticity propagates that identity down
the compression path. At the lower slab endpoint, feasibility contradicts
the strict excess. At mass zero use the compression limit itself.

This argument needs no prior continuity of the profile.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace ShadowVerification.ProfileConcavity
open Spherical Integrated FullFrame AmbientArea ActualContact Profile ProfileClosedness
open Compression OptimizerCompression AffineContact
open _root_.ShadowVerification.Dual

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]

omit [DecidableEq n] [Nonempty n] [BorelSpace (EuclideanSpace ℝ n)] [mu.IsAddHaarMeasure] in
theorem profile_zero : profile mu 0 = 0 := by
  have h := (Attainment.empty_optimizer mu).minimal
  simpa [shadow, area] using h.symm

theorem transformed_mem_region (A B : Set (UnitSphere n))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (ha : Antipodal.IsAntipodal A) (hb : Antipodal.IsAntipodal B) (hAB : Avoids A B)
    (T : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n) :
    (primal mu A (point T), dual mu B (point T)) ∈ region mu := by
  rw [primal_point mu A hA, dual_point mu B hB]
  exact ⟨action T '' A, action (dualEquiv T) '' B,
    measurable_action_image T A hA, measurable_action_image (dualEquiv T) B hB,
    Antipodal.antipodal_action_image T A ha, Antipodal.antipodal_action_image (dualEquiv T) B hb,
    avoids_dual_images T A B hAB, rfl, rfl⟩

set_option maxHeartbeats 800000 in
theorem chord_bound (hd : 2 < Module.finrank ℝ (EuclideanSpace ℝ n))
    (a b p q k : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hap : a < p) (hpb : p < b)
    (hqa : q = profile mu a) (hqb : q + k * (b - a) = profile mu b) :
    q + k * (p - a) ≤ profile mu p := by
  by_contra! hbad
  let S : Set (ℝ × ℝ) := region mu ∩ {z | z.1 ∈ Icc a b}
  let F : ℝ × ℝ → ℝ := fun z => z.2 + q + k * (z.1 - a)
  have hc : IsCompact S := (region_compact mu hd).inter_right
    (isClosed_Icc.preimage continuous_fst)
  have hstart : (p, 1 - profile mu p) ∈ S :=
    ⟨optimal_mem_region mu hd p ⟨by linarith, by linarith⟩, hap.le, hpb.le⟩
  obtain ⟨w,hw,hmax⟩ := hc.exists_isMaxOn ⟨_,hstart⟩
    (show ContinuousOn F S from (by unfold F; fun_prop : Continuous F).continuousOn)
  have hwgt : 1 < F w := by
    have h := hmax hstart
    change 1 - profile mu p + q + k * (p - a) ≤ F w at h
    linarith
  have hwbound := region_profile_bound mu hw.1
  have haw : a < w.1 := by
    have hle := hw.2.1
    apply lt_of_le_of_ne hle
    intro he
    have he' : w.1 = a := he.symm
    rw [he', ← hqa] at hwbound
    dsimp [F] at hwgt
    rw [he'] at hwgt
    nlinarith
  have hwb : w.1 < b := by
    apply lt_of_le_of_ne hw.2.2
    intro he
    rw [he, ← hqb] at hwbound
    dsimp [F] at hwgt
    rw [he] at hwgt
    linarith
  obtain ⟨A,B,hA,hB,haA,haB,hAB,hmA,hmB⟩ := hw.1
  have hbase : contact mu A B q a k 0 (base (n := n)) = F w := by
    rw [contact, ProfileContact.primal_base mu A hA, ProfileContact.dual_base mu B hB, hmA,hmB]
    simp [F,Contact.support,add_assoc]
  let T := ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ n)
  have hpoint : point T = base := ActualLocal.point_identity
  have hcont : ContinuousAt (primal mu A) (base (n := n)) := by
    simpa only [hpoint] using (primal_contDiffAt mu A T).continuousAt
  have hslab : ∀ᶠ x in 𝓝 (base (n := n)), primal mu A x ∈ Ioo a b :=
    hcont.eventually (isOpen_Ioo.mem_nhds (by rw [ProfileContact.primal_base mu A hA,hmA]; exact ⟨haw,hwb⟩))
  have hlocal : IsLocalMax (contact mu A B q a k 0) (base (n := n)) := by
    filter_upwards [hpoint ▸ MomentField.eventually_point T,hslab] with x hx hxs
    obtain ⟨U,rfl⟩ := hx
    rw [hbase]
    have h := hmax (show (primal mu A (point U), dual mu B (point U)) ∈ S from
      ⟨transformed_mem_region mu A B hA hB haA haB hAB U,hxs.1.le,hxs.2.le⟩)
    simpa [contact,Contact.support,F,add_assoc] using h
  obtain ⟨e,hlim⟩ := CompressionConcentration.exists_zero_compression mu A hA haA
    (by rw [hmA]; linarith)
  have hconstant (t : ℝ) (ht : 0 < t) :
      contact mu A B q a k 0 (path e t) = F w :=
    (affine_compression_constant mu A B hA hB q a k hlocal e t ht).trans hbase
  by_cases ha0 : a = 0
  · have hq0 : q = 0 := by rw [hqa,ha0,profile_zero]
    have hineq : ∀ᶠ t : ℝ in atTop, F w ≤ 1 + k * compressionArea mu A e t := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have h := area_le_one mu (action (dualEquiv (compressionEquiv e t ht)) '' B)
      change transformedArea mu B (dualEquiv (compressionEquiv e t ht)) ≤ 1 at h
      rw [← dual_point mu B hB, ← path_eq_point e t ht] at h
      have hh := hconstant t ht
      rw [contact,primal_path] at hh
      simp only [Contact.support,hq0,ha0,sub_zero,zero_div,zero_mul,sub_zero,zero_add] at hh
      linarith
    have ht : Tendsto (fun t => 1 + k * compressionArea mu A e t) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hlim)
    exact (not_le_of_gt hwgt) (ge_of_tendsto ht hineq)
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    obtain ⟨R,hR,hlow⟩ := (eventually_gt_atTop (1 : ℝ)).and
      (hlim.eventually (eventually_lt_nhds ha')) |>.exists
    have hca : ContinuousOn (compressionArea mu A e) (Icc 1 R) := by
      intro t ht
      exact ((analytic_compressionArea mu A e) t (show 0 < t by linarith [ht.1])).continuousAt.continuousWithinAt
    obtain ⟨t,ht,hat⟩ := intermediate_value_Icc' hR.le hca
      (show a ∈ Icc (compressionArea mu A e R) (compressionArea mu A e 1) by
        rw [compressionArea_one mu A hA e,hmA]; exact ⟨hlow.le,haw.le⟩)
    have ht0 : 0 < t := by linarith [ht.1]
    have hreg := transformed_mem_region mu A B hA hB haA haB hAB (compressionEquiv e t ht0)
    have h := region_profile_bound mu hreg
    rw [← path_eq_point e t ht0,primal_path,hat,← hqa] at h
    have hh := hconstant t ht0
    rw [contact,primal_path,hat] at hh
    simp only [Contact.support,sub_self,mul_zero,zero_pow (by norm_num : 2 ≠ 0),zero_div,
      sub_zero,add_zero] at hh
    exact (not_le_of_gt hwgt) (by linarith)

theorem concave (hd : 2 < Module.finrank ℝ (EuclideanSpace ℝ n)) :
    ConcaveOn ℝ (Icc 0 1) (profile mu) := by
  apply concaveOn_of_slope_anti_adjacent (convex_Icc (0 : ℝ) 1)
  intro a p b ha hb hap hpb
  have hab : a < b := hap.trans hpb
  have h := chord_bound mu hd a b p (profile mu a)
    ((profile mu b - profile mu a) / (b-a)) ha.1 hb.2 hap hpb rfl
    (by rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')]; ring)
  apply (div_le_div_iff₀ (sub_pos.mpr hpb) (sub_pos.mpr hap)).mpr
  have hdpos := sub_pos.mpr hab
  have hh := mul_le_mul_of_nonneg_right h hdpos.le
  field_simp at hh
  nlinarith

theorem locallyLipschitz (hd : 2 < Module.finrank ℝ (EuclideanSpace ℝ n)) :
    LocallyLipschitzOn (Ioo 0 1) (profile mu) := by
  simpa only [interior_Icc] using (concave mu hd).locallyLipschitzOn_interior

theorem continuous_interior (hd : 2 < Module.finrank ℝ (EuclideanSpace ℝ n)) :
    ContinuousOn (profile mu) (Ioo 0 1) := (locallyLipschitz mu hd).continuousOn

end ShadowVerification.ProfileConcavity
#print axioms ShadowVerification.ProfileConcavity.profile_zero
#print axioms ShadowVerification.ProfileConcavity.transformed_mem_region
#print axioms ShadowVerification.ProfileConcavity.chord_bound
#print axioms ShadowVerification.ProfileConcavity.concave
#print axioms ShadowVerification.ProfileConcavity.locallyLipschitz
#print axioms ShadowVerification.ProfileConcavity.continuous_interior

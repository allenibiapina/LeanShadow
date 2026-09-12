import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

/-! # Supporting lines in a smooth comparison coordinate

A nonincreasing ratio of right derivatives supplies a supporting line in
the g-coordinate. Continuity reaches both endpoints without differentiating
there or changing variables across exceptional sets.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology
namespace ShadowVerification.RatioSupport

theorem right_deriv_nonpos_endpoint (f d : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt f (d t) (Ioi t) t)
    (hsign : ∀ t ∈ Ico a b, d t ≤ 0) : f b ≤ f a := by
  have h := image_le_of_deriv_right_le_deriv_boundary hf
    (fun t ht => (hd t ht).Ici_of_Ioi) (B := fun _ => f a) (B' := fun _ => 0)
    le_rfl continuousOn_const (fun t _ => (hasDerivAt_const t (f a)).hasDerivWithinAt)
    hsign (right_mem_Icc.mpr hab)
  exact h

theorem support_interior (f g v w : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Ioo a b)) (hg : ContinuousOn g (Ioo a b))
    (hv : ∀ t ∈ Ioo a b, HasDerivWithinAt f (v t) (Ioi t) t)
    (hw : ∀ t ∈ Ioo a b, HasDerivAt g (w t) t)
    (hwp : ∀ t ∈ Ioo a b, 0 < w t)
    (hq : AntitoneOn (fun t => v t / w t) (Ioo a b))
    (p x : ℝ) (hp : p ∈ Ioo a b) (hx : x ∈ Ioo a b) :
    f x - (v p / w p) * g x ≤ f p - (v p / w p) * g p := by
  let q := v p / w p
  rcases le_total x p with hxp | hpx
  · have hsub : Icc x p ⊆ Ioo a b := fun t ht => ⟨hx.1.trans_le ht.1,ht.2.trans_lt hp.2⟩
    have h := right_deriv_nonpos_endpoint (fun t => q * g t - f t) (fun t => q * w t - v t)
      x p hxp ((continuousOn_const.mul (hg.mono hsub)).sub (hf.mono hsub))
      (fun t ht => ((hw t (hsub ⟨ht.1,ht.2.le⟩)).const_mul q).hasDerivWithinAt.sub
        (hv t (hsub ⟨ht.1,ht.2.le⟩)))
      (fun t ht => sub_nonpos.mpr ((le_div_iff₀ (hwp t (hsub ⟨ht.1,ht.2.le⟩))).mp
        (hq (hsub ⟨ht.1,ht.2.le⟩) hp ht.2.le)))
    dsimp only [q] at h
    linarith
  · have hsub : Icc p x ⊆ Ioo a b := fun t ht => ⟨hp.1.trans_le ht.1,ht.2.trans_lt hx.2⟩
    exact right_deriv_nonpos_endpoint (fun t => f t - q * g t) (fun t => v t - q * w t)
      p x hpx ((hf.mono hsub).sub (continuousOn_const.mul (hg.mono hsub)))
      (fun t ht => (hv t (hsub ⟨ht.1,ht.2.le⟩)).sub
        ((hw t (hsub ⟨ht.1,ht.2.le⟩)).const_mul q).hasDerivWithinAt)
      (fun t ht => sub_nonpos.mpr ((div_le_iff₀ (hwp t (hsub ⟨ht.1,ht.2.le⟩))).mp
        (hq hp (hsub ⟨ht.1,ht.2.le⟩) ht.1)))

theorem support_closed (f g v w : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hv : ∀ t ∈ Ioo a b, HasDerivWithinAt f (v t) (Ioi t) t)
    (hw : ∀ t ∈ Ioo a b, HasDerivAt g (w t) t)
    (hwp : ∀ t ∈ Ioo a b, 0 < w t)
    (hq : AntitoneOn (fun t => v t / w t) (Ioo a b))
    (p x : ℝ) (hp : p ∈ Ioo a b) (hx : x ∈ Icc a b) :
    f x - (v p / w p) * g x ≤ f p - (v p / w p) * g p := by
  have hc : ContinuousOn (fun t => f t - (v p / w p) * g t) (closure (Ioo a b)) := by
    rw [closure_Ioo (hp.1.trans hp.2).ne]
    exact hf.sub (continuousOn_const.mul hg)
  apply le_on_closure (fun t ht => support_interior f g v w a b
    (hf.mono Ioo_subset_Icc_self) (hg.mono Ioo_subset_Icc_self) hv hw hwp hq p t hp ht)
    hc continuousOn_const
  rwa [closure_Ioo (hp.1.trans hp.2).ne]

theorem endpoint_chord (f g v w : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (hg : ContinuousOn g (Icc (0 : ℝ) 1))
    (hv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt f (v t) (Ioi t) t)
    (hw : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g (w t) t)
    (hwp : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < w t)
    (hq : AntitoneOn (fun t => v t / w t) (Ioo (0 : ℝ) 1))
    (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hg0 : g 0 = 0) (hg1 : g 1 = 1)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) (hgp : g p ∈ Icc (0 : ℝ) 1) : g p ≤ f p := by
  have h0 := support_closed f g v w 0 1 hf hg hv hw hwp hq p 0 hp ⟨le_rfl,zero_le_one⟩
  have h1 := support_closed f g v w 0 1 hf hg hv hw hwp hq p 1 hp ⟨zero_le_one,le_rfl⟩
  rw [hf0,hg0,mul_zero,sub_zero] at h0
  rw [hf1,hg1,mul_one] at h1
  have h0' := mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hgp.2)
  have h1' := mul_le_mul_of_nonneg_left h1 hgp.1
  nlinarith

end ShadowVerification.RatioSupport
#print axioms ShadowVerification.RatioSupport.right_deriv_nonpos_endpoint
#print axioms ShadowVerification.RatioSupport.support_interior
#print axioms ShadowVerification.RatioSupport.support_closed
#print axioms ShadowVerification.RatioSupport.endpoint_chord

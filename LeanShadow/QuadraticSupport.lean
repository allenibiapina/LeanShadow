import LeanShadow.ContactCalculus
import Mathlib.Analysis.Asymptotics.Defs

/-! # A quadratic lower support from a second-order expansion at one point

The expansion is a Peano remainder statement at one mass. It neither
requires nor asserts twice continuous differentiability of the profile.
An arbitrarily small increase of the negative quadratic coefficient gives
the two-sided lower support used by the contact maximum argument.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology Asymptotics
namespace ShadowVerification.ProfileSupport

def HasQuadraticExpansion (f : ℝ → ℝ) (p k rho : ℝ) : Prop :=
  (fun s => f s - Contact.support (f p) p k rho s) =o[𝓝 p] (fun s => (s - p) ^ 2)

theorem support_at_center (q p k rho : ℝ) : Contact.support q p k rho p = q := by
  simp [Contact.support]

theorem slope_at_center (p k rho : ℝ) : Contact.slope p k rho p = k := by
  simp [Contact.slope]

/-- The little-o bound supplies a genuine lower support on a neighborhood. -/
theorem lower_support_of_expansion (f : ℝ → ℝ) (p k rho : ℝ)
    (h : HasQuadraticExpansion f p k rho) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ s in 𝓝 p, Contact.support (f p) p k (rho + eps) s ≤ f s := by
  have hh := h.def (show 0 < eps / 2 by positivity)
  filter_upwards [hh] with s hs
  have hn := neg_abs_le (f s - Contact.support (f p) p k rho s)
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (s - p))] at hs
  unfold Contact.support at hs hn ⊢
  nlinarith

/-- A positive support coefficient is available for any finite expansion coefficient. -/
theorem positive_lower_support (f : ℝ → ℝ) (p k rho : ℝ)
    (h : HasQuadraticExpansion f p k rho) :
    ∃ rho₀ > 0, rho < rho₀ ∧
      ∀ᶠ s in 𝓝 p, Contact.support (f p) p k rho₀ s ≤ f s := by
  refine ⟨rho + (|rho| + 1), by linarith [neg_abs_le rho], by linarith [abs_nonneg rho], ?_⟩
  exact lower_support_of_expansion f p k rho h (|rho| + 1) (by positivity)

end ShadowVerification.ProfileSupport
#print axioms ShadowVerification.ProfileSupport.support_at_center
#print axioms ShadowVerification.ProfileSupport.slope_at_center
#print axioms ShadowVerification.ProfileSupport.lower_support_of_expansion
#print axioms ShadowVerification.ProfileSupport.positive_lower_support

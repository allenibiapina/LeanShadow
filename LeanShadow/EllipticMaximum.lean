import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

/-! # Maximum principle development

Actual directional derivatives are used throughout. No maximum principle is
postulated as an axiom. This module develops the calculus and barrier proof
needed for the elliptic step in the nonisotropy argument.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology BigOperators

namespace ShadowVerification.Elliptic

/-- The necessary second-derivative condition, including Lean's convention
for an undefined derivative. -/
theorem second_deriv_nonpos_at_max {f : ℝ → ℝ} {x : ℝ}
    (hc : ContinuousAt f x) (hm : IsLocalMax f x) :
    deriv (deriv f) x ≤ 0 := by
  by_contra! h
  have hmin := isLocalMin_of_deriv_deriv_pos h hm.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hm, hmin] with y hy hy'
    exact le_antisymm hy hy'
  have hz := heq.deriv.deriv_eq
  simp only [deriv_const', deriv_const] at hz
  linarith

variable {E ι : Type*} [NormedAddCommGroup E] [Fintype ι]

section Normed
variable [NormedSpace ℝ E]

noncomputable def firstLine (u : E → ℝ) (x v : E) : ℝ :=
  deriv (fun t : ℝ => u (x + t • v)) 0

noncomputable def secondLine (u : E → ℝ) (x v : E) : ℝ :=
  deriv (deriv (fun t : ℝ => u (x + t • v))) 0

/-- A nondivergence operator in sum-of-squares form. The vector values are
held fixed while taking each straight-line derivative. -/
noncomputable def frameOp (V : ι → E → E) (b : E → E) (u : E → ℝ) (x : E) : ℝ :=
  (∑ i, secondLine u x (V i x)) + firstLine u x (b x)

theorem firstLine_zero_at_max {u : E → ℝ} {x : E} (hm : IsLocalMax u x) (v : E) :
    firstLine u x v = 0 := by
  have h : IsLocalMax (fun t : ℝ => u (x + t • v)) 0 := by
    have hm' : IsLocalMax u (x + (0 : ℝ) • v) := by simpa using hm
    simpa only [Function.comp_def, zero_smul, add_zero] using
      (hm'.comp_continuous (g := fun t : ℝ => x + t • v) (b := 0) (by fun_prop))
  exact h.deriv_eq_zero

theorem secondLine_nonpos_at_max {u : E → ℝ} {x : E}
    (hc : ContinuousAt u x) (hm : IsLocalMax u x) (v : E) :
    secondLine u x v ≤ 0 := by
  have h : IsLocalMax (fun t : ℝ => u (x + t • v)) 0 := by
    have hm' : IsLocalMax u (x + (0 : ℝ) • v) := by simpa using hm
    simpa only [Function.comp_def, zero_smul, add_zero] using
      (hm'.comp_continuous (g := fun t : ℝ => x + t • v) (b := 0) (by fun_prop))
  apply second_deriv_nonpos_at_max _ h
  have hc' : ContinuousAt u (x + (0 : ℝ) • v) := by simpa using hc
  exact hc'.comp (f := fun t : ℝ => x + t • v) (by fun_prop)

theorem frameOp_nonpos_at_max (V : ι → E → E) (b : E → E)
    {u : E → ℝ} {x : E} (hc : ContinuousAt u x) (hm : IsLocalMax u x) :
    frameOp V b u x ≤ 0 := by
  unfold frameOp
  rw [firstLine_zero_at_max hm, add_zero]
  exact Finset.sum_nonpos (fun i _ => secondLine_nonpos_at_max hc hm (V i x))

/-- The strict weak maximum principle on a compact region: if the operator is
strictly positive in its interior, a positive maximum cannot occur there. -/
theorem strict_weak_maximum (V : ι → E → E) (b : E → E)
    (u : E → ℝ) (K : Set E) (hK : IsCompact K) (hc : ContinuousOn u K)
    (hboundary : ∀ x ∈ K \ interior K, u x ≤ 0)
    (hP : ∀ x ∈ interior K, 0 < frameOp V b u x) :
    ∀ x ∈ K, u x ≤ 0 := by
  intro x hx
  by_contra! hpos
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hc
  have hzp : 0 < u z := lt_of_lt_of_le hpos (hmax hx)
  have hzi : z ∈ interior K := by
    by_contra hn
    exact (not_lt_of_ge (hboundary z ⟨hz, hn⟩)) hzp
  have hKn : K ∈ 𝓝 z := mem_interior_iff_mem_nhds.mp hzi
  have hzmax : IsLocalMax u z := hmax.isLocalMax hKn
  have hzc : ContinuousAt u z := (hc z hz).continuousAt hKn
  exact (not_lt_of_ge (frameOp_nonpos_at_max V b hzc hzmax)) (hP z hzi)

theorem exp_quadratic_hasDeriv (a b c t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (a + b * s + c * s ^ 2))
      ((b + 2 * c * t) * Real.exp (a + b * t + c * t ^ 2)) t := by
  have h := (((hasDerivAt_const t a).add ((hasDerivAt_id t).const_mul b)).add
    (((hasDerivAt_id t).pow 2).const_mul c)).exp
  convert h using 1
  · rfl
  · simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    ring

theorem exp_quadratic_second_deriv (a b c : ℝ) :
    deriv (deriv (fun s : ℝ => Real.exp (a + b * s + c * s ^ 2))) 0 =
      (b ^ 2 + 2 * c) * Real.exp a := by
  have hfirst : deriv (fun s : ℝ => Real.exp (a + b * s + c * s ^ 2)) =
      fun t => (b + 2 * c * t) * Real.exp (a + b * t + c * t ^ 2) :=
    funext (fun t => (exp_quadratic_hasDeriv a b c t).deriv)
  rw [hfirst]
  have h := ((hasDerivAt_const 0 b).add ((hasDerivAt_id 0).const_mul (2 * c))).mul
    (exp_quadratic_hasDeriv a b c 0)
  calc
    _ = (0 + 2 * c * 1) * Real.exp (a + b * 0 + c * 0 ^ 2) +
        (b + 2 * c * 0) * ((b + 2 * c * 0) * Real.exp (a + b * 0 + c * 0 ^ 2)) := h.deriv
    _ = _ := by simp; ring

theorem second_deriv_add {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun t => f t + g t)) x = deriv (deriv f) x + deriv (deriv g) x := by
  have heq : deriv (fun t => f t + g t) =ᶠ[𝓝 x] fun t => deriv f t + deriv g t := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hy hy'
    exact deriv_add (hy.differentiableAt (by norm_num)) (hy'.differentiableAt (by norm_num))
  rw [heq.deriv_eq]
  exact deriv_add ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))

theorem frameOp_add (V : ι → E → E) (b : E → E) (u w : E → ℝ) (x : E)
    (hu : ∀ v : E, ContDiffAt ℝ 2 (fun t : ℝ => u (x + t • v)) 0)
    (hw : ∀ v : E, ContDiffAt ℝ 2 (fun t : ℝ => w (x + t • v)) 0) :
    frameOp V b (fun y => u y + w y) x = frameOp V b u x + frameOp V b w x := by
  unfold frameOp secondLine firstLine
  simp_rw [second_deriv_add (hu _) (hw _)]
  have hd : deriv (fun t : ℝ => u (x + t • b x) + w (x + t • b x)) 0 =
      deriv (fun t : ℝ => u (x + t • b x)) 0 + deriv (fun t : ℝ => w (x + t • b x)) 0 :=
    deriv_add ((hu (b x)).differentiableAt (by norm_num))
      ((hw (b x)).differentiableAt (by norm_num))
  rw [hd, Finset.sum_add_distrib]
  ring

theorem frameOp_const_mul (V : ι → E → E) (b : E → E) (u : E → ℝ) (x : E) (c : ℝ) :
    frameOp V b (fun y => c * u y) x = c * frameOp V b u x := by
  simp only [frameOp, secondLine, firstLine, deriv_const_mul_field', deriv_const_mul_field,
    Finset.mul_sum, mul_add]

theorem frameOp_sub_const (V : ι → E → E) (b : E → E) (u : E → ℝ) (x : E) (c : ℝ) :
    frameOp V b (fun y => u y - c) x = frameOp V b u x := by
  simp only [frameOp, secondLine, firstLine, sub_eq_add_neg, deriv_add_const', deriv_add_const]

end Normed

section Inner
variable [InnerProductSpace ℝ E]

noncomputable def gaussian (a : ℝ) (y x : E) : ℝ := Real.exp (-a * ‖x - y‖ ^ 2)

theorem gaussian_on_line (a : ℝ) (y x v : E) :
    (fun t : ℝ => gaussian a y (x + t • v)) =
      fun t => Real.exp ((-a * ‖x - y‖ ^ 2) +
        (-2 * a * inner ℝ (x - y) v) * t + (-a * ‖v‖ ^ 2) * t ^ 2) := by
  funext t
  unfold gaussian
  congr 1
  rw [show x + t • v - y = (x - y) + t • v by abel,
    norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs]
  rw [mul_pow, sq_abs]
  ring

theorem gaussian_line_smooth (a : ℝ) (y x v : E) :
    ContDiffAt ℝ 2 (fun t : ℝ => gaussian a y (x + t • v)) 0 := by
  rw [gaussian_on_line]
  fun_prop

theorem gaussian_firstLine (a : ℝ) (y x v : E) :
    firstLine (gaussian a y) x v =
      (-2 * a * inner ℝ (x - y) v) * gaussian a y x := by
  unfold firstLine
  rw [gaussian_on_line]
  simpa only [mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero, gaussian] using
    (exp_quadratic_hasDeriv (-a * ‖x - y‖ ^ 2)
      (-2 * a * inner ℝ (x - y) v) (-a * ‖v‖ ^ 2) 0).deriv

theorem gaussian_secondLine (a : ℝ) (y x v : E) :
    secondLine (gaussian a y) x v =
      (4 * a ^ 2 * (inner ℝ (x - y) v) ^ 2 - 2 * a * ‖v‖ ^ 2) * gaussian a y x := by
  unfold secondLine
  rw [gaussian_on_line, exp_quadratic_second_deriv]
  unfold gaussian
  ring

theorem gaussian_frameOp (V : ι → E → E) (b : E → E) (a : ℝ) (y x : E) :
    frameOp V b (gaussian a y) x = gaussian a y x *
      (4 * a ^ 2 * (∑ i, (inner ℝ (x - y) (V i x)) ^ 2) -
        2 * a * (∑ i, ‖V i x‖ ^ 2) - 2 * a * inner ℝ (x - y) (b x)) := by
  simp only [frameOp, gaussian_secondLine, gaussian_firstLine,
    ← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem gaussian_frameOp_pos (V : ι → E → E) (b : E → E)
    (a lam K r : ℝ) (y x : E) (ha : 0 < a) (hlam : 0 ≤ lam) (hr : 0 ≤ r)
    (hd : r ≤ ‖x - y‖)
    (hell : lam * ‖x - y‖ ^ 2 ≤ ∑ i, (inner ℝ (x - y) (V i x)) ^ 2)
    (hbound : (∑ i, ‖V i x‖ ^ 2) + inner ℝ (x - y) (b x) ≤ K)
    (hchoice : K < 2 * a * lam * r ^ 2) :
    0 < frameOp V b (gaussian a y) x := by
  rw [gaussian_frameOp]
  apply mul_pos (Real.exp_pos _)
  have hs : lam * r ^ 2 ≤ ∑ i, (inner ℝ (x - y) (V i x)) ^ 2 := by
    have hsq : r ^ 2 ≤ ‖x - y‖ ^ 2 := sq_le_sq₀ hr (norm_nonneg _) |>.mpr hd
    exact (mul_le_mul_of_nonneg_left hsq hlam).trans hell
  have hmul := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * a)
  have hpos : 0 < 2 * a *
      (2 * a * (∑ i, (inner ℝ (x - y) (V i x)) ^ 2) -
        ((∑ i, ‖V i x‖ ^ 2) + inner ℝ (x - y) (b x))) := by
    apply mul_pos (by positivity)
    nlinarith
  nlinarith

/-- The Hopf barrier contradiction at a tangent ball. The hypotheses are
actual inequalities for the differential operator, not a postulated maximum
principle. Gaussian positivity is supplied by `gaussian_frameOp_pos`. -/
theorem no_tangent_ball_contact [ProperSpace E]
    (V : ι → E → E) (b : E → E) (u : E → ℝ) (M a r : ℝ) (y z : E)
    (hr : 0 < r) (ha : 0 < a) (hz : ‖z - y‖ = r)
    (hc : Continuous u) (huz : u z = M) (hm : IsLocalMax u z)
    (hupper : ∀ x, ‖x - y‖ ≤ r → u x ≤ M)
    (hstrict : ∀ x, ‖x - y‖ < r → u x < M)
    (hsmooth : ∀ x, r / 2 ≤ ‖x - y‖ → ‖x - y‖ ≤ r →
      ∀ v : E, ContDiffAt ℝ 2 (fun t : ℝ => u (x + t • v)) 0)
    (hsub : ∀ x, r / 2 ≤ ‖x - y‖ → ‖x - y‖ ≤ r → 0 ≤ frameOp V b u x)
    (hgauss : ∀ x, r / 2 ≤ ‖x - y‖ → ‖x - y‖ ≤ r →
      0 < frameOp V b (gaussian a y) x) : False := by
  classical
  let K : Set E := {x | r / 2 ≤ ‖x - y‖ ∧ ‖x - y‖ ≤ r}
  have hK : IsCompact K := by
    apply (isCompact_closedBall y r).of_isClosed_subset
    · change IsClosed {x : E | r / 2 ≤ ‖x - y‖ ∧ ‖x - y‖ ≤ r}
      exact (isClosed_le continuous_const (show Continuous (fun x : E => ‖x - y‖) by fun_prop)).inter
        (isClosed_le (show Continuous (fun x : E => ‖x - y‖) by fun_prop) continuous_const)
    · intro x hx
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hx.2
  obtain ⟨m, hmBall, hmMax⟩ := (isCompact_closedBall y (r / 2)).exists_isMaxOn
    (show (Metric.closedBall y (r / 2)).Nonempty from ⟨y, by simp; positivity⟩)
    hc.continuousOn
  have hmd : ‖m - y‖ ≤ r / 2 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hmBall
  have hmM : u m < M := hstrict m (by linarith)
  let ε := M - u m
  have hε : 0 < ε := sub_pos.mpr hmM
  let γ := Real.exp (-a * r ^ 2)
  let vfun : E → ℝ := fun x => (u x - M) + ε * (gaussian a y x - γ)
  have hvc : Continuous vfun := by
    dsimp [vfun, gaussian]
    fun_prop
  have hvbound : ∀ x ∈ K, vfun x ≤ 0 := by
    apply strict_weak_maximum V b vfun K hK hvc.continuousOn
    · intro x hx
      have hdx : r / 2 ≤ ‖x - y‖ ∧ ‖x - y‖ ≤ r := hx.1
      by_cases htop : ‖x - y‖ = r
      · have huM := hupper x hdx.2
        simpa [vfun, gaussian, γ, htop] using sub_nonpos.mpr huM
      · have hbot : ‖x - y‖ = r / 2 := by
          by_contra hn
          have hi : x ∈ {w : E | r / 2 < ‖w - y‖ ∧ ‖w - y‖ < r} := by
            exact ⟨lt_of_le_of_ne hdx.1 (Ne.symm hn), lt_of_le_of_ne hdx.2 htop⟩
          have hop : IsOpen {w : E | r / 2 < ‖w - y‖ ∧ ‖w - y‖ < r} :=
            (isOpen_lt continuous_const (show Continuous (fun w : E => ‖w - y‖) by fun_prop)).inter
              (isOpen_lt (show Continuous (fun w : E => ‖w - y‖) by fun_prop) continuous_const)
          have hKi : K ∈ 𝓝 x := Filter.mem_of_superset (hop.mem_nhds hi)
            (fun w hw => ⟨hw.1.le, hw.2.le⟩)
          exact hx.2 (mem_interior_iff_mem_nhds.mpr hKi)
        have hum : u x ≤ u m := hmMax (by simp [Metric.mem_closedBall, dist_eq_norm, hbot])
        have hg1 : gaussian a y x ≤ 1 := Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) (sq_nonneg _))
        have hw1 : gaussian a y x - γ ≤ 1 := by
          have hγ : 0 < γ := Real.exp_pos _
          linarith
        have hprod := mul_le_mul_of_nonneg_left hw1 hε.le
        dsimp [vfun, ε] at *
        nlinarith
    · intro x hxi
      have hx : x ∈ K := interior_subset hxi
      have hlin : frameOp V b vfun x =
          frameOp V b u x + ε * frameOp V b (gaussian a y) x := by
        dsimp [vfun]
        rw [frameOp_add V b (fun w => u w - M) (fun w => ε * (gaussian a y w - γ)) x
          (fun w => (hsmooth x hx.1 hx.2 w).sub contDiffAt_const)
          (fun w => contDiffAt_const.mul ((gaussian_line_smooth a y x w).sub contDiffAt_const))]
        rw [frameOp_sub_const, frameOp_const_mul, frameOp_sub_const]
      rw [hlin]
      exact add_pos_of_nonneg_of_pos (hsub x hx.1 hx.2) (mul_pos hε (hgauss x hx.1 hx.2))
  let q : E := -(z - y)
  have hzlow : r / 2 ≤ ‖z - y‖ := by rw [hz]; linarith
  have hv0 : vfun z = 0 := by simp [vfun, huz, gaussian, hz, γ]
  have hdv : firstLine vfun z q = ε * (2 * a * r ^ 2 * γ) := by
    unfold firstLine vfun
    have hd : deriv (fun t : ℝ => (u (z + t • q) - M) +
        ε * (gaussian a y (z + t • q) - γ)) 0 =
        deriv (fun t : ℝ => u (z + t • q) - M) 0 +
        deriv (fun t : ℝ => ε * (gaussian a y (z + t • q) - γ)) 0 :=
      deriv_add ((hsmooth z hzlow hz.le q).sub contDiffAt_const |>.differentiableAt (by norm_num))
        ((contDiffAt_const.mul ((gaussian_line_smooth a y z q).sub contDiffAt_const)).differentiableAt (by norm_num))
    rw [hd, deriv_sub_const, deriv_const_mul_field, deriv_sub_const]
    change firstLine u z q + ε * firstLine (gaussian a y) z q = _
    rw [firstLine_zero_at_max hm, gaussian_firstLine]
    simp only [q, inner_neg_right, real_inner_self_eq_norm_sq, hz, gaussian, γ]
    ring
  have hdpos : 0 < deriv (fun t : ℝ => vfun (z + t • q)) 0 := by
    change 0 < firstLine vfun z q
    rw [hdv]
    exact mul_pos hε (mul_pos (mul_pos (mul_pos (by norm_num) ha) (sq_pos_of_pos hr)) (Real.exp_pos _))
  have hv00 : (fun t : ℝ => vfun (z + t • q)) 0 = 0 := by simpa using hv0
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos hdpos hv00
  have hex : ∀ᶠ t : ℝ in 𝓝[>] 0,
      0 < t ∧ t < 1 / 2 ∧ 0 < vfun (z + t • q) := by
    filter_upwards [nhdsWithin_le_nhds hsign, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with t ht ht0 ht1
    refine ⟨ht0, ht1, ?_⟩
    have ht0' : 0 < t := ht0
    simp only [sub_zero, sign_pos ht0'] at ht
    exact sign_eq_one_iff.mp ht
  obtain ⟨t, ht0, ht1, htp⟩ := hex.exists
  have hnorm : ‖z + t • q - y‖ = (1 - t) * r := by
    rw [show z + t • q - y = (1 - t) • (z - y) by dsimp [q]; module,
      norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hz]
  have htK : z + t • q ∈ K := by
    change r / 2 ≤ ‖z + t • q - y‖ ∧ ‖z + t • q - y‖ ≤ r
    rw [hnorm]
    constructor <;> nlinarith
  exact (not_lt_of_ge (hvbound _ htK)) htp

/-- A local strong maximum principle with explicit uniform ellipticity and
coefficient bounds. A subsolution which attains its maximum at the center is
constant on a smaller ball. No regularity of the coefficients beyond these
bounds is used; the function has continuous second derivatives along lines. -/
theorem local_strong_maximum [ProperSpace E]
    (V : ι → E → E) (b : E → E) (u : E → ℝ) (x₀ : E)
    (R lam C B : ℝ) (_hR : 0 < R) (hlam : 0 < lam)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hc : Continuous u)
    (hmax : ∀ x, ‖x - x₀‖ < R → u x ≤ u x₀)
    (hsmooth : ∀ x, ‖x - x₀‖ < R → ∀ v : E,
      ContDiffAt ℝ 2 (fun t : ℝ => u (x + t • v)) 0)
    (hsub : ∀ x, ‖x - x₀‖ < R → 0 ≤ frameOp V b u x)
    (hell : ∀ x, ‖x - x₀‖ < R → ∀ v : E,
      lam * ‖v‖ ^ 2 ≤ ∑ i, (inner ℝ v (V i x)) ^ 2)
    (htrace : ∀ x, ‖x - x₀‖ < R → (∑ i, ‖V i x‖ ^ 2) ≤ C)
    (hdrift : ∀ x, ‖x - x₀‖ < R → ‖b x‖ ≤ B) :
    ∀ y, ‖y - x₀‖ < R / 4 → u y = u x₀ := by
  intro y hy
  by_contra hne
  let S : Set E := {x | u x = u x₀}
  have hS : IsClosed S := isClosed_eq hc continuous_const
  obtain ⟨z, hzS, hzdist⟩ := hS.exists_infDist_eq_dist ⟨x₀, rfl⟩ y
  let r := ‖z - y‖
  have hr : 0 < r := by
    apply norm_pos_iff.mpr
    intro heq
    have hzy : z = y := sub_eq_zero.mp heq
    exact hne (hzy ▸ hzS)
  have hrad : r ≤ ‖y - x₀‖ := by
    have hh := Metric.infDist_le_dist_of_mem (x := y) (show x₀ ∈ S from rfl)
    rw [hzdist] at hh
    simpa only [dist_eq_norm, norm_sub_rev, r] using hh
  have hinside : ∀ x, ‖x - y‖ ≤ r → ‖x - x₀‖ < R := by
    intro x hx
    have htri := norm_add_le (x - y) (y - x₀)
    rw [sub_add_sub_cancel] at htri
    linarith
  have hzR : ‖z - x₀‖ < R := hinside z le_rfl
  have hupper : ∀ x, ‖x - y‖ ≤ r → u x ≤ u x₀ :=
    fun x hx => hmax x (hinside x hx)
  have hstrict : ∀ x, ‖x - y‖ < r → u x < u x₀ := by
    intro x hx
    apply lt_of_le_of_ne (hupper x hx.le)
    intro heq
    have hh := Metric.infDist_le_dist_of_mem (x := y) (show x ∈ S from heq)
    rw [hzdist, dist_eq_norm, dist_eq_norm, norm_sub_rev y z, norm_sub_rev y x] at hh
    exact (not_le_of_gt hx) hh
  have hlocal : IsLocalMax u z := by
    have hopen : IsOpen {x : E | ‖x - x₀‖ < R} :=
      isOpen_lt (show Continuous (fun x : E => ‖x - x₀‖) by fun_prop) continuous_const
    filter_upwards [hopen.mem_nhds hzR] with x hx
    change u x ≤ u z
    rw [show u z = u x₀ from hzS]
    exact hmax x hx
  let K := C + B * r
  have hK : 0 ≤ K := add_nonneg hC (mul_nonneg hB hr.le)
  let a := (K + 1) / (2 * lam * (r / 2) ^ 2)
  have hden : 0 < 2 * lam * (r / 2) ^ 2 := by positivity
  have ha : 0 < a := div_pos (by linarith) hden
  have hchoice : K < 2 * a * lam * (r / 2) ^ 2 := by
    have heq : 2 * a * lam * (r / 2) ^ 2 = K + 1 := by
      dsimp [a]
      field_simp
    rw [heq]
    linarith
  apply no_tangent_ball_contact V b u (u x₀) a r y z hr ha rfl hc hzS hlocal
    hupper hstrict
  · intro x _ hx v
    exact hsmooth x (hinside x hx) v
  · intro x _ hx
    exact hsub x (hinside x hx)
  · intro x hxlow hx
    apply gaussian_frameOp_pos V b a lam K (r / 2) y x ha hlam.le
      (by positivity) hxlow (hell x (hinside x hx) (x - y)) _ hchoice
    have hi : inner ℝ (x - y) (b x) ≤ r * B := by
      apply (real_inner_le_norm _ _).trans
      exact mul_le_mul hx (hdrift x (hinside x hx)) (norm_nonneg _) hr.le
    have ht := htrace x (hinside x hx)
    dsimp [K]
    nlinarith


end Inner

end ShadowVerification.Elliptic

#print axioms ShadowVerification.Elliptic.second_deriv_nonpos_at_max
#print axioms ShadowVerification.Elliptic.firstLine_zero_at_max
#print axioms ShadowVerification.Elliptic.secondLine_nonpos_at_max
#print axioms ShadowVerification.Elliptic.frameOp_nonpos_at_max
#print axioms ShadowVerification.Elliptic.strict_weak_maximum
#print axioms ShadowVerification.Elliptic.exp_quadratic_hasDeriv
#print axioms ShadowVerification.Elliptic.exp_quadratic_second_deriv
#print axioms ShadowVerification.Elliptic.second_deriv_add
#print axioms ShadowVerification.Elliptic.frameOp_add
#print axioms ShadowVerification.Elliptic.frameOp_const_mul
#print axioms ShadowVerification.Elliptic.frameOp_sub_const
#print axioms ShadowVerification.Elliptic.gaussian_on_line
#print axioms ShadowVerification.Elliptic.gaussian_line_smooth
#print axioms ShadowVerification.Elliptic.gaussian_firstLine
#print axioms ShadowVerification.Elliptic.gaussian_secondLine
#print axioms ShadowVerification.Elliptic.gaussian_frameOp
#print axioms ShadowVerification.Elliptic.gaussian_frameOp_pos
#print axioms ShadowVerification.Elliptic.no_tangent_ball_contact

#print axioms ShadowVerification.Elliptic.local_strong_maximum

import LeanShadow.WeightedFrame

/-! # Local uniform ellipticity from a spanning frame

Continuity and spanning at one point suffice to obtain a uniform positive
principal-symbol bound nearby. Compactness of the unit sphere supplies a
single constant for all covectors. This proves the local estimate used by the
weighted maximum principle, rather than assuming uniform ellipticity.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set Filter
open scoped BigOperators Topology
namespace ShadowVerification.WeightedEllipticity

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def symbol (A : E → Matrix ι ι ℝ) (V : ι → E → E) (x v : E) : ℝ :=
  (fun i => inner ℝ v (V i x)) ⬝ᵥ (A x *ᵥ (fun i => inner ℝ v (V i x)))

/-- Homogeneity is what turns a bound on unit covectors into ellipticity. -/
theorem symbol_smul (A : E → Matrix ι ι ℝ) (V : ι → E → E) (x v : E) (t : ℝ) :
    symbol A V x (t • v) = t ^ 2 * symbol A V x v := by
  simp only [symbol, dotProduct, Matrix.mulVec, real_inner_smul_left, Finset.mul_sum]
  simp_rw [show ∀ i j, (t * inner ℝ v (V i x)) * (A x i j * (t * inner ℝ v (V j x))) =
    t ^ 2 * (inner ℝ v (V i x) * (A x i j * inner ℝ v (V j x))) by intro i j; ring]

/-- Continuous coefficients and fields give a jointly continuous symbol. -/
theorem symbol_continuousAt (A : E → Matrix ι ι ℝ) (V : ι → E → E) (x v : E)
    (hA : ∀ i j, ContinuousAt (fun y => A y i j) x)
    (hV : ∀ i, ContinuousAt (V i) x) :
    ContinuousAt (fun z : E × E => symbol A V z.1 z.2) (x, v) := by
  unfold symbol dotProduct Matrix.mulVec
  fun_prop

/-- A positive coefficient matrix and a frame separating covectors give a
strictly positive principal symbol. -/
theorem symbol_pos_of_spanning (A : E → Matrix ι ι ℝ) (V : ι → E → E) (x : E)
    (hA : (A x).PosDef)
    (hspan : ∀ v : E, (∀ i, inner ℝ v (V i x) = 0) → v = 0)
    (v : E) (hv : v ≠ 0) : 0 < symbol A V x v := by
  have hc : (fun i => inner ℝ v (V i x)) ≠ 0 := by
    intro heq
    exact hv (hspan v (fun i => congrFun heq i))
  simpa only [symbol, star_trivial] using hA.dotProduct_mulVec_pos hc

/-- Scaling a unit-sphere bound gives the full quadratic lower bound. -/
theorem symbol_lower_of_unit (A : E → Matrix ι ι ℝ) (V : ι → E → E) (x : E)
    (lam : ℝ) (hunit : ∀ v : E, ‖v‖ = 1 → lam ≤ symbol A V x v) (v : E) :
    lam * ‖v‖ ^ 2 ≤ symbol A V x v := by
  by_cases hv : v = 0
  · simp [hv, symbol, dotProduct, Matrix.mulVec]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let w : E := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by simp [w, norm_smul, hn]
  have hvw : ‖v‖ • w = v := by simp [w, smul_smul, hn]
  calc
    lam * ‖v‖ ^ 2 ≤ symbol A V x w * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hunit w hw) (sq_nonneg _)
    _ = symbol A V x v := by rw [mul_comm, ← symbol_smul, hvw]

/-- The compactness step produces one positive ellipticity constant on an
actual neighborhood, not a separate bound for each covector. -/
theorem eventually_uniform_ellipticity [ProperSpace E] [Nontrivial E]
    (A : E → Matrix ι ι ℝ) (V : ι → E → E) (x₀ : E)
    (hA : ∀ i j, ContinuousAt (fun y => A y i j) x₀)
    (hV : ∀ i, ContinuousAt (V i) x₀)
    (hpos : ∀ v : E, v ≠ 0 → 0 < symbol A V x₀ v) :
    ∃ lam > 0, ∀ᶠ x in 𝓝 x₀, ∀ v : E, lam * ‖v‖ ^ 2 ≤ symbol A V x v := by
  let S : Set E := Metric.sphere 0 1
  have hS : IsCompact S := isCompact_sphere 0 1
  have hSne : S.Nonempty := NormedSpace.sphere_nonempty.mpr (by norm_num)
  have hc : Continuous (fun v => symbol A V x₀ v) := by
    unfold symbol dotProduct Matrix.mulVec
    fun_prop
  obtain ⟨w, hw, hmin⟩ := hS.exists_isMinOn hSne hc.continuousOn
  have hwn : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
  have hwp : 0 < symbol A V x₀ w := hpos w (by intro hz; simp [hz] at hwn)
  let lam := symbol A V x₀ w / 2
  have hlam : 0 < lam := by dsimp [lam]; positivity
  refine ⟨lam, hlam, ?_⟩
  have hnear : ∀ᶠ x in 𝓝 x₀, ∀ v ∈ S, lam < symbol A V x v := by
    apply hS.eventually_forall_of_forall_eventually
    intro v hv
    have hlt : lam < symbol A V x₀ v := by
      have hm : symbol A V x₀ w ≤ symbol A V x₀ v := hmin hv
      dsimp [lam]
      linarith
    exact (symbol_continuousAt A V x₀ v hA hV).eventually (eventually_gt_nhds hlt)
  filter_upwards [hnear] with x hx
  intro v
  exact symbol_lower_of_unit A V x lam
    (fun w hw => (hx w (mem_sphere_zero_iff_norm.mpr hw)).le) v

/-- A continuous spanning frame and positive weight at the base point supply
all nearby principal-symbol estimates required by the maximum principle. -/
theorem eventually_uniform_of_spanning [ProperSpace E] [Nontrivial E]
    (A : E → Matrix ι ι ℝ) (V : ι → E → E) (x₀ : E)
    (hA : ∀ i j, ContinuousAt (fun y => A y i j) x₀)
    (hV : ∀ i, ContinuousAt (V i) x₀) (hpos : (A x₀).PosDef)
    (hspan : ∀ v : E, (∀ i, inner ℝ v (V i x₀) = 0) → v = 0) :
    ∃ lam > 0, ∀ᶠ x in 𝓝 x₀, ∀ v : E, lam * ‖v‖ ^ 2 ≤ symbol A V x v :=
  eventually_uniform_ellipticity A V x₀ hA hV
    (fun v hv => symbol_pos_of_spanning A V x₀ hpos hspan v hv)

end ShadowVerification.WeightedEllipticity
#print axioms ShadowVerification.WeightedEllipticity.symbol_smul
#print axioms ShadowVerification.WeightedEllipticity.symbol_continuousAt
#print axioms ShadowVerification.WeightedEllipticity.symbol_pos_of_spanning
#print axioms ShadowVerification.WeightedEllipticity.symbol_lower_of_unit
#print axioms ShadowVerification.WeightedEllipticity.eventually_uniform_ellipticity
#print axioms ShadowVerification.WeightedEllipticity.eventually_uniform_of_spanning

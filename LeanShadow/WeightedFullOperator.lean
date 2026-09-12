import LeanShadow.FullProjectiveFrame
import LeanShadow.WeightedAreaSource
import LeanShadow.WeightedFlow

/-! # Completing the principal part in all matrix coordinates

The geometric symmetric weight is augmented by identity coefficients in the
skew and scalar directions. The resulting full matrix is positive definite.
The constructed fields and compactness then give local uniform ellipticity
for every continuous matrix weight satisfying the stated smallness condition.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Filter
open scoped BigOperators Topology Matrix.Norms.Frobenius
namespace ShadowVerification.FullWeight
open FullFrame Weighted WeightedEllipticity
open _root_.ShadowVerification.Frame

section Blocks
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

noncomputable def completeWeight (W : Matrix ι ι ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks W 0 0 1

/-- Identity coefficients are added only in the supplementary directions. -/
theorem completeWeight_quadratic (W : Matrix ι ι ℝ) (v : (ι ⊕ κ) → ℝ) :
    v ⬝ᵥ (completeWeight W *ᵥ v) =
      (fun i => v (.inl i)) ⬝ᵥ (W *ᵥ (fun i => v (.inl i))) +
        ∑ j, v (.inr j) ^ 2 := by
  simp [completeWeight, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
    Matrix.one_apply, pow_two]

omit [Fintype ι] [Fintype κ] in
theorem completeWeight_symm (W : Matrix ι ι ℝ) (hW : W.IsSymm) :
    (completeWeight (κ := κ) W).IsSymm := by
  ext i j
  cases i <;> cases j <;> simp [completeWeight, Matrix.transpose_apply, hW.apply, Matrix.one_apply, eq_comm]

/-- A coefficient lower bound on the symmetric block survives completion. -/
theorem completeWeight_lower (W : Matrix ι ι ℝ)
    (hW : ∀ v : ι → ℝ, (1 / 2 : ℝ) * (∑ i, v i ^ 2) ≤ v ⬝ᵥ (W *ᵥ v))
    (v : (ι ⊕ κ) → ℝ) :
    (1 / 2 : ℝ) * (∑ i, v i ^ 2) ≤ v ⬝ᵥ (completeWeight W *ᵥ v) := by
  rw [completeWeight_quadratic, Fintype.sum_sum_type]
  have hh := hW (fun i => v (.inl i))
  have hn : 0 ≤ ∑ j : κ, v (.inr j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith

/-- Positivity is proved for the full coefficient matrix, including its
supplementary directions. -/
theorem completeWeight_posDef (W : Matrix ι ι ℝ) (hsym : W.IsSymm)
    (hW : ∀ v : ι → ℝ, (1 / 2 : ℝ) * (∑ i, v i ^ 2) ≤ v ⬝ᵥ (W *ᵥ v)) :
    (completeWeight (κ := κ) W).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨by simpa using completeWeight_symm (κ := κ) W hsym, ?_⟩
  intro v hv
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hp : 0 < ∑ j, v j ^ 2 := Finset.sum_pos'
    (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  have hh := completeWeight_lower W hW v
  simpa only [star_trivial] using
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hp).trans_le hh
end Blocks

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def geometricWeight (G : Ambient n → Matrix n n ℝ) (L : ℝ)
    (x : Ambient n) : Matrix (FullIndex n) (FullIndex n) ℝ :=
  completeWeight (weightCoefficients (frame (frobeniusBasis (n := n))) (1 - L • G x))

/-- Coercivity of the actual trace weight supplies full positive definiteness. -/
theorem geometricWeight_posDef (G : Ambient n → Matrix n n ℝ) (L : ℝ) (x : Ambient n)
    (hL : 0 ≤ L) (hsmall : L * ‖G x‖ ≤ 1 / 2) : (geometricWeight G L x).PosDef := by
  apply completeWeight_posDef
  · exact weightCoefficients_symm _ _
  · intro v
    have hh := weightCoefficients_lower_bound (frame (frobeniusBasis (n := n)))
      (fun i => (frobeniusBasis i).property.1) (G x) L hL hsmall v
    rwa [WeightedSource.frame_sum_norm_sq] at hh

omit [DecidableEq n] in
/-- Matrix entries are continuous also for the Frobenius norm used here. -/
theorem matrix_entry_continuous (i j : n) :
    Continuous (fun M : Matrix n n ℝ => M i j) := by
  let e : Matrix n n ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun M => M i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact e.continuous_of_finiteDimensional

/-- No derivatives of the weight are needed: its entries are continuous when G is. -/
theorem geometricWeight_continuousAt (G : Ambient n → Matrix n n ℝ) (L : ℝ)
    (x : Ambient n) (hG : ContinuousAt G x) (i j : FullIndex n) :
    ContinuousAt (fun y => geometricWeight G L y i j) x := by
  have hentry (r s : n) : ContinuousAt (fun y => G y r s) x :=
    (matrix_entry_continuous r s).continuousAt.comp hG
  cases i <;> cases j
  · unfold geometricWeight completeWeight weightCoefficients
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  · simpa only [geometricWeight, completeWeight, Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply] using (continuousAt_const : ContinuousAt (fun _ : Ambient n => (0 : ℝ)) x)
  · simpa only [geometricWeight, completeWeight, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply] using (continuousAt_const : ContinuousAt (fun _ : Ambient n => (0 : ℝ)) x)
  · exact continuousAt_const

/-- The full geometric principal part is uniformly elliptic near the identity.
Spanning, continuity of the fields, and the matrix coercivity are all supplied
by proved constructions. Only continuity and smallness of the prescribed G
are inputs here; identifying G with transformed moments is a separate step. -/
theorem geometric_uniform_ellipticity [Nonempty n]
    (G : Ambient n → Matrix n n ℝ) (L : ℝ)
    (hG : ContinuousAt G (base (n := n))) (hL : 0 ≤ L)
    (hsmall : L * ‖G base‖ ≤ 1 / 2) :
    ∃ lam > 0, ∀ᶠ x in 𝓝 (base (n := n)), ∀ v : Ambient n,
      lam * ‖v‖ ^ 2 ≤ symbol (geometricWeight G L)
        (fun i y => leftField (generator i) y) x v := by
  apply eventually_uniform_of_spanning
  · exact geometricWeight_continuousAt G L base hG
  · intro i
    exact (continuous_field i).continuousAt
  · exact geometricWeight_posDef G L base hL hsmall
  · exact fields_separate_at_base

end ShadowVerification.FullWeight
#print axioms ShadowVerification.FullWeight.completeWeight_quadratic
#print axioms ShadowVerification.FullWeight.completeWeight_symm
#print axioms ShadowVerification.FullWeight.completeWeight_lower
#print axioms ShadowVerification.FullWeight.completeWeight_posDef
#print axioms ShadowVerification.FullWeight.geometricWeight_posDef
#print axioms ShadowVerification.FullWeight.geometricWeight_continuousAt
#print axioms ShadowVerification.FullWeight.geometric_uniform_ellipticity

#print axioms ShadowVerification.FullWeight.matrix_entry_continuous

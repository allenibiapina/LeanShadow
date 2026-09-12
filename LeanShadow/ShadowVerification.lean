import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

/-!
# Partial verification of the shadow manuscript

This file DOES NOT prove the shadow theorem or the double-cap conjecture.
It verifies selected algebraic implications used by the manuscript.
Every hypothesis is explicit. No geometric, analytic, or measure-theoretic
claim is introduced as an axiom or as an unfinished proof.
-/

set_option autoImplicit false
open scoped BigOperators Matrix

namespace ShadowVerification

section Scalar

/-- Final entrywise algebra only; the decomposition and its squares are not proved here. -/
theorem contraction_coefficient (N t : ℝ) (hN : N ≠ 0) (hN1 : N - 1 ≠ 0) :
    N * (N - 1) * ((1 + N * (N - 2) * t) / (N * (N - 1))) -
        N * ((1 + (N - 2) * t) / 2) =
      (N - 2) / 2 * (N * t - 1) := by
  field_simp
  ring

theorem weighted_trace_algebra (N Λ k r s t : ℝ) :
    -(N - 2) * k * (-Λ * s) - r * (s - Λ * t) =
      ((N - 2) * Λ * k - r) * s + r * Λ * t := by
  ring

theorem weighted_coercivity (r c Λ s t : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hc : 2 * r ≤ c) (ht : |Λ * t| ≤ s / 2) :
    r / 2 * s ≤ (c - r) * s + r * Λ * t := by
  have ht' : -(s / 2) ≤ Λ * t := (abs_le.mp ht).1
  have hcs : 0 ≤ (c - 2 * r) * s := mul_nonneg (sub_nonneg.mpr hc) hs
  have hts : 0 ≤ r * (Λ * t + s / 2) :=
    mul_nonneg hr (by linarith)
  nlinarith

theorem negative_eigenvalue_bound (ρ C d : ℝ)
    (hd : 0 < d) (h : 0 ≤ ρ * d ^ 2 - C * d) :
    C / d ≤ ρ := by
  apply (div_le_iff₀ hd).2
  nlinarith

theorem moment_bound_transfer (ρ C d D : ℝ)
    (hC : 0 ≤ C) (hd : 0 < d) (hdD : d ≤ D)
    (hρ : C / d ≤ ρ) :
    C / D ≤ ρ := by
  exact (div_le_div_of_nonneg_left hC hd hdD).trans hρ

theorem equality_forces_moment (C ρ d D : ℝ)
    (hC : 0 < C) (hd : 0 < d) (hD : 0 < D)
    (hρ : ρ = C / D) (hbound : C / d ≤ ρ) (hupper : d ≤ D) :
    d = D := by
  apply le_antisymm hupper
  have h : C / d ≤ C / D := hρ ▸ hbound
  exact (div_le_div_iff_of_pos_left hC hd hD).mp h

theorem concave_endpoint_chord (φ : ℝ → ℝ)
    (hφ : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) φ)
    (h0 : φ 0 = 0) (h1 : φ 1 = 1)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    s ≤ φ s := by
  have h := hφ.2 (by simp : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (by simp : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (sub_nonneg.mpr hs.2) hs.1 (by ring : (1 - s) + s = 1)
  simpa [smul_eq_mul, h0, h1] using h

end Scalar

section Matrices

variable {ι n : Type*} [Fintype ι] [Fintype n]

noncomputable def gramContraction
    (H : ι → Matrix n n ℝ) (Q : Matrix ι ι ℝ) : Matrix n n ℝ :=
  ∑ k : n, (Matrix.of (fun i a => H i k a))ᴴ * Q *
    Matrix.of (fun i a => H i k a)

theorem gramContraction_posSemidef
    (H : ι → Matrix n n ℝ) (Q : Matrix ι ι ℝ)
    (hQ : Q.PosSemidef) :
    (gramContraction H Q).PosSemidef := by
  classical
  unfold gramContraction
  exact Matrix.posSemidef_sum Finset.univ
    (fun k _ => hQ.conjTranspose_mul_mul_same (fun i a => H i k a))

noncomputable def productContraction
    (H : ι → Matrix n n ℝ) (Q : Matrix ι ι ℝ) : Matrix n n ℝ :=
  ∑ i : ι, ∑ j : ι, Q i j • (H i * H j)

theorem gramContraction_eq_product
    (H : ι → Matrix n n ℝ) (Q : Matrix ι ι ℝ)
    (hH : ∀ i, (H i).IsSymm) :
    gramContraction H Q = productContraction H Q := by
  classical
  ext a b
  simp only [gramContraction, productContraction, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ k : n, ∑ j : ι, ∑ i : ι, H i k a * Q i j * H j k b) =
        ∑ j : ι, ∑ k : n, ∑ i : ι, H i k a * Q i j * H j k b := by
      exact Finset.sum_comm
    _ = ∑ j : ι, ∑ i : ι, ∑ k : n, H i k a * Q i j * H j k b := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ i : ι, ∑ j : ι, ∑ k : n, H i k a * Q i j * H j k b := by
      exact Finset.sum_comm
    _ = ∑ i : ι, ∑ j : ι, ∑ k : n, Q i j * (H i a k * H j k b) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [(hH i).apply a k]
      ring

noncomputable def manuscriptContraction
    (H : ι → Matrix n n ℝ) (Q : Matrix ι ι ℝ) : Matrix n n ℝ :=
  ∑ i : ι, ∑ j : ι, (Q i j / 2) • (H i * H j + H j * H i)

theorem manuscriptContraction_eq_product
    (H : ι → Matrix n n ℝ) (Q : Matrix ι ι ℝ)
    (hQ : Q.IsSymm) :
    manuscriptContraction H Q = productContraction H Q := by
  classical
  have hswap :
      (∑ i : ι, ∑ j : ι, Q i j • (H j * H i)) =
        ∑ i : ι, ∑ j : ι, Q i j • (H i * H j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hQ.apply i j]
  have hsplit :
      manuscriptContraction H Q =
        (1 / 2 : ℝ) •
          ((∑ i : ι, ∑ j : ι, Q i j • (H i * H j)) +
           (∑ i : ι, ∑ j : ι, Q i j • (H j * H i))) := by
    simp only [manuscriptContraction, smul_add, Finset.sum_add_distrib,
      Finset.smul_sum, smul_smul]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
      apply Finset.sum_congr rfl <;> intro j _ <;> congr 1 <;> ring
  rw [hsplit, hswap]
  ext a b
  simp only [productContraction, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

theorem manuscriptContraction_posSemidef
    (H : ι → Matrix n n ℝ) (Q : Matrix ι ι ℝ)
    (hH : ∀ i, (H i).IsSymm) (hQ : Q.PosSemidef) :
    (manuscriptContraction H Q).PosSemidef := by
  have hQs : Q.IsSymm := by
    ext i j
    simpa using hQ.isHermitian.apply i j
  rw [manuscriptContraction_eq_product H Q hQs,
    ← gramContraction_eq_product H Q hH]
  exact gramContraction_posSemidef H Q hQ

/-- Linearity in the operator being contracted. -/
theorem manuscriptContraction_sub
    (H : ι → Matrix n n ℝ) (Q R : Matrix ι ι ℝ) :
    manuscriptContraction H (Q - R) =
      manuscriptContraction H Q - manuscriptContraction H R := by
  classical
  simp only [manuscriptContraction, Matrix.sub_apply, sub_div, sub_smul,
    Finset.sum_sub_distrib]

theorem manuscriptContraction_smul
    (H : ι → Matrix n n ℝ) (Q : Matrix ι ι ℝ) (r : ℝ) :
    manuscriptContraction H (r • Q) = r • manuscriptContraction H Q := by
  classical
  simp only [manuscriptContraction, Matrix.smul_apply, smul_eq_mul,
    Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

/-- The positivity theorem also preserves the semidefinite ordering. -/
theorem manuscriptContraction_mono
    (H : ι → Matrix n n ℝ) (Q R : Matrix ι ι ℝ)
    (hH : ∀ i, (H i).IsSymm) (hQR : (R - Q).PosSemidef) :
    (manuscriptContraction H R - manuscriptContraction H Q).PosSemidef := by
  rw [← manuscriptContraction_sub]
  exact manuscriptContraction_posSemidef H (R - Q) hH hQR

/-- The coefficient matrix of the rank-one form v tensor v. -/
def rankOne (v : ι → ℝ) : Matrix ι ι ℝ := fun i j => v i * v j

omit [Fintype ι] in
theorem rankOne_isSymm (v : ι → ℝ) : (rankOne v).IsSymm := by
  ext i j
  exact mul_comm _ _

/-- This is the manuscript identity Ψ(v tensor v) = (sum v_i H_i)^2. -/
theorem manuscriptContraction_rankOne
    (H : ι → Matrix n n ℝ) (v : ι → ℝ) :
    manuscriptContraction H (rankOne v) =
      (∑ i : ι, v i • H i) * (∑ i : ι, v i • H i) := by
  classical
  rw [manuscriptContraction_eq_product H (rankOne v) (rankOne_isSymm v)]
  simp only [productContraction, rankOne, Finset.sum_mul, Finset.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

/-- The contracted second-variation implication. Its variational and moment
identities are hypotheses; their geometric proofs are outside this file. -/
theorem contracted_variation_bound
    (H : ι → Matrix n n ℝ) (Q : Matrix ι ι ℝ)
    (v : ι → ℝ) (G : Matrix n n ℝ) (ρ C : ℝ)
    (hH : ∀ i, (H i).IsSymm)
    (hG : (∑ i : ι, v i • H i) = G)
    (hvariation : (ρ • rankOne v - Q).PosSemidef)
    (hidentity : manuscriptContraction H Q = (-C) • G) :
    (ρ • (G * G) + C • G).PosSemidef := by
  have h := manuscriptContraction_posSemidef H (ρ • rankOne v - Q) hH hvariation
  rw [manuscriptContraction_sub, manuscriptContraction_smul,
    manuscriptContraction_rankOne, hG, hidentity] at h
  simpa only [neg_smul, sub_neg_eq_add] using h

/-- Testing the semidefinite matrix on a unit negative eigenvector. -/
theorem matrix_negative_eigenvalue_bound
    (G : Matrix n n ℝ) (z : n → ℝ) (ρ C d : ℝ)
    (hd : 0 < d) (hz : z ⬝ᵥ z = 1)
    (heigen : G *ᵥ z = (-d) • z)
    (hM : (ρ • (G * G) + C • G).PosSemidef) :
    C / d ≤ ρ := by
  have hmul : (ρ • (G * G) + C • G) *ᵥ z = (ρ * d ^ 2 - C * d) • z := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      ← Matrix.mulVec_mulVec, heigen, Matrix.mulVec_smul, heigen]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h := hM.dotProduct_mulVec_nonneg z
  rw [hmul] at h
  have hscalar : 0 ≤ ρ * d ^ 2 - C * d := by
    simpa [star_trivial, dotProduct_smul, hz, smul_eq_mul] using h
  exact negative_eigenvalue_bound ρ C d hd hscalar

/-- A single checked algebraic chain, from variational data and a moment
upper bound to the scalar inequality used in the manuscript. -/
theorem variation_to_scalar_bound
    (H : ι → Matrix n n ℝ) (Q : Matrix ι ι ℝ)
    (v : ι → ℝ) (G : Matrix n n ℝ) (z : n → ℝ) (ρ C d D : ℝ)
    (hH : ∀ i, (H i).IsSymm)
    (hG : (∑ i : ι, v i • H i) = G)
    (hvariation : (ρ • rankOne v - Q).PosSemidef)
    (hidentity : manuscriptContraction H Q = (-C) • G)
    (hC : 0 ≤ C) (hd : 0 < d) (hdD : d ≤ D)
    (hz : z ⬝ᵥ z = 1) (heigen : G *ᵥ z = (-d) • z) :
    C / D ≤ ρ := by
  have hM := contracted_variation_bound H Q v G ρ C hH hG hvariation hidentity
  have hb := matrix_negative_eigenvalue_bound G z ρ C d hd hz heigen hM
  exact moment_bound_transfer ρ C d D hC hd hdD hb

end Matrices
end ShadowVerification

#print axioms ShadowVerification.contraction_coefficient
#print axioms ShadowVerification.weighted_trace_algebra
#print axioms ShadowVerification.weighted_coercivity
#print axioms ShadowVerification.negative_eigenvalue_bound
#print axioms ShadowVerification.moment_bound_transfer
#print axioms ShadowVerification.equality_forces_moment
#print axioms ShadowVerification.concave_endpoint_chord
#print axioms ShadowVerification.gramContraction_posSemidef
#print axioms ShadowVerification.gramContraction_eq_product
#print axioms ShadowVerification.manuscriptContraction_eq_product
#print axioms ShadowVerification.manuscriptContraction_posSemidef
#print axioms ShadowVerification.manuscriptContraction_sub
#print axioms ShadowVerification.manuscriptContraction_smul
#print axioms ShadowVerification.manuscriptContraction_mono
#print axioms ShadowVerification.rankOne_isSymm
#print axioms ShadowVerification.manuscriptContraction_rankOne
#print axioms ShadowVerification.contracted_variation_bound
#print axioms ShadowVerification.matrix_negative_eigenvalue_bound
#print axioms ShadowVerification.variation_to_scalar_bound

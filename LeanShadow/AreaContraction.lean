import LeanShadow.IntegratedContraction

/-! # Contraction of actual polarized area variations

The matrix in this file is defined from derivatives of the measure of actual
projectively transformed Borel sets. Polarization identifies that matrix with
the integrated pointwise kernel. Consequently its contraction and trace are
proved identities about actual area derivatives.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open Matrix MeasureTheory Set Module
namespace ShadowVerification.AreaContraction
open Spherical Projective Coordinates Integrated
open _root_.ShadowVerification.Frame

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def quadraticDensity (H : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  (Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2) * (x ⬝ᵥ (H *ᵥ x)) ^ 2 -
    2 * (Fintype.card n : ℝ) * ((H *ᵥ x) ⬝ᵥ (H *ᵥ x))

omit [DecidableEq n] in
theorem quadraticDensity_symmetric (H : Matrix n n ℝ) (hH : H.IsSymm) (x : n → ℝ) :
    quadraticDensity H x =
      (Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2) * (x ⬝ᵥ (H *ᵥ x)) ^ 2 -
        2 * (Fintype.card n : ℝ) * (x ⬝ᵥ (H *ᵥ (H *ᵥ x))) := by
  have h : x ⬝ᵥ (H *ᵥ (H *ᵥ x)) = (H *ᵥ x) ⬝ᵥ (H *ᵥ x) := by
    simpa only [hH.eq] using dotProduct_transpose_mulVec H x (H *ᵥ x)
  simp only [quadraticDensity, h]

omit [DecidableEq n] in
theorem density_polarization {ι : Type*} (H : ι → Matrix n n ℝ) (x : n → ℝ) (i j : ι) :
    pointwiseKernel H x i j =
      (quadraticDensity (H i + H j) x - quadraticDensity (H i) x - quadraticDensity (H j) x) / 2 := by
  rw [pointwiseKernel_apply]
  simp only [quadraticDensity, Matrix.add_mulVec, dotProduct_add, add_dotProduct]
  rw [dotProduct_comm (H j *ᵥ x) (H i *ᵥ x)]
  ring

omit [DecidableEq n] in
theorem continuous_quadraticDensity (H : Matrix n n ℝ) :
    Continuous (fun x : UnitSphere n => quadraticDensity H ⇑(x : EuclideanSpace ℝ n)) := by
  unfold quadraticDensity dotProduct Matrix.mulVec
  fun_prop

variable [Nonempty n] [MeasurableSpace (EuclideanSpace ℝ n)] [BorelSpace (EuclideanSpace ℝ n)]
  (mu : Measure (EuclideanSpace ℝ n)) [mu.IsAddHaarMeasure]
  (A : Set (UnitSphere n))

noncomputable def firstArea (H : Matrix n n ℝ) : ℝ :=
  deriv (fun t => transformedArea mu A (flowEquiv (operator H) t)) 0

noncomputable def secondArea (H : Matrix n n ℝ) : ℝ :=
  deriv (deriv (fun t => transformedArea mu A (flowEquiv (operator H) t))) 0

theorem secondArea_integral (hA : MeasurableSet A) (H : Matrix n n ℝ)
    (hH : H.IsSymm) (ht : H.trace = 0) :
    secondArea mu A H = ∫ x in A, quadraticDensity H ⇑(x : EuclideanSpace ℝ n) ∂probability mu := by
  simp_rw [quadraticDensity_symmetric H hH]
  exact area_second_matrix mu H hH ht A hA

/-- Reversing the projective direction reverses the actual first variation. -/
theorem firstArea_neg (hA : MeasurableSet A) (H : Matrix n n ℝ)
    (hH : H.IsSymm) (ht : H.trace = 0) : firstArea mu A (-H) = -firstArea mu A H := by
  unfold firstArea
  rw [(area_first_matrix mu (-H) hH.neg (by simp [Matrix.trace_neg, ht]) A hA).deriv,
    (area_first_matrix mu H hH ht A hA).deriv, ← integral_neg]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp [Matrix.neg_mulVec, dotProduct_neg]

/-- Reversing the direction preserves the actual second variation. -/
theorem secondArea_neg (hA : MeasurableSet A) (H : Matrix n n ℝ)
    (hH : H.IsSymm) (ht : H.trace = 0) : secondArea mu A (-H) = secondArea mu A H := by
  rw [secondArea_integral mu A hA (-H) hH.neg (by simp [Matrix.trace_neg, ht]),
    secondArea_integral mu A hA H hH ht]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp [quadraticDensity, Matrix.neg_mulVec, dotProduct_neg, neg_dotProduct]

variable {ι : Type*} [Fintype ι]

noncomputable def polarizedAreaMatrix (H : ι → Matrix n n ℝ) : Matrix ι ι ℝ :=
  fun i j => (secondArea mu A (H i + H j) - secondArea mu A (H i) - secondArea mu A (H j)) / 2

/-- Every entry of the integrated kernel is an actual polarized area derivative. -/
theorem polarizedAreaMatrix_eq_integrated (hA : MeasurableSet A) (H : ι → Matrix n n ℝ)
    (hH : ∀ i, (H i).IsSymm) (ht : ∀ i, (H i).trace = 0) :
    polarizedAreaMatrix mu A H = integratedKernel ((probability mu).restrict A) H := by
  ext i j
  have hint : ∀ M : Matrix n n ℝ,
      Integrable (fun x : UnitSphere n => quadraticDensity M ⇑(x : EuclideanSpace ℝ n))
        ((probability mu).restrict A) :=
    fun M => sphere_integrable_continuous _ _ (continuous_quadraticDensity M)
  rw [integratedKernel_entry]
  change (secondArea mu A (H i + H j) - secondArea mu A (H i) - secondArea mu A (H j)) / 2 = _
  rw [secondArea_integral mu A hA _ ((hH i).add (hH j)) (by simp [Matrix.trace_add, ht]),
    secondArea_integral mu A hA _ (hH i) (ht i), secondArea_integral mu A hA _ (hH j) (ht j)]
  simp_rw [density_polarization]
  have hd : Integrable (fun x : UnitSphere n =>
      quadraticDensity (H i + H j) ⇑(x : EuclideanSpace ℝ n) -
      quadraticDensity (H i) ⇑(x : EuclideanSpace ℝ n)) ((probability mu).restrict A) := by
    exact sphere_integrable_continuous _ _
      ((continuous_quadraticDensity (H i + H j)).sub (continuous_quadraticDensity (H i)))
  rw [integral_div, integral_sub hd (hint (H j)),
    integral_sub (hint (H i + H j)) (hint (H i))]

theorem firstArea_eq_coefficients (hA : MeasurableSet A) (H : ι → Matrix n n ℝ)
    (hH : ∀ i, (H i).IsSymm) (ht : ∀ i, (H i).trace = 0) :
    (fun i => firstArea mu A (H i)) = firstCoefficients ((probability mu).restrict A) H := by
  funext i
  rw [firstCoefficients_entry]
  exact (area_first_matrix mu (H i) (hH i) (ht i) A hA).deriv

/-- The contracted matrix is defined entirely from actual area derivatives. -/
theorem area_contraction (hA : MeasurableSet A)
    (b : Basis ι ℝ (symZero (n := n))) (hb : IsOrthonormal b) :
    manuscriptContraction (frame b) (polarizedAreaMatrix mu A (frame b)) =
      (-((Fintype.card n : ℝ) - 2) / 2) • gradientMatrix ((probability mu).restrict A) := by
  rw [polarizedAreaMatrix_eq_integrated mu A hA (frame b)
    (fun i => (b i).property.1) (fun i => (b i).property.2)]
  exact integrated_contraction _ b hb

theorem area_trace_zero (hA : MeasurableSet A)
    (b : Basis ι ℝ (symZero (n := n))) (hb : IsOrthonormal b) :
    (polarizedAreaMatrix mu A (frame b)).trace = 0 := by
  rw [polarizedAreaMatrix_eq_integrated mu A hA (frame b)
    (fun i => (b i).property.1) (fun i => (b i).property.2)]
  exact integrated_trace_zero _ b hb

theorem firstArea_reconstruction (hA : MeasurableSet A)
    (b : Basis ι ℝ (symZero (n := n))) (hb : IsOrthonormal b) :
    (∑ i, firstArea mu A (frame b i) • frame b i) = gradientMatrix ((probability mu).restrict A) := by
  have h := firstArea_eq_coefficients mu A hA (frame b)
    (fun i => (b i).property.1) (fun i => (b i).property.2)
  change MatrixIntegral.synthesis (frame b) (fun i => firstArea mu A (frame b i)) = _
  rw [h]
  exact integrated_first_reconstruction _ b hb

end ShadowVerification.AreaContraction
#print axioms ShadowVerification.AreaContraction.quadraticDensity_symmetric
#print axioms ShadowVerification.AreaContraction.density_polarization
#print axioms ShadowVerification.AreaContraction.continuous_quadraticDensity
#print axioms ShadowVerification.AreaContraction.secondArea_integral
#print axioms ShadowVerification.AreaContraction.firstArea_neg
#print axioms ShadowVerification.AreaContraction.secondArea_neg
#print axioms ShadowVerification.AreaContraction.polarizedAreaMatrix_eq_integrated
#print axioms ShadowVerification.AreaContraction.firstArea_eq_coefficients
#print axioms ShadowVerification.AreaContraction.area_contraction
#print axioms ShadowVerification.AreaContraction.area_trace_zero
#print axioms ShadowVerification.AreaContraction.firstArea_reconstruction

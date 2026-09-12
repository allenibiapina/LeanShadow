import LeanShadow.SphericalNullSets
import LeanShadow.ThresholdTrimming
import LeanShadow.AntipodalGeometry

/-! # Exact measurable trimming that preserves antipodality

A measurable embedding into the real line gives a real code for each point.
Taking the minimum of the codes of a point and its antipode makes the code
antipodally invariant. Its fibers are finite, hence null. Threshold cuts of
this code give exact masses by dominated convergence and the IVT.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ENNReal
namespace ShadowVerification.AntipodalTrimming
open Spherical Antipodal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

noncomputable def orbitCode (x : Sphere E) : ℝ :=
  min (embeddingReal (Sphere E) x) (embeddingReal (Sphere E) (antipode x))

omit [Nontrivial E] in
theorem orbitCode_measurable : Measurable (orbitCode (E := E)) := by
  exact (measurable_embeddingReal _).min
    ((measurable_embeddingReal _).comp antipodeHomeomorph.continuous.measurable)

omit [Nontrivial E] in
theorem orbitCode_antipode (x : Sphere E) : orbitCode (antipode x) = orbitCode x := by
  simp only [orbitCode, antipode_twice, min_comm]

omit [Nontrivial E] in
theorem orbitCode_fiber_finite (t : ℝ) : {x : Sphere E | orbitCode x = t}.Finite := by
  let e := embeddingReal (Sphere E)
  have he : Function.Injective e := (measurableEmbedding_embeddingReal _).injective
  have h1 : {x | e x = t}.Subsingleton := by
    intro x hx y hy
    exact he (hx.trans hy.symm)
  have h2 : {x : Sphere E | e (antipode x) = t}.Subsingleton := by
    intro x hx y hy
    have h := congrArg antipode (he (hx.trans hy.symm))
    simpa only [antipode_twice] using h
  apply (h1.finite.union h2.finite).subset
  intro x hx
  change min (e x) (e (antipode x)) = t at hx
  rcases le_total (e x) (e (antipode x)) with h | h
  · exact Or.inl (by simpa only [mem_ofPred_eq, min_eq_left h] using hx)
  · exact Or.inr (by simpa only [mem_ofPred_eq, min_eq_right h] using hx)

variable (mu : Measure E) [mu.IsAddHaarMeasure]

/-- Exact trimming of an antipodal Borel set, by taking a subset. -/
theorem exists_subset_area (hd : 1 < Module.finrank ℝ E)
    (D : Set (Sphere E)) (hD : MeasurableSet D) (hanti : IsAntipodal D)
    (p : ℝ) (hp : 0 ≤ p) (hpD : p ≤ area mu D) :
    ∃ A ⊆ D, MeasurableSet A ∧ IsAntipodal A ∧ area mu A = p := by
  by_cases hp0 : p = 0
  · exact ⟨∅, empty_subset D, MeasurableSet.empty, by intro x hx; exact hx.elim,
      by simp [area, hp0]⟩
  by_cases hpEq : p = area mu D
  · exact ⟨D, Subset.rfl, hD, hanti, hpEq.symm⟩
  let : NullSingletonClass (probability mu) := SphericalNull.nullSingletonClass mu hd
  let nu := (probability mu).restrict D
  have hnull (t : ℝ) : nu {x | orbitCode (E := E) x = t} = 0 :=
    (orbitCode_fiber_finite t).measure_zero nu
  have htotal : nu.real univ = area mu D := by simp [nu, area, measureReal_def]
  obtain ⟨t, ht⟩ := Trimming.exists_cutMass_eq nu orbitCode orbitCode_measurable hnull p
    (lt_of_le_of_ne hp (Ne.symm hp0)) (htotal ▸ lt_of_le_of_ne hpD hpEq)
  let C : Set (Sphere E) := {x | orbitCode x ≤ t}
  have hC : MeasurableSet C := measurableSet_le orbitCode_measurable measurable_const
  refine ⟨D ∩ C, inter_subset_left, hD.inter hC, ?_, ?_⟩
  · intro x hx
    exact ⟨hanti x hx.1, by simpa only [C, mem_ofPred_eq, orbitCode_antipode] using hx.2⟩
  · change ((probability mu) (D ∩ C)).toReal = p
    change ((probability mu).restrict D C).toReal = p at ht
    rw [Measure.restrict_apply hC, inter_comm C D] at ht
    exact ht

/-- There are Borel antipodal competitors at every normalized mass. -/
theorem exists_set_area (hd : 1 < Module.finrank ℝ E)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ A : Set (Sphere E), MeasurableSet A ∧ IsAntipodal A ∧ area mu A = p := by
  have ht : area mu (univ : Set (Sphere E)) = 1 := by simp [area]
  obtain ⟨A, _, hA, hanti, hm⟩ := exists_subset_area mu hd univ MeasurableSet.univ
    (fun _ _ => mem_univ _) p hp (ht ▸ hp1)
  exact ⟨A, hA, hanti, hm⟩

end ShadowVerification.AntipodalTrimming
#print axioms ShadowVerification.AntipodalTrimming.orbitCode_measurable
#print axioms ShadowVerification.AntipodalTrimming.orbitCode_antipode
#print axioms ShadowVerification.AntipodalTrimming.orbitCode_fiber_finite
#print axioms ShadowVerification.AntipodalTrimming.exists_subset_area
#print axioms ShadowVerification.AntipodalTrimming.exists_set_area

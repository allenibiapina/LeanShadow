import LeanShadow.EquatorialMeasure
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Diagonal invariant pair measures are determined by their Gram law -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.InvariantPair
open Spherical OrthogonalHaar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

def diagonal (R : OrthogonalHaar.Group E) (z : Sphere E × Sphere E) :=
  (rotate R z.1, rotate R z.2)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem diagonal_continuous : Continuous (fun z : OrthogonalHaar.Group E ×
    (Sphere E × Sphere E) => diagonal z.1 z.2) := by
  exact (rotate_continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
    (rotate_continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

def gram (z : Sphere E × Sphere E) : ℝ := inner ℝ (z.1 : E) (z.2 : E)

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem gram_continuous : Continuous (gram (E := E)) := by unfold gram; fun_prop

abbrev GramRange (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  Set.range (gram (E := E))

instance : CompactSpace (GramRange E) :=
  isCompact_iff_compactSpace.mp (isCompact_range (gram_continuous (E := E)))

def quotient : C(Sphere E × Sphere E, GramRange E) :=
  ⟨fun z => ⟨gram z, ⟨z, rfl⟩⟩, gram_continuous.subtype_mk _⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem quotientMap : Topology.IsQuotientMap (quotient (E := E)) :=
  Topology.IsQuotientMap.of_surjective_continuous
    (fun ⟨t, ht⟩ => by obtain ⟨z, rfl⟩ := ht; exact ⟨z, rfl⟩) quotient.continuous

def translated (f : C(Sphere E × Sphere E, ℝ)) :
    C(OrthogonalHaar.Group E, C(Sphere E × Sphere E, ℝ)) :=
  (f.comp ⟨_, diagonal_continuous⟩).curry

def average (f : C(Sphere E × Sphere E, ℝ)) : C(Sphere E × Sphere E, ℝ) :=
  ∫ R, translated f R ∂haar E

omit [MeasurableSpace E] [BorelSpace E] in
theorem average_apply (f : C(Sphere E × Sphere E, ℝ)) (z : Sphere E × Sphere E) :
    average f z = ∫ R, f (diagonal R z) ∂haar E :=
  ContinuousMap.integral_apply
    (memLp_one_iff_integrable.mp ((translated f).memLp ℝ (p := 1) (μ := haar E))) z

omit [MeasurableSpace E] [BorelSpace E] in
theorem average_invariant (f : C(Sphere E × Sphere E, ℝ))
    (S : OrthogonalHaar.Group E) (z : Sphere E × Sphere E) :
    average f (diagonal S z) = average f z := by
  rw [average_apply, average_apply]
  simpa only [diagonal, rotate_mul] using
    integral_mul_right_eq_self (fun R : OrthogonalHaar.Group E => f (diagonal R z)) S

omit [MeasurableSpace E] [BorelSpace E] in
theorem average_factors (f : C(Sphere E × Sphere E, ℝ)) :
    Function.FactorsThrough (average f) (quotient (E := E)) := by
  intro z w h
  have hg : gram z = gram w := congrArg Subtype.val h
  obtain ⟨R, hx, hy⟩ := OrthogonalFrame.exists_pair_of_inner_eq z.1 z.2 w.1 w.2 hg
  have he : diagonal R z = w := Prod.ext hx hy
  rw [← he, average_invariant]

def descend (f : C(Sphere E × Sphere E, ℝ)) : C(GramRange E, ℝ) :=
  quotientMap.lift (average f) (average_factors f)

omit [MeasurableSpace E] [BorelSpace E] in
theorem descend_quotient (f : C(Sphere E × Sphere E, ℝ)) (z : Sphere E × Sphere E) :
    descend f (quotient z) = average f z :=
  congrArg (fun g : C(Sphere E × Sphere E, ℝ) => g z)
    (quotientMap.lift_comp (average f) (average_factors f))

def Invariant (nu : Measure (Sphere E × Sphere E)) : Prop :=
  ∀ R : OrthogonalHaar.Group E, MeasurePreserving (diagonal R) nu nu

theorem integral_average (nu : Measure (Sphere E × Sphere E)) [IsFiniteMeasure nu]
    (hn : Invariant nu) (f : C(Sphere E × Sphere E, ℝ)) :
    (∫ z, average f z ∂nu) = ∫ z, f z ∂nu := by
  simp_rw [average_apply]
  have hk : Integrable (fun z : (Sphere E × Sphere E) × OrthogonalHaar.Group E =>
      f (diagonal z.2 z.1)) (nu.prod (haar E)) :=
    memLp_one_iff_integrable.mp
      ((⟨_, f.continuous.comp (diagonal_continuous.comp continuous_swap)⟩ :
        C((Sphere E × Sphere E) × OrthogonalHaar.Group E, ℝ)).memLp ℝ (p := 1) (μ := nu.prod (haar E)))
  rw [integral_integral_swap hk]
  have he (R : OrthogonalHaar.Group E) :
      (∫ z, f (diagonal R z) ∂nu) = ∫ z, f z ∂nu :=
    by
      rw [← integral_map (hn R).measurable.aemeasurable f.continuous.aestronglyMeasurable,
        (hn R).map_eq]
  simp_rw [he]
  simp

/-- The one-dimensional Gram distribution determines a diagonally invariant finite measure. -/
theorem ext_of_gram (nu eta : Measure (Sphere E × Sphere E))
    [IsFiniteMeasure nu] [IsFiniteMeasure eta] (hn : Invariant nu) (he : Invariant eta)
    (hg : nu.map gram = eta.map gram) : nu = eta := by
  have hq : nu.map quotient = eta.map quotient := by
    apply (MeasurableEmbedding.subtype_coe (isCompact_range gram_continuous).measurableSet).map_injective
    rw [Measure.map_map measurable_subtype_coe quotient.continuous.measurable,
      Measure.map_map measurable_subtype_coe quotient.continuous.measurable]
    exact hg
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let fc : C(Sphere E × Sphere E, ℝ) := f.toContinuousMap
  calc
    (∫ z, f z ∂nu) = ∫ z, average fc z ∂nu := (integral_average nu hn fc).symm
    _ = ∫ t, descend fc t ∂nu.map quotient := by
      rw [integral_map quotient.continuous.measurable.aemeasurable
        (descend fc).continuous.aestronglyMeasurable]
      simp_rw [descend_quotient]
    _ = ∫ t, descend fc t ∂eta.map quotient := by rw [hq]
    _ = ∫ z, average fc z ∂eta := by
      rw [integral_map quotient.continuous.measurable.aemeasurable
        (descend fc).continuous.aestronglyMeasurable]
      simp_rw [descend_quotient]
    _ = ∫ z, f z ∂eta := integral_average eta he fc

end ShadowVerification.InvariantPair
#print axioms ShadowVerification.InvariantPair.diagonal_continuous
#print axioms ShadowVerification.InvariantPair.gram_continuous
#print axioms ShadowVerification.InvariantPair.quotientMap
#print axioms ShadowVerification.InvariantPair.average_apply
#print axioms ShadowVerification.InvariantPair.average_invariant
#print axioms ShadowVerification.InvariantPair.average_factors
#print axioms ShadowVerification.InvariantPair.descend_quotient
#print axioms ShadowVerification.InvariantPair.integral_average
#print axioms ShadowVerification.InvariantPair.ext_of_gram

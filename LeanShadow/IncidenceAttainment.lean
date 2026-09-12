import LeanShadow.ZonalKernelCompactness
import LeanShadow.IncidenceDensityRecovery

/-! # Unconditional compactness and attainment for the actual spherical profile

For ambient dimension n≥3, the actual two-step law has an integrable
scalar Gram density. Its operator is compact by zonal approximation.
It equals the square of the actual incidence operator. Self-adjointness
then gives compactness of incidence itself. The proved pointwise recovery
and the existing direct method yield optimal pairs at every prescribed area.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace ShadowVerification.IncidenceAttainment
open Spherical OrthogonalHaar InvariantPair ZonalCompactness
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

def twoStepOperator (a b : Sphere E) :
    Lp ℝ 2 (probability mu) →L[ℝ] Lp ℝ 2 (probability mu) :=
  CouplingOperator.operator (probability mu) (TwoStep.measure a b)
    (TwoStep.firstMarginal mu a b) (TwoStep.secondMarginal mu a b)

def scalarDensity (a b : Sphere E) (t : ℝ) : ℝ :=
  ((TwoStep.measure a b).map gram |>.rnDeriv (law mu)) t |>.toReal

omit [BorelSpace E] [mu.IsAddHaarMeasure] in
theorem scalarDensity_measurable (a b : Sphere E) : Measurable (scalarDensity mu a b) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

omit [mu.IsAddHaarMeasure] in
theorem scalarDensity_integrable (a b : Sphere E) : Integrable (scalarDensity mu a b) (law mu) := by
  unfold scalarDensity
  exact integrableOn_univ.mp
    (Measure.integrableOn_toReal_rnDeriv (μ := (TwoStep.measure a b).map gram) (ν := law mu)
      (s := Set.univ) (measure_ne_top _ _))

/-- An actual finite real density, defined almost everywhere by Radon–Nikodym. -/
theorem joint_eq (hd : 2 < Module.finrank ℝ E) (a b : Sphere E)
    (hba : inner ℝ (b : E) (a : E) = 0) :
    TwoStep.measure a b = KernelMeasure.joint (probability mu)
      (fun z => scalarDensity mu a b (gram z)) := by
  rw [PairDensity.density_eq _ _ (PairDensity.invariant_twoStep a b)
    (PairDensity.invariant_product mu) (TwoStepGram.absolutelyContinuous mu hd a b hba)]
  apply withDensity_congr_ae
  have hp : MeasurePreserving gram ((probability mu).prod (probability mu)) (law mu) :=
    ⟨gram_continuous.measurable, rfl⟩
  filter_upwards [hp.quasiMeasurePreserving.ae
    (Measure.rnDeriv_lt_top ((TwoStep.measure a b).map gram) (law mu))] with z hz
  exact (ENNReal.ofReal_toReal hz.ne).symm

/-- Compactness of the concrete two-step averaging operator. -/
theorem twoStep_compact (hd : 2 < Module.finrank ℝ E) (a b : Sphere E)
    (hba : inner ℝ (b : E) (a : E) = 0) : IsCompactOperator (twoStepOperator mu a b) := by
  apply ZonalCompactness.compact mu (scalarDensity mu a b) (scalarDensity_measurable mu a b)
    (fun _ => ENNReal.toReal_nonneg) (scalarDensity_integrable mu a b)
  intro u v
  rw [twoStepOperator, CouplingOperator.pairing, joint_eq mu hd a b hba]
  exact KernelMeasure.pairing (probability mu) _
    ((scalarDensity_measurable mu a b).comp gram_continuous.measurable)
    (fun _ => ENNReal.toReal_nonneg) u v

theorem twoStep_continuous_pairing (a b : Sphere E) (u v : C(Sphere E, ℝ)) :
    inner ℝ (ContinuousMap.toLp 2 (probability mu) ℝ u)
      (twoStepOperator mu a b (ContinuousMap.toLp 2 (probability mu) ℝ v)) =
      ∫ z : Sphere E × Sphere E, u z.1 * v z.2 ∂TwoStep.measure a b := by
  rw [twoStepOperator, CouplingOperator.pairing]
  apply integral_congr_ae
  filter_upwards [(TwoStep.firstMarginal mu a b).quasiMeasurePreserving.ae
      (ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) (probability mu) u),
    (TwoStep.secondMarginal mu a b).quasiMeasurePreserving.ae
      (ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) (probability mu) v)] with z hz hw
  rw [hz, hw]

/-- Identification with F² on all of L², using the density of continuous functions. -/
theorem square_eq (hd : 1 < Module.finrank ℝ E) (a b : Sphere E)
    (hab : inner ℝ (a : E) (b : E) = 0) :
    (SphericalIncidenceOperator.operator mu hd).comp (SphericalIncidenceOperator.operator mu hd) =
      twoStepOperator mu a b := by
  let F := SphericalIncidenceOperator.operator mu hd
  let T := twoStepOperator mu a b
  have hdense := ContinuousMap.toLp_denseRange ℝ (probability mu) ℝ
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  have he (v : C(Sphere E, ℝ)) :
      F (F (ContinuousMap.toLp 2 (probability mu) ℝ v)) =
        T (ContinuousMap.toLp 2 (probability mu) ℝ v) := by
    apply ext_inner_left ℝ
    have h := hdense.equalizer
      (show Continuous (fun u : Lp ℝ 2 (probability mu) =>
        inner ℝ u (F (F (ContinuousMap.toLp 2 (probability mu) ℝ v)))) by fun_prop)
      (show Continuous (fun u : Lp ℝ 2 (probability mu) =>
        inner ℝ u (T (ContinuousMap.toLp 2 (probability mu) ℝ v))) by fun_prop)
      (show _ = _ from funext fun u => by
        change inner ℝ (ContinuousMap.toLp 2 (probability mu) ℝ u)
          (F (F (ContinuousMap.toLp 2 (probability mu) ℝ v))) =
          inner ℝ (ContinuousMap.toLp 2 (probability mu) ℝ u)
            (T (ContinuousMap.toLp 2 (probability mu) ℝ v))
        exact (TwoStep.continuous_pairing mu hd a b hab u v).trans
          (twoStep_continuous_pairing mu a b u v).symm)
    exact fun u => congrFun h u
  have heq := hdense.equalizer (F.continuous.comp F.continuous) T.continuous (funext he)
  exact ContinuousLinearMap.ext (fun v => congrFun heq v)

/-- Unconditional compactness of the Haar orthogonality operator for n≥3. -/
theorem compact (hd : 2 < Module.finrank ℝ E) :
    IsCompactOperator (SphericalIncidenceOperator.operator mu (by omega)) := by
  have hd' : 1 < Module.finrank ℝ E := by omega
  obtain ⟨a,b,hab⟩ := OrthogonalIncidence.exists_orthogonal_pair hd'
  have hba : inner ℝ (b : E) (a : E) = 0 := by rw [real_inner_comm, hab]
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  apply CompactSquare.compact_of_comp_self (SphericalIncidenceOperator.operator mu hd')
    (SphericalIncidenceOperator.symmetric mu hd')
  change IsCompactOperator ((SphericalIncidenceOperator.operator mu hd').comp
    (SphericalIncidenceOperator.operator mu hd'))
  rw [square_eq mu hd' a b hab]
  exact twoStep_compact mu hd a b hba

/-- Attainment for the actual optimal profile, with no compactness or recovery hypothesis. -/
theorem exists_optimizer (hd : 2 < Module.finrank ℝ E)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ A B : Set (Sphere E), Profile.IsOptimalPair mu p A B ∧ Profile.IsOptimizer mu p A :=
  IncidenceRecovery.exists_optimizer_of_compact mu (by omega) (compact mu hd) p hp0 hp1

end ShadowVerification.IncidenceAttainment
#print axioms ShadowVerification.IncidenceAttainment.scalarDensity_measurable
#print axioms ShadowVerification.IncidenceAttainment.scalarDensity_integrable
#print axioms ShadowVerification.IncidenceAttainment.joint_eq
#print axioms ShadowVerification.IncidenceAttainment.twoStep_compact
#print axioms ShadowVerification.IncidenceAttainment.twoStep_continuous_pairing
#print axioms ShadowVerification.IncidenceAttainment.square_eq
#print axioms ShadowVerification.IncidenceAttainment.compact
#print axioms ShadowVerification.IncidenceAttainment.exists_optimizer

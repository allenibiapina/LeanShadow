import LeanShadow.SphericalLatitudeClass
import LeanShadow.IncidenceTwoStep

/-! # Stabilizer orbits are uniform on the perpendicular sphere -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace ShadowVerification.Equatorial
open Spherical OrthogonalHaar AxisCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

def embed (b : Sphere E) (y : Sphere (perpendicular b)) : Sphere E :=
  ⟨(y : perpendicular b), y.property⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem embed_continuous (b : Sphere E) : Continuous (embed b) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem embed_perpendicular (b : Sphere E) (y : Sphere (perpendicular b)) :
    inner ℝ (b : E) (embed b y : E) = 0 := inner_perpendicular b y

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem maps_perpendicular (b : Sphere E) (R : AxisStabilizer.subgroup b)
    (v : E) (hv : v ∈ perpendicular b) : (R.1 : E →L[ℝ] E) v ∈ perpendicular b := by
  have hb : (R.1 : E →L[ℝ] E) b = (b : E) := congrArg Subtype.val R.property
  have h := Unitary.inner_map_map R.1 (b : E) v
  rw [hb] at h
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  exact h.trans (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hv)

def restriction (b : Sphere E) (R : AxisStabilizer.subgroup b) :
    perpendicular b ≃ₗᵢ[ℝ] perpendicular b where
  toFun v := ⟨(R.1 : E →L[ℝ] E) v, maps_perpendicular b R v v.property⟩
  invFun v := ⟨((R⁻¹).1 : E →L[ℝ] E) v, maps_perpendicular b R⁻¹ v v.property⟩
  left_inv v := by
    apply Subtype.ext
    change (((R⁻¹).1 * R.1 : OrthogonalHaar.Group E) : E →L[ℝ] E) v = (v : E)
    simp
  right_inv v := by
    apply Subtype.ext
    change ((R.1 * (R⁻¹).1 : OrthogonalHaar.Group E) : E →L[ℝ] E) v = (v : E)
    simp
  map_add' v w := by apply Subtype.ext; exact map_add (R.1 : E →L[ℝ] E) (v : E) (w : E)
  map_smul' t v := by apply Subtype.ext; exact map_smul (R.1 : E →L[ℝ] E) t (v : E)
  norm_map' v := Unitary.norm_map R.1 v

def restrictedRotation (b : Sphere E) (R : AxisStabilizer.subgroup b) :
    OrthogonalHaar.Group (perpendicular b) := Unitary.linearIsometryEquiv.symm (restriction b R)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem embed_rotate (b : Sphere E) (R : AxisStabilizer.subgroup b)
    (y : Sphere (perpendicular b)) :
    embed b (rotate (restrictedRotation b R) y) = rotate R.1 (embed b y) := by
  apply Subtype.ext
  rfl

/-- Stabilizer Haar orbits depend only on the latitude of their starting point. -/
theorem orbit_map_eq (b a x : Sphere E)
    (h : inner ℝ (b : E) (a : E) = inner ℝ (b : E) (x : E)) :
    (AxisStabilizer.haar b).map (fun R => rotate R.1 a) =
      (AxisStabilizer.haar b).map (fun R => rotate R.1 x) := by
  obtain ⟨S, hS⟩ := AxisStabilizer.exists_latitude b a x h
  have hm : Measurable (fun R : AxisStabilizer.subgroup b => rotate R.1 a) :=
    (rotate_continuous.comp (continuous_subtype_val.prodMk continuous_const)).measurable
  calc
    _ = ((AxisStabilizer.haar b).map (· * S)).map (fun R => rotate R.1 a) := by
      rw [AxisStabilizer.haar_map_right]
    _ = _ := by
      rw [Measure.map_map hm (continuous_mul_const S).measurable]
      congr 1
      funext R
      simp only [Function.comp_apply, Subgroup.coe_mul, rotate_mul, hS]

/-- The orbit law agrees with the existing Haar-induced measure of the perpendicular subspace. -/
theorem orbit_map_spherical (hd : 1 < Module.finrank ℝ E) (b a : Sphere E)
    (hba : inner ℝ (b : E) (a : E) = 0) :
    let : Nontrivial (perpendicular b) := perpendicular_nontrivial b hd
    (AxisStabilizer.haar b).map (fun R => rotate R.1 a) =
      (probability (Measure.addHaar : Measure (perpendicular b))).map (embed b) := by
  let : Nontrivial (perpendicular b) := perpendicular_nontrivial b hd
  apply Measure.ext
  intro A hA
  let F : Sphere E → ℝ≥0∞ := A.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hA
  have hm (x : Sphere E) : Measurable (fun R : AxisStabilizer.subgroup b => rotate R.1 x) :=
    (rotate_continuous.comp (continuous_subtype_val.prodMk continuous_const)).measurable
  have hc (y : Sphere (perpendicular b)) :
      (∫⁻ R : AxisStabilizer.subgroup b, F (rotate R.1 a) ∂AxisStabilizer.haar b) =
        ∫⁻ R : AxisStabilizer.subgroup b, F (rotate R.1 (embed b y)) ∂AxisStabilizer.haar b := by
    rw [← lintegral_map hF (hm a), ← lintegral_map hF (hm (embed b y)),
      orbit_map_eq b a (embed b y) (hba.trans (embed_perpendicular b y).symm)]
  calc
    ((AxisStabilizer.haar b).map (fun R => rotate R.1 a)) A =
        ∫⁻ R, F (rotate R.1 a) ∂AxisStabilizer.haar b := by
      rw [← lintegral_map hF (hm a)]
      simp [F, lintegral_indicator hA]
    _ = ∫⁻ y : Sphere (perpendicular b), ∫⁻ R, F (rotate R.1 (embed b y))
        ∂AxisStabilizer.haar b ∂probability (Measure.addHaar : Measure (perpendicular b)) := by
      simp_rw [← hc]
      simp
    _ = ∫⁻ R : AxisStabilizer.subgroup b, ∫⁻ y, F (rotate R.1 (embed b y))
        ∂probability (Measure.addHaar : Measure (perpendicular b)) ∂AxisStabilizer.haar b := by
      apply lintegral_lintegral_swap
      exact (hF.comp (rotate_continuous.comp
        ((continuous_subtype_val.comp continuous_snd).prodMk
          ((embed_continuous b).comp continuous_fst))).measurable).aemeasurable
    _ = _ := by
      simp_rw [← embed_rotate]
      have hp (R : AxisStabilizer.subgroup b) :=
        (SphericalRotation.measurePreserving_rotate (Measure.addHaar : Measure (perpendicular b))
          (restrictedRotation b R)).lintegral_comp (hF.comp (embed_continuous b).measurable)
      have he (R : AxisStabilizer.subgroup b) :
          (∫⁻ y, F (embed b (rotate (restrictedRotation b R) y))
            ∂probability (Measure.addHaar : Measure (perpendicular b))) =
          ∫⁻ y, F (embed b y) ∂probability (Measure.addHaar : Measure (perpendicular b)) := hp R
      simp_rw [he]
      simp only [lintegral_const, measure_univ, mul_one]
      rw [← lintegral_map hF (embed_continuous b).measurable]
      simp [F, lintegral_indicator hA]

end ShadowVerification.Equatorial
#print axioms ShadowVerification.Equatorial.embed_continuous
#print axioms ShadowVerification.Equatorial.embed_perpendicular
#print axioms ShadowVerification.Equatorial.maps_perpendicular
#print axioms ShadowVerification.Equatorial.embed_rotate
#print axioms ShadowVerification.Equatorial.orbit_map_eq
#print axioms ShadowVerification.Equatorial.orbit_map_spherical

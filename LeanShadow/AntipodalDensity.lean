import LeanShadow.SphericalDensityPoint
import LeanShadow.ProjectiveCompression

/-! # Density at both ends of a compression axis

For antipodal sets, the relative mass in a pair of small opposite spherical
balls is exactly the relative mass in either ball. Thus the density-zero axis
obtained from Besicovitch differentiation also has zero projective-cap density.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace ShadowVerification.AntipodalDensity
open Spherical Antipodal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem antipode_dist (x y : Sphere E) : dist (antipode x) (antipode y) = dist x y :=
  dist_neg_neg (x : E) (y : E)

omit [InnerProductSpace ℝ E] in
theorem antipode_image_closedBall (e : Sphere E) (r : ℝ) :
    antipode '' closedBall e r = closedBall (antipode e) r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [mem_closedBall, antipode_dist] using hy
  · intro hx
    refine ⟨antipode x, ?_, antipode_twice x⟩
    have h := antipode_dist x (antipode e)
    rw [antipode_twice] at h
    simpa only [mem_closedBall, h] using hx

theorem opposite_balls_disjoint (e : Sphere E) (r : ℝ) (hr : r < 1) :
    Disjoint (closedBall e r) (closedBall (antipode e) r) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hdist : dist e (antipode e) = 2 := by
    rw [Subtype.dist_eq, dist_eq_norm]
    change ‖(e : E) - -(e : E)‖ = 2
    rw [sub_neg_eq_add, ← two_smul ℝ (e : E), norm_smul,
      mem_sphere_zero_iff_norm.mp e.property]
    norm_num
  have h := dist_triangle e x (antipode e)
  rw [hdist, dist_comm e x] at h
  have hx' := mem_closedBall.mp hx
  have hy' := mem_closedBall.mp hy
  linarith

def doubleBall (e : Sphere E) (r : ℝ) : Set (Sphere E) :=
  closedBall e r ∪ closedBall (antipode e) r

omit [InnerProductSpace ℝ E] in
theorem measurableSet_doubleBall [MeasurableSpace E] [BorelSpace E]
    (e : Sphere E) (r : ℝ) : MeasurableSet (doubleBall e r) :=
  isClosed_closedBall.measurableSet.union isClosed_closedBall.measurableSet

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

/-- Spherical probability measure is unchanged by the actual antipodal map. -/
theorem measure_antipode_image (A : Set (Sphere E)) (hA : MeasurableSet A) :
    probability mu (antipode '' A) = probability mu A := by
  have hact : action (ContinuousLinearEquiv.neg ℝ (M := E)) = antipode := by
    funext x
    apply Subtype.ext
    change NormedSpace.normalize (-(x : E)) = -(x : E)
    rw [NormedSpace.normalize_neg,
      NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp x.property)]
  have ha := Invariance.area_of_constant_unit_norm mu A hA
    (ContinuousLinearEquiv.neg ℝ (M := E)) 1 zero_lt_one
    (fun x => by simpa only [ContinuousLinearEquiv.neg_apply, norm_neg] using
      mem_sphere_zero_iff_norm.mp x.property)
  rw [transformedArea, hact] at ha
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp ha

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [Nontrivial E] in
theorem antipode_image_inter (A : Set (Sphere E)) (hanti : IsAntipodal A) (D : Set (Sphere E)) :
    antipode '' (A ∩ D) = A ∩ (antipode '' D) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyA, hyD⟩, rfl⟩
    exact ⟨hanti y hyA, ⟨y, hyD, rfl⟩⟩
  · rintro ⟨hx, y, hy, rfl⟩
    exact ⟨y, ⟨by simpa only [antipode_twice] using hanti _ hx, hy⟩, rfl⟩

theorem measure_doubleBall (e : Sphere E) (r : ℝ) (hr : r < 1) :
    probability mu (doubleBall e r) = 2 * probability mu (closedBall e r) := by
  rw [doubleBall, measure_union (opposite_balls_disjoint e r hr) isClosed_closedBall.measurableSet,
    ← antipode_image_closedBall, measure_antipode_image mu _ isClosed_closedBall.measurableSet,
    two_mul]

theorem measure_inter_doubleBall (A : Set (Sphere E)) (hA : MeasurableSet A)
    (hanti : IsAntipodal A) (e : Sphere E) (r : ℝ) (hr : r < 1) :
    probability mu (A ∩ doubleBall e r) = 2 * probability mu (A ∩ closedBall e r) := by
  rw [doubleBall, inter_union_distrib_left,
    measure_union ((opposite_balls_disjoint e r hr).mono inter_subset_right inter_subset_right)
      (hA.inter isClosed_closedBall.measurableSet),
    ← antipode_image_closedBall, ← antipode_image_inter A hanti,
    measure_antipode_image mu _ (hA.inter isClosed_closedBall.measurableSet), two_mul]

theorem doubleBall_density_ratio (A : Set (Sphere E)) (hA : MeasurableSet A)
    (hanti : IsAntipodal A) (e : Sphere E) (r : ℝ) (hr : r < 1) :
    probability mu (A ∩ doubleBall e r) / probability mu (doubleBall e r) =
      probability mu (A ∩ closedBall e r) / probability mu (closedBall e r) := by
  rw [measure_inter_doubleBall mu A hA hanti e r hr, measure_doubleBall mu e r hr]
  exact ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)

/-- Every positive complement of an antipodal Borel set supplies an axis
with zero relative mass in small projective caps. -/
theorem exists_doubleBall_density_zero (A : Set (Sphere E)) (hA : MeasurableSet A)
    (hanti : IsAntipodal A) (hp : area mu A < 1) :
    ∃ e : Sphere E, e ∉ A ∧
      Tendsto (fun r => probability mu (A ∩ doubleBall e r) / probability mu (doubleBall e r))
        (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨e, he, hd⟩ := SphericalDensity.exists_axis_of_area_lt_one mu A hA hp
  refine ⟨e, he, hd.congr' ?_⟩
  filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with r hr
  exact (doubleBall_density_ratio mu A hA hanti e r hr).symm

end ShadowVerification.AntipodalDensity
#print axioms ShadowVerification.AntipodalDensity.antipode_dist
#print axioms ShadowVerification.AntipodalDensity.antipode_image_closedBall
#print axioms ShadowVerification.AntipodalDensity.opposite_balls_disjoint
#print axioms ShadowVerification.AntipodalDensity.measurableSet_doubleBall
#print axioms ShadowVerification.AntipodalDensity.measure_antipode_image
#print axioms ShadowVerification.AntipodalDensity.antipode_image_inter
#print axioms ShadowVerification.AntipodalDensity.measure_doubleBall
#print axioms ShadowVerification.AntipodalDensity.measure_inter_doubleBall
#print axioms ShadowVerification.AntipodalDensity.doubleBall_density_ratio
#print axioms ShadowVerification.AntipodalDensity.exists_doubleBall_density_zero

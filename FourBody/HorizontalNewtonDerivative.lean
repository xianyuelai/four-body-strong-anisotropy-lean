import FourBody.Reuse.NewtonBounds
import FourBody.Operators
import FourBody.ScalarGeometry
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Actual Newton-field differentiation at a horizontal one-dimensional seed.
The finite label type is arbitrary, so it includes every `Fin n`, finite
cluster subtypes and the empty/singleton cases. The force displacement is
target minus source, exactly as in the frozen v2 and FourBody.Geometry.

The derivative is first proved on the full planar configuration space from
the already proved true Newton target-field derivative. Its horizontal and
vertical coordinate formulas are subsequently identified with the actual
GeneralOperator inverse-cube Laplacian. No Jacobian formula, invertibility,
scalar seed existence or analytic interface is assumed.

Preparation status: this new module still requires compilation in the parent's
serial window. It does not assert completion of Proposition 4.1.
-/

noncomputable section
open scoped BigOperators

namespace FourBody.HorizontalNewton

open FourBody.Reuse
open FourBody.GeneralOperator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Configuration (ι : Type*) := ι → Plane
abbrev ConfigurationN (n : ℕ) := Configuration (Fin n)

def xy (x y : ℝ) : Plane := !₂[x, y]

@[simp] theorem xy_x (x y : ℝ) : xy x y 0 = x := rfl
@[simp] theorem xy_y (x y : ℝ) : xy x y 1 = y := rfl

theorem xy_sub (x y a b : ℝ) : xy x y - xy a b = xy (x - a) (y - b) := by
  ext k
  fin_cases k <;> simp [xy, PiLp.sub_apply]

theorem zero_sub_xy (x : ℝ) : (0 : Plane) - xy x 0 = xy (-x) 0 := by
  ext k
  fin_cases k <;> simp [xy]

theorem norm_xy_horizontal (x : ℝ) : ‖xy x 0‖ = |x| := by
  have hs : ‖xy x 0‖ ^ 2 = |x| ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simp [xy, sq_abs]
  exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp hs

theorem inner_xy_horizontal (x : ℝ) (v : Plane) :
    inner ℝ (xy x 0) v = x * v 0 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [xy, mul_comm]

theorem plane_sum_apply {κ : Type*} (S : Finset κ) (f : κ → Plane) (k : Fin 2) :
    (∑ j ∈ S, f j) k = ∑ j ∈ S, f j k := by
  simp only [WithLp.ofLp_sum, Finset.sum_apply]

/-- Translation of both physical source and target is handled explicitly. -/
theorem physicalNewtonForce_eq_difference (m : ℝ) (source target : Plane) :
    physicalNewtonForce m source target =
      physicalNewtonForce m 0 (target - source) := by
  simp only [physicalNewtonForce, dist_eq_norm, sub_zero]

def displacement (i j : ι) : Configuration ι →L[ℝ] Plane :=
  (ContinuousLinearMap.proj i : Configuration ι →L[ℝ] Plane) -
    ContinuousLinearMap.proj j

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem displacement_apply (i j : ι) (q : Configuration ι) :
    displacement i j q = q i - q j := rfl

omit [DecidableEq ι] in
/-- Both source and target vary in the same ambient configuration. -/
theorem movingPair_hasFDerivAt (m : ℝ) (q : Configuration ι) (i j : ι)
    (hij : q i ≠ q j) :
    HasFDerivAt (fun p : Configuration ι => physicalNewtonForce m (p j) (p i))
      (((-m) • newtonTargetDerivative 0 (q i - q j)).comp (displacement i j)) q := by
  have hzero : (0 : Plane) ≠ q i - q j :=
    (sub_ne_zero.mpr hij).symm
  have hd := (physicalNewtonForce_hasFDerivAt m 0 (q i - q j) hzero).comp q
    ((displacement i j).hasFDerivAt)
  convert! hd using 1
  funext p
  exact physicalNewtonForce_eq_difference m (p j) (p i)

def totalNewtonField (μ : Coordinates ι) (q : Configuration ι) : Configuration ι :=
  fun i => ∑ j ∈ Finset.univ.erase i, physicalNewtonForce (μ j) (q j) (q i)

def newtonDerivative (μ : Coordinates ι) (q : Configuration ι) :
    Configuration ι →L[ℝ] Configuration ι :=
  ContinuousLinearMap.pi fun i =>
    ∑ j ∈ Finset.univ.erase i,
      (((-μ j) • newtonTargetDerivative 0 (q i - q j)).comp (displacement i j))

@[simp] theorem newtonDerivative_apply (μ : Coordinates ι) (q v : Configuration ι)
    (i : ι) :
    newtonDerivative μ q v i = ∑ j ∈ Finset.univ.erase i,
      ((-μ j) • newtonTargetDerivative 0 (q i - q j)) (v i - v j) := by
  simp only [newtonDerivative, ContinuousLinearMap.pi_apply, sum_apply,
    ContinuousLinearMap.comp_apply, displacement_apply]

/-- Genuine full-space Frechet derivative; masses need not be normalized. -/
theorem totalNewtonField_hasFDerivAt (μ : Coordinates ι) (q : Configuration ι)
    (hq : Function.Injective q) :
    HasFDerivAt (totalNewtonField μ) (newtonDerivative μ q) q := by
  unfold totalNewtonField newtonDerivative
  apply hasFDerivAt_pi.mpr
  intro i
  apply HasFDerivAt.fun_sum
  intro j hj
  apply movingPair_hasFDerivAt
  intro heq
  exact (Finset.mem_erase.mp hj).1 ((hq heq).symm)

theorem totalNewtonField_fderiv (μ : Coordinates ι) (q : Configuration ι)
    (hq : Function.Injective q) :
    fderiv ℝ (totalNewtonField μ) q = newtonDerivative μ q :=
  (totalNewtonField_hasFDerivAt μ q hq).fderiv

/-- Exact bridge to the original labeled four-body field. -/
theorem totalNewtonField_four_eq_force (μ : FourBody.Masses)
    (q : FourBody.Configuration) :
    totalNewtonField μ q = FourBody.force μ q := by
  funext i
  rfl

omit [Fintype ι] in
/-- Exact finite-cluster bridge. This aligns the subtype's total field with
the actual `S.erase i` sum used by the blow-up inner-field rows. -/
theorem subtype_totalNewtonField_eq_finiteSum (S : Finset ι) (μ : Coordinates ι)
    (q : Configuration ι) (i : S) :
    totalNewtonField (fun j : S => μ j) (fun j : S => q j) i =
      ∑ j ∈ S.erase (i : ι), physicalNewtonForce (μ j) (q j) (q i) := by
  let f : ι → Plane := fun j => physicalNewtonForce (μ j) (q j) (q i)
  have hf : f i = 0 := by simp [f, physicalNewtonForce]
  calc
    totalNewtonField (fun j : S => μ j) (fun j : S => q j) i =
        ∑ j : S, f j := by
      change (∑ j ∈ Finset.univ.erase i, f j) = ∑ j : S, f j
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hf, sub_zero]
    _ = ∑ j ∈ S, f j := Finset.sum_coe_sort S f
    _ = ∑ j ∈ S.erase (i : ι), f j := by
      rw [Finset.sum_erase_eq_sub i.property, hf, sub_zero]
    _ = _ := rfl

theorem singleton_totalNewtonField_zero (μ : Fin 1 → ℝ) (q : ConfigurationN 1) :
    totalNewtonField μ q = 0 := by
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  simp [totalNewtonField]

theorem singleton_newtonDerivative_zero (μ : Fin 1 → ℝ) (q : ConfigurationN 1) :
    newtonDerivative μ q = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  simp [newtonDerivative_apply]

def horizontalConfiguration (z : Coordinates ι) : Configuration ι := fun i => xy (z i) 0

omit [Fintype ι] [DecidableEq ι] in
theorem horizontalConfiguration_injective (z : Coordinates ι)
    (hz : Function.Injective z) : Function.Injective (horizontalConfiguration z) := by
  intro i j heq
  apply hz
  have hx := congrArg (fun p : Plane => p 0) heq
  simpa [horizontalConfiguration] using hx

/-- The signed pair derivative: horizontal -2 and vertical +1. -/
theorem physicalPairDerivative_horizontal (m d : ℝ) (hd : d ≠ 0) (v : Plane) :
    ((-m) • newtonTargetDerivative 0 (xy d 0)) v =
      xy (-2 * m * (|d| ^ 3)⁻¹ * v 0) (m * (|d| ^ 3)⁻¹ * v 1) := by
  have habs : |d| ≠ 0 := abs_ne_zero.mpr hd
  have hcoef : (3 / |d| ^ 5) * d ^ 2 - (|d| ^ 3)⁻¹ =
      2 * (|d| ^ 3)⁻¹ := by
    rw [← sq_abs d]
    field_simp [habs]
    ring
  rw [smul_apply, newtonTargetDerivative_apply]
  rw [zero_sub_xy, norm_xy_horizontal, inner_xy_horizontal, abs_neg]
  ext k
  fin_cases k
  · change (-m) * ((3 / |d| ^ 5 * (-d * v 0)) * -d -
      (|d| ^ 3)⁻¹ * v 0) = -2 * m * (|d| ^ 3)⁻¹ * v 0
    calc
      (-m) * ((3 / |d| ^ 5 * (-d * v 0)) * -d - (|d| ^ 3)⁻¹ * v 0) =
          (-m) * (((3 / |d| ^ 5) * d ^ 2 - (|d| ^ 3)⁻¹) * v 0) := by ring
      _ = -2 * m * (|d| ^ 3)⁻¹ * v 0 := by rw [hcoef]; ring
  · change (-m) * ((3 / |d| ^ 5 * (-d * v 0)) * 0 -
      (|d| ^ 3)⁻¹ * v 1) = m * (|d| ^ 3)⁻¹ * v 1
    ring

def axisCoordinates (q : Configuration ι) (k : Fin 2) : Coordinates ι := fun i => q i k

def axisProjectionLM (k : Fin 2) : Configuration ι →ₗ[ℝ] Coordinates ι where
  toFun q := axisCoordinates q k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def axisProjection (k : Fin 2) : Configuration ι →L[ℝ] Coordinates ι :=
  (axisProjectionLM k).toContinuousLinearMap

def combineLM : (Coordinates ι × Coordinates ι) →ₗ[ℝ] Configuration ι where
  toFun u i := xy (u.1 i) (u.2 i)
  map_add' u v := by
    funext i
    ext k
    fin_cases k <;> simp [xy, PiLp.add_apply]
  map_smul' a u := by
    funext i
    ext k
    fin_cases k <;> simp [xy, PiLp.smul_apply, smul_eq_mul]

def combine : (Coordinates ι × Coordinates ι) →L[ℝ] Configuration ι :=
  combineLM.toContinuousLinearMap

/-- The two scalar Laplacian blocks are actual continuous linear maps. -/
def horizontalBlockDerivative (μ z : Coordinates ι) :
    Configuration ι →L[ℝ] Configuration ι :=
  combine.comp
    (((-2 : ℝ) • ((laplacian μ (inverseCubeCoefficient z)).toContinuousLinearMap.comp
      (axisProjection 0))).prod
      ((laplacian μ (inverseCubeCoefficient z)).toContinuousLinearMap.comp
        (axisProjection 1)))

omit [DecidableEq ι] in
@[simp] theorem horizontalBlockDerivative_apply (μ z : Coordinates ι)
    (v : Configuration ι) (i : ι) :
    horizontalBlockDerivative μ z v i =
      xy (-2 * laplacian μ (inverseCubeCoefficient z) (axisCoordinates v 0) i)
        (laplacian μ (inverseCubeCoefficient z) (axisCoordinates v 1) i) := rfl

theorem newtonDerivative_horizontal_apply (μ z : Coordinates ι)
    (hz : Function.Injective z) (v : Configuration ι) (i : ι) :
    newtonDerivative μ (horizontalConfiguration z) v i =
      xy (-2 * laplacian μ (inverseCubeCoefficient z) (axisCoordinates v 0) i)
        (laplacian μ (inverseCubeCoefficient z) (axisCoordinates v 1) i) := by
  rw [newtonDerivative_apply]
  have hterms : (∑ j ∈ Finset.univ.erase i,
      ((-μ j) • newtonTargetDerivative 0
        (horizontalConfiguration z i - horizontalConfiguration z j)) (v i - v j)) =
      ∑ j ∈ Finset.univ.erase i,
        xy (-2 * μ j * (|z i - z j| ^ 3)⁻¹ * (v i 0 - v j 0))
          (μ j * (|z i - z j| ^ 3)⁻¹ * (v i 1 - v j 1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hne : z i - z j ≠ 0 := sub_ne_zero.mpr (fun heq =>
      (Finset.mem_erase.mp hj).1 ((hz heq).symm))
    simp only [horizontalConfiguration, xy_sub, sub_self]
    rw [physicalPairDerivative_horizontal (μ j) (z i - z j) hne]
    simp only [PiLp.sub_apply]
  rw [hterms]
  ext k
  fin_cases k
  · rw [plane_sum_apply]
    change (∑ j ∈ Finset.univ.erase i,
      -2 * μ j * (|z i - z j| ^ 3)⁻¹ * (v i 0 - v j 0)) =
        -2 * laplacian μ (inverseCubeCoefficient z) (axisCoordinates v 0) i
    rw [laplacian_inverseCube_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [axisCoordinates, div_eq_mul_inv]
    ring
  · rw [plane_sum_apply]
    change (∑ j ∈ Finset.univ.erase i,
      μ j * (|z i - z j| ^ 3)⁻¹ * (v i 1 - v j 1)) =
        laplacian μ (inverseCubeCoefficient z) (axisCoordinates v 1) i
    rw [laplacian_inverseCube_apply]
    apply Finset.sum_congr rfl
    intro j _
    simp only [axisCoordinates, div_eq_mul_inv]
    ring

theorem newtonDerivative_horizontal_eq_block (μ z : Coordinates ι)
    (hz : Function.Injective z) :
    newtonDerivative μ (horizontalConfiguration z) = horizontalBlockDerivative μ z := by
  apply ContinuousLinearMap.ext
  intro v
  funext i
  exact newtonDerivative_horizontal_apply μ z hz v i

theorem totalNewtonField_horizontal_hasFDerivAt (μ z : Coordinates ι)
    (hz : Function.Injective z) :
    HasFDerivAt (totalNewtonField μ) (horizontalBlockDerivative μ z)
      (horizontalConfiguration z) := by
  have hd := totalNewtonField_hasFDerivAt μ (horizontalConfiguration z)
    (horizontalConfiguration_injective z hz)
  rwa [newtonDerivative_horizontal_eq_block μ z hz] at hd

theorem totalNewtonField_horizontal_fderiv_x (μ z : Coordinates ι)
    (hz : Function.Injective z) (v : Configuration ι) (i : ι) :
    (fderiv ℝ (totalNewtonField μ) (horizontalConfiguration z) v i) 0 =
      -2 * laplacian μ (inverseCubeCoefficient z) (axisCoordinates v 0) i := by
  rw [(totalNewtonField_horizontal_hasFDerivAt μ z hz).fderiv]
  simp only [horizontalBlockDerivative_apply, xy_x]

theorem totalNewtonField_horizontal_fderiv_y (μ z : Coordinates ι)
    (hz : Function.Injective z) (v : Configuration ι) (i : ι) :
    (fderiv ℝ (totalNewtonField μ) (horizontalConfiguration z) v i) 1 =
      laplacian μ (inverseCubeCoefficient z) (axisCoordinates v 1) i := by
  rw [(totalNewtonField_horizontal_hasFDerivAt μ z hz).fderiv]
  simp only [horizontalBlockDerivative_apply, xy_y]

/-- The two independently defined scalar mass-center maps coincide exactly. -/
theorem scalarCenter_eq_scalarCenterLM {n : ℕ} (μ : Fin n → ℝ) :
    scalarCenter μ = FourBody.ScalarGeometry.scalarCenterLM μ := by
  ext h
  rfl

theorem centeredSpace_eq_ScalarW {n : ℕ} (μ : Fin n → ℝ) :
    centeredSpace μ = FourBody.ScalarGeometry.ScalarW μ := by
  exact congrArg LinearMap.ker (scalarCenter_eq_scalarCenterLM μ)

def centeredEmbedding (μ : Coordinates ι) :
    (centeredSpace μ × centeredSpace μ) →L[ℝ] Configuration ι :=
  combine.comp ((centeredSpace μ).subtypeL.prodMap (centeredSpace μ).subtypeL)

omit [DecidableEq ι] in
@[simp] theorem centeredEmbedding_apply (μ : Coordinates ι)
    (u : centeredSpace μ × centeredSpace μ) (i : ι) :
    centeredEmbedding μ u i =
      xy ((u.1 : Coordinates ι) i) ((u.2 : Coordinates ι) i) := rfl

omit [DecidableEq ι] in
@[simp] theorem centeredEmbedding_axis_x (μ : Coordinates ι)
    (h t : centeredSpace μ) :
    axisCoordinates (centeredEmbedding μ (h, t)) 0 = (h : Coordinates ι) := by
  funext i
  simp only [axisCoordinates, centeredEmbedding_apply, xy_x]

omit [DecidableEq ι] in
@[simp] theorem centeredEmbedding_axis_y (μ : Coordinates ι)
    (h t : centeredSpace μ) :
    axisCoordinates (centeredEmbedding μ (h, t)) 1 = (t : Coordinates ι) := by
  funext i
  simp only [axisCoordinates, centeredEmbedding_apply, xy_y]

def planeCenter (μ : Coordinates ι) (q : Configuration ι) : Plane := ∑ i, μ i • q i

omit [DecidableEq ι] in
theorem planeCenter_axis (μ : Coordinates ι) (q : Configuration ι) (k : Fin 2) :
    planeCenter μ q k = scalarCenter μ (axisCoordinates q k) := by
  rw [planeCenter, plane_sum_apply]
  simp only [PiLp.smul_apply, smul_eq_mul, scalarCenter_apply, axisCoordinates]

omit [DecidableEq ι] in
theorem centeredEmbedding_planeCenter_zero (μ : Coordinates ι)
    (h t : centeredSpace μ) : planeCenter μ (centeredEmbedding μ (h, t)) = 0 := by
  ext k
  fin_cases k
  · rw [planeCenter_axis]
    change scalarCenter μ (axisCoordinates (centeredEmbedding μ (h, t)) 0) = 0
    rw [centeredEmbedding_axis_x]
    exact h.property
  · rw [planeCenter_axis]
    change scalarCenter μ (axisCoordinates (centeredEmbedding μ (h, t)) 1) = 0
    rw [centeredEmbedding_axis_y]
    exact t.property

omit [DecidableEq ι] in
theorem horizontalBlockDerivative_centered (μ z : Coordinates ι)
    (h t : centeredSpace μ) :
    horizontalBlockDerivative μ z (centeredEmbedding μ (h, t)) =
      centeredEmbedding μ
        ((-2 : ℝ) • centeredLaplacian μ (inverseCubeCoefficient z)
            (inverseCubeCoefficient_symmetric z) h,
          centeredLaplacian μ (inverseCubeCoefficient z)
            (inverseCubeCoefficient_symmetric z) t) := by
  funext i
  rw [horizontalBlockDerivative_apply, centeredEmbedding_axis_x, centeredEmbedding_axis_y]
  rfl

omit [DecidableEq ι] in
theorem centeredEmbedding_horizontal (μ : Coordinates ι) (z : centeredSpace μ) :
    centeredEmbedding μ (z, 0) = horizontalConfiguration (z : Coordinates ι) := by
  funext i
  simp only [centeredEmbedding_apply, horizontalConfiguration, Submodule.coe_zero,
    Pi.zero_apply]

/-- Actual derivative on the product of two constrained scalar center spaces. -/
theorem centeredSlice_hasFDerivAt (μ : Coordinates ι) (z : centeredSpace μ)
    (hz : Function.Injective (z : Coordinates ι)) :
    HasFDerivAt (fun u : centeredSpace μ × centeredSpace μ =>
      totalNewtonField μ (centeredEmbedding μ u))
      ((horizontalBlockDerivative μ (z : Coordinates ι)).comp (centeredEmbedding μ))
      (z, 0) := by
  have hd := totalNewtonField_horizontal_hasFDerivAt μ (z : Coordinates ι) hz
  rw [← centeredEmbedding_horizontal μ z] at hd
  exact hd.comp (z, 0) ((centeredEmbedding μ).hasFDerivAt)

theorem centeredSlice_fderiv_apply (μ : Coordinates ι) (z : centeredSpace μ)
    (hz : Function.Injective (z : Coordinates ι)) (h t : centeredSpace μ) :
    fderiv ℝ (fun u : centeredSpace μ × centeredSpace μ =>
      totalNewtonField μ (centeredEmbedding μ u)) (z, 0) (h, t) =
      centeredEmbedding μ
        ((-2 : ℝ) • centeredLaplacian μ (inverseCubeCoefficient (z : Coordinates ι))
            (inverseCubeCoefficient_symmetric (z : Coordinates ι)) h,
          centeredLaplacian μ (inverseCubeCoefficient (z : Coordinates ι))
            (inverseCubeCoefficient_symmetric (z : Coordinates ι)) t) := by
  rw [(centeredSlice_hasFDerivAt μ z hz).fderiv]
  exact horizontalBlockDerivative_centered μ (z : Coordinates ι) h t

end FourBody.HorizontalNewton

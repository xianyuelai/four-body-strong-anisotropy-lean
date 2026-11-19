import FourBody.Reuse.NewtonKernel
import FourBody.Geometry
import Mathlib.Analysis.Calculus.MeanValue

/-! The current manuscript's force uses the negative of the legacy
Newton target field. The equality and true derivative are proved here.
The old exterior bound used 4/r^3; the current two-scale estimates require
the sharp 2/r^3 bound, established by the actual squared-norm identity.
This module uses arbitrary finite source sets and no five-body assumptions.
-/
noncomputable section
open scoped BigOperators
open Set
namespace FourBody.Reuse

def physicalNewtonForce (m : ℝ) (source target : Plane) : Plane :=
  (m / dist target source ^ 3) • (target-source)

/-- The reused field is identified with the actual force in the current
four-body geometry module, with the exact labeled erase-sum. -/
theorem force_eq_sum_physicalNewtonForce (m : FourBody.Masses)
    (q : FourBody.Configuration) (i : FourBody.Label) :
    FourBody.force m q i = ∑ j ∈ Finset.univ.erase i,
      physicalNewtonForce (m j) (q j) (q i) := rfl

theorem physicalNewtonForce_eq_neg_legacy (m : ℝ) (source target : Plane) :
    physicalNewtonForce m source target = -(m • newtonTargetField source target) := by
  unfold physicalNewtonForce newtonTargetField
  rw [dist_eq_norm, norm_sub_rev target source, div_eq_mul_inv, mul_smul]
  have hs : target-source=-(source-target) := by abel
  rw [hs,smul_neg,smul_neg]

theorem physicalNewtonForce_hasFDerivAt (m : ℝ) (source target : Plane)
    (hsep : source ≠ target) :
    HasFDerivAt (physicalNewtonForce m source)
      ((-m) • newtonTargetDerivative source target) target := by
  have hd := (newtonTargetField_hasFDerivAt source target hsep).const_smul (-m)
  convert! hd using 1
  funext p
  rw [physicalNewtonForce_eq_neg_legacy,neg_smul]
  rfl

/-- The sharp derivative bound keeps the manuscript's constants unchanged. -/
theorem newtonTargetDerivative_operator_norm_bound_sharp (source target : Plane)
    (hsep : source ≠ target) :
    ‖newtonTargetDerivative source target‖ ≤ 2 / ‖source-target‖^3 := by
  let d := source-target
  let R := ‖source-target‖
  have hR : 0 < R := norm_pos_iff.mpr (sub_ne_zero.mpr hsep)
  have hR0 : R ≠ 0 := ne_of_gt hR
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  let B := (3/R^2*inner ℝ d v) • d-v
  have hsq : ‖B‖^2 = ‖v‖^2+(3/R^2)*(inner ℝ d v)^2 := by
    dsimp only [B]
    rw [norm_sub_sq_real,norm_smul,real_inner_smul_left,Real.norm_eq_abs]
    rw [mul_pow,sq_abs]
    change (3/R^2*inner ℝ d v)^2*R^2-
      2*(3/R^2*inner ℝ d v*inner ℝ d v)+‖v‖^2 = _
    field_simp [hR0]
    ring
  have hi : |inner ℝ d v| ≤ R*‖v‖ := abs_real_inner_le_norm d v
  have hisq : (inner ℝ d v)^2 ≤ (R*‖v‖)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hi
  have hmul := mul_le_mul_of_nonneg_left hisq (by positivity : 0 ≤ 3/R^2)
  have hfactor : (3/R^2)*(R*‖v‖)^2=3*‖v‖^2 := by
    field_simp [hR0]
  rw [hfactor] at hmul
  have hB : ‖B‖ ≤ 2*‖v‖ := by
    apply (sq_le_sq₀ (norm_nonneg B) (by positivity)).mp
    nlinarith [hsq,hmul]
  have hA : newtonTargetDerivative source target v = (R^3)⁻¹ • B := by
    rw [newtonTargetDerivative_apply]
    dsimp only [B]
    conv_rhs => rw [smul_sub,smul_smul]
    change (3/R^5*inner ℝ d v) • d-(R^3)⁻¹ • v =
      ((R^3)⁻¹*(3/R^2*inner ℝ d v)) • d-(R^3)⁻¹ • v
    congr 1
    congr 1
    field_simp [hR0]
  rw [hA,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (pow_pos hR 3))]
  calc
    (R^3)⁻¹*‖B‖ ≤ (R^3)⁻¹*(2*‖v‖) :=
      mul_le_mul_of_nonneg_left hB (inv_nonneg.mpr (pow_nonneg hR.le 3))
    _=(2/‖source-target‖^3)*‖v‖ := by change _=(2/R^3)*‖v‖; ring

theorem physicalNewtonForce_fderiv_norm_bound (m : ℝ) (source target : Plane)
    (hsep : source ≠ target) :
    ‖fderiv ℝ (physicalNewtonForce m source) target‖ ≤
      |m| * (2 / dist target source ^ 3) := by
  rw [(physicalNewtonForce_hasFDerivAt m source target hsep).fderiv,
    norm_smul,Real.norm_eq_abs,abs_neg,dist_eq_norm,norm_sub_rev target source]
  exact mul_le_mul_of_nonneg_left
    (newtonTargetDerivative_operator_norm_bound_sharp source target hsep) (abs_nonneg m)

def exteriorNewtonForce {ι : Type*} (S : Finset ι)
    (mass : ι → ℝ) (sources : ι → Plane) (target : Plane) : Plane :=
  ∑ j ∈ S, physicalNewtonForce (mass j) (sources j) target

theorem exteriorNewtonForce_hasFDerivAt {ι : Type*} (S : Finset ι)
    (mass : ι → ℝ) (sources : ι → Plane) (target : Plane)
    (hsep : ∀ j ∈ S, sources j ≠ target) :
    HasFDerivAt (exteriorNewtonForce S mass sources)
      (∑ j ∈ S, (-mass j) • newtonTargetDerivative (sources j) target) target := by
  unfold exteriorNewtonForce
  exact HasFDerivAt.fun_sum (fun j hj =>
    physicalNewtonForce_hasFDerivAt (mass j) (sources j) target (hsep j hj))

theorem exteriorNewtonForce_fderiv_norm_bound {ι : Type*} (S : Finset ι)
    (mass : ι → ℝ) (sources : ι → Plane) (target : Plane)
    (hm : ∀ j ∈ S, 0 ≤ mass j) (hsep : ∀ j ∈ S, sources j ≠ target) :
    ‖fderiv ℝ (exteriorNewtonForce S mass sources) target‖ ≤
      ∑ j ∈ S, mass j * (2 / dist target (sources j)^3) := by
  rw [(exteriorNewtonForce_hasFDerivAt S mass sources target hsep).fderiv]
  calc
    _ ≤ ∑ j ∈ S, ‖(-mass j) • newtonTargetDerivative (sources j) target‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ S, mass j * (2 / dist target (sources j)^3) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (hm j hj),
        dist_eq_norm,norm_sub_rev target (sources j)]
      exact mul_le_mul_of_nonneg_left
        (newtonTargetDerivative_operator_norm_bound_sharp _ _ (hsep j hj)) (hm j hj)

theorem exteriorNewtonForce_fderiv_norm_bound_separated {ι : Type*} (S : Finset ι)
    (mass : ι → ℝ) (sources : ι → Plane) (target : Plane) (δ : ℝ)
    (hm : ∀ j ∈ S, 0 ≤ mass j) (hδ : 0 < δ)
    (hseparation : ∀ j ∈ S, δ/2 ≤ dist target (sources j)) :
    ‖fderiv ℝ (exteriorNewtonForce S mass sources) target‖ ≤
      16 * (∑ j ∈ S, mass j) / δ^3 := by
  have hsep : ∀ j ∈ S, sources j ≠ target := by
    intro j hj
    have hd : 0 < dist target (sources j) := (half_pos hδ).trans_le (hseparation j hj)
    exact (dist_pos.mp hd).symm
  calc
    _ ≤ ∑ j ∈ S, mass j * (2 / dist target (sources j)^3) :=
      exteriorNewtonForce_fderiv_norm_bound S mass sources target hm hsep
    _ ≤ ∑ j ∈ S, mass j * (16/δ^3) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (hm j hj)
      have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
        (pow_pos (half_pos hδ) 3)
        (pow_le_pow_left₀ (half_pos hδ).le (hseparation j hj) 3)
      have he : 2/(δ/2)^3 = 16/δ^3 := by field_simp; ring
      simpa only [he] using h
    _ = 16 * (∑ j ∈ S, mass j) / δ^3 := by
      rw [← Finset.sum_mul]
      ring

theorem exteriorNewtonForce_sub_norm_bound_on_convex {ι : Type*} (S : Finset ι)
    (mass : ι → ℝ) (sources : ι → Plane) (U : Set Plane) (δ : ℝ)
    (hm : ∀ j ∈ S, 0 ≤ mass j) (hδ : 0 < δ) (hU : Convex ℝ U)
    (hseparation : ∀ p ∈ U, ∀ j ∈ S, δ/2 ≤ dist p (sources j))
    (p q : Plane) (hp : p ∈ U) (hq : q ∈ U) :
    ‖exteriorNewtonForce S mass sources p-exteriorNewtonForce S mass sources q‖ ≤
      (16 * (∑ j ∈ S, mass j) / δ^3) * ‖p-q‖ := by
  apply hU.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) _ _ hq hp
  · intro y hy
    apply (exteriorNewtonForce_hasFDerivAt S mass sources y _).differentiableAt
    intro j hj
    have hd : 0 < dist y (sources j) := (half_pos hδ).trans_le (hseparation y hy j hj)
    exact (dist_pos.mp hd).symm
  · intro y hy
    exact exteriorNewtonForce_fderiv_norm_bound_separated S mass sources y δ hm hδ
      (hseparation y hy)

end FourBody.Reuse

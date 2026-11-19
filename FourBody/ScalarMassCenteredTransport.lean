import FourBody.ScalarMassGeometry
import FourBody.ScalarGeometry
import FourBody.ScalarPairFormBridge
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
STATIC supplements S3-D01/D04/U02/T04/T05/U15. The image of the actual
mass-center kernel under z_i ↦ sqrt(μ_i) z_i is an actual Euclidean
submodule, with its inherited norm and inner product. The original scalar
space keeps its existing coordinate norm. Its literal L is conjugated by
a concrete continuous linear equivalence, and the genuine library adjoint
and positive-operator assertions are proved on the Euclidean image.

All finite n and all positive masses are retained, including n = 0, 1.
This file and its ScalarMassGeometry dependency await strict compilation.
No additional global norm or inner-product instance is installed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace
namespace FourBody.ScalarSupplement

open ScalarGeometry GeneralOperator

def massCenteredSpace {n : ℕ} (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i) :
    Submodule ℝ (ScalarMassGeometry.MassEuclidean n) :=
  (ScalarW μ).map (ScalarMassGeometry.massEuclideanEquivalence μ hμ).toLinearMap

def massCenteredLinearEquivalence {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) : ScalarW μ ≃ₗ[ℝ] massCenteredSpace μ hμ where
  toFun z := ⟨ScalarMassGeometry.massEuclideanEquivalence μ hμ z.val,
    Submodule.mem_map.mpr ⟨z.val, z.property, rfl⟩⟩
  invFun w := ⟨(ScalarMassGeometry.massEuclideanEquivalence μ hμ).symm w.val, by
    obtain ⟨z, hz, heq⟩ := Submodule.mem_map.mp w.property
    have hv : (ScalarMassGeometry.massEuclideanEquivalence μ hμ).symm w.val = z := by
      rw [← heq]
      exact (ScalarMassGeometry.massEuclideanEquivalence μ hμ).symm_apply_apply z
    rw [hv]
    exact hz⟩
  left_inv z := by
    apply Subtype.ext
    exact (ScalarMassGeometry.massEuclideanEquivalence μ hμ).symm_apply_apply z.val
  right_inv w := by
    apply Subtype.ext
    exact (ScalarMassGeometry.massEuclideanEquivalence μ hμ).apply_symm_apply w.val
  map_add' z w := by
    apply Subtype.ext
    exact (ScalarMassGeometry.massEuclideanEquivalence μ hμ).map_add z.val w.val
  map_smul' a z := by
    apply Subtype.ext
    exact (ScalarMassGeometry.massEuclideanEquivalence μ hμ).map_smul a z.val

def massCenteredEquivalence {n : ℕ} (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i) :
    ScalarW μ ≃L[ℝ] massCenteredSpace μ hμ :=
  (massCenteredLinearEquivalence μ hμ).toContinuousLinearEquiv

@[simp] theorem massCenteredEquivalence_coe {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (z : ScalarW μ) :
    (massCenteredEquivalence μ hμ z).val =
      ScalarMassGeometry.massEuclideanEquivalence μ hμ z.val := rfl

@[simp] theorem massCenteredEquivalence_apply {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (z : ScalarW μ) (i : Fin n) :
    (massCenteredEquivalence μ hμ z).val i = Real.sqrt (μ i) * z.val i := rfl

theorem massCentered_inner_formula {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (z w : ScalarW μ) :
    ⟪massCenteredEquivalence μ hμ z, massCenteredEquivalence μ hμ w⟫_ℝ =
      weightedPairing μ z.val w.val := by
  change ⟪ScalarMassGeometry.massEuclideanEquivalence μ hμ z.val,
    ScalarMassGeometry.massEuclideanEquivalence μ hμ w.val⟫_ℝ = _
  exact (ScalarMassGeometry.massInner_eq_euclidean μ hμ z.val w.val).symm

theorem massCentered_norm_sq {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (z : ScalarW μ) :
    ‖massCenteredEquivalence μ hμ z‖ ^ 2 = ∑ i, μ i * z.val i ^ 2 := by
  change ScalarMassGeometry.massNorm μ hμ z.val ^ 2 = _
  exact ScalarMassGeometry.massNorm_sq μ hμ z.val

theorem massCentered_norm_equivalent {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ScalarW μ,
      c * ‖z‖ ≤ ‖massCenteredEquivalence μ hμ z‖ ∧
        ‖massCenteredEquivalence μ hμ z‖ ≤ C * ‖z‖ := by
  obtain ⟨c, C, hc, hC, hbound⟩ := ScalarMassGeometry.massNorm_equivalent μ hμ
  exact ⟨c, C, hc, hC, fun z => hbound z.val⟩

/-- The normed Euclidean image is genuinely complete by finite dimension. -/
theorem massCentered_complete {n : ℕ} (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i) :
    CompleteSpace (massCenteredSpace μ hμ) := inferInstance

/-- The original coordinate topology is also complete, and the explicit
CLE identifies it with the mass Hilbert topology without changing instances. -/
theorem scalarCentered_complete {n : ℕ} (μ : Fin n → ℝ) :
    CompleteSpace (ScalarW μ) := inferInstance

def scalarCenteredLaplacianLM {n : ℕ} (μ : Fin n → ℝ)
    (c : Fin n → Fin n → ℝ) (hc : SymmetricCoefficients c) :
    ScalarW μ →ₗ[ℝ] ScalarW μ where
  toFun z := ⟨laplacian μ c z.val, by
    change (∑ i, μ i * laplacian μ c z.val i) = 0
    exact scalarCenter_laplacian μ c hc z.val⟩
  map_add' z w := by
    apply Subtype.ext
    exact (laplacian μ c).map_add z.val w.val
  map_smul' a z := by
    apply Subtype.ext
    exact (laplacian μ c).map_smul a z.val

def scalarCenteredLaplacianCLM {n : ℕ} (μ : Fin n → ℝ)
    (c : Fin n → Fin n → ℝ) (hc : SymmetricCoefficients c) :
    ScalarW μ →L[ℝ] ScalarW μ :=
  (scalarCenteredLaplacianLM μ c hc).toContinuousLinearMap

@[simp] theorem scalarCenteredLaplacianCLM_coe {n : ℕ} (μ : Fin n → ℝ)
    (c : Fin n → Fin n → ℝ) (hc : SymmetricCoefficients c) (z : ScalarW μ) :
    (scalarCenteredLaplacianCLM μ c hc z).val = laplacian μ c z.val := rfl

def conjugateCenteredLaplacian {n : ℕ} (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i)
    (c : Fin n → Fin n → ℝ) (hc : SymmetricCoefficients c) :
    massCenteredSpace μ hμ →L[ℝ] massCenteredSpace μ hμ :=
  (massCenteredEquivalence μ hμ).toContinuousLinearMap.comp
    ((scalarCenteredLaplacianCLM μ c hc).comp
      (massCenteredEquivalence μ hμ).symm.toContinuousLinearMap)

theorem conjugateCenteredLaplacian_apply_equivalence {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (c : Fin n → Fin n → ℝ)
    (hc : SymmetricCoefficients c) (z : ScalarW μ) :
    conjugateCenteredLaplacian μ hμ c hc (massCenteredEquivalence μ hμ z) =
      massCenteredEquivalence μ hμ (scalarCenteredLaplacianCLM μ c hc z) := by
  change massCenteredEquivalence μ hμ (scalarCenteredLaplacianCLM μ c hc
    ((massCenteredEquivalence μ hμ).symm (massCenteredEquivalence μ hμ z))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem conjugateCenteredLaplacian_inner_formula {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (c : Fin n → Fin n → ℝ)
    (hc : SymmetricCoefficients c) (z w : ScalarW μ) :
    ⟪conjugateCenteredLaplacian μ hμ c hc (massCenteredEquivalence μ hμ z),
      massCenteredEquivalence μ hμ w⟫_ℝ =
      weightedPairing μ (laplacian μ c z.val) w.val := by
  rw [conjugateCenteredLaplacian_apply_equivalence, massCentered_inner_formula]
  rfl

theorem conjugateCenteredLaplacian_isSymmetric {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (c : Fin n → Fin n → ℝ)
    (hc : SymmetricCoefficients c) :
    (conjugateCenteredLaplacian μ hμ c hc).IsSymmetric := by
  intro x y
  obtain ⟨z, rfl⟩ := (massCenteredEquivalence μ hμ).surjective x
  obtain ⟨w, rfl⟩ := (massCenteredEquivalence μ hμ).surjective y
  change inner ℝ
    (conjugateCenteredLaplacian μ hμ c hc (massCenteredEquivalence μ hμ z))
    (massCenteredEquivalence μ hμ w) =
      inner ℝ (massCenteredEquivalence μ hμ z)
        (conjugateCenteredLaplacian μ hμ c hc (massCenteredEquivalence μ hμ w))
  rw [conjugateCenteredLaplacian_inner_formula,
    conjugateCenteredLaplacian_apply_equivalence, massCentered_inner_formula]
  exact (laplacian_selfAdjoint μ c hc z.val w.val).symm

theorem conjugateCenteredLaplacian_adjoint_eq {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (c : Fin n → Fin n → ℝ)
    (hc : SymmetricCoefficients c) :
    (conjugateCenteredLaplacian μ hμ c hc).adjoint =
      conjugateCenteredLaplacian μ hμ c hc :=
  (conjugateCenteredLaplacian_isSymmetric μ hμ c hc).clm_adjoint_eq

theorem scalarCenteredLaplacian_pos {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (c : Fin n → Fin n → ℝ)
    (hc : SymmetricCoefficients c) (hp : PositiveOffDiagonal c)
    (z : ScalarW μ) (hz : z ≠ 0) :
    0 < weightedPairing μ z.val (scalarCenteredLaplacianCLM μ c hc z).val := by
  let t : centeredSpace μ := ⟨z.val, z.property⟩
  have ht : t ≠ 0 := by
    intro h
    apply hz
    apply Subtype.ext
    exact congrArg Subtype.val h
  exact centeredLaplacian_pos μ hμ c hc hp t ht

theorem conjugateCenteredLaplacian_quadratic_pos {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (c : Fin n → Fin n → ℝ)
    (hc : SymmetricCoefficients c) (hp : PositiveOffDiagonal c)
    (x : massCenteredSpace μ hμ) (hx : x ≠ 0) :
    0 < ⟪conjugateCenteredLaplacian μ hμ c hc x, x⟫_ℝ := by
  obtain ⟨z, rfl⟩ := (massCenteredEquivalence μ hμ).surjective x
  have hz : z ≠ 0 := by
    intro h
    apply hx
    rw [h, map_zero]
  rw [conjugateCenteredLaplacian_inner_formula, weightedPairing_symm]
  exact scalarCenteredLaplacian_pos μ hμ c hc hp z hz

theorem conjugateCenteredLaplacian_isPositive {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (c : Fin n → Fin n → ℝ)
    (hc : SymmetricCoefficients c) (hp : PositiveOffDiagonal c) :
    (conjugateCenteredLaplacian μ hμ c hc).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff _).mpr
  refine ⟨conjugateCenteredLaplacian_isSymmetric μ hμ c hc, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp only [hx, map_zero, inner_zero_left, le_refl]
  · exact (conjugateCenteredLaplacian_quadratic_pos μ hμ c hc hp x hx).le

theorem conjugateCenteredLaplacian_isSelfAdjoint {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (c : Fin n → Fin n → ℝ)
    (hc : SymmetricCoefficients c) (hp : PositiveOffDiagonal c) :
    IsSelfAdjoint (conjugateCenteredLaplacian μ hμ c hc) :=
  (conjugateCenteredLaplacian_isPositive μ hμ c hc hp).isSelfAdjoint

/-- Literal inverse-cube L from the source, with collision freedom supplying
positive off-diagonal coefficients rather than an input positivity certificate. -/
theorem conjugateInverseCubeL_isPositive {n : ℕ} (μ z : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (hz : Function.Injective z) :
    (conjugateCenteredLaplacian μ hμ (inverseCubeCoefficient z)
      (inverseCubeCoefficient_symmetric z)).IsPositive :=
  conjugateCenteredLaplacian_isPositive μ hμ _ _
    (inverseCubeCoefficient_positive z hz)

theorem conjugateInverseCubeL_quadratic_pos {n : ℕ} (μ z : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (hz : Function.Injective z)
    (x : massCenteredSpace μ hμ) (hx : x ≠ 0) :
    0 < ⟪conjugateCenteredLaplacian μ hμ (inverseCubeCoefficient z)
      (inverseCubeCoefficient_symmetric z) x, x⟫_ℝ :=
  conjugateCenteredLaplacian_quadratic_pos μ hμ _ _
    (inverseCubeCoefficient_positive z hz) x hx

end FourBody.ScalarSupplement

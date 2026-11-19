import FourBody.ScalarPotentialOperatorBridge
import FourBody.ScalarPotentialConstraint
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
The actual Jacobian of z - scalarForce(mu,z), in the increasing chamber.
This closes the calculus-to-operator representation bridge for Id + 2L.
It proves a derivative; neither a branch nor a seed is assumed.
Staged source only, awaiting the parent's serial compiler verification.
-/

noncomputable section
open scoped BigOperators
open Set Filter Topology

namespace FourBody.ScalarMinimizer

def normalizedScalarResidual {n : ℕ} (μ z : ScalarVector n) : ScalarVector n :=
  fun i => z i - FourBody.ScalarGeometry.scalarForce μ z i

def normalizedScalarResidualDerivative {n : ℕ} (μ z : ScalarVector n) :
    ScalarVector n →L[ℝ] ScalarVector n :=
  ContinuousLinearMap.id ℝ (ScalarVector n) + (2 : ℝ) •
    (FourBody.GeneralOperator.laplacian μ
      (FourBody.GeneralOperator.inverseCubeCoefficient z)).toContinuousLinearMap

theorem scalarPotentialHessian_symm {n : ℕ} (μ z h v : ScalarVector n)
    (hz : z ∈ ambientChamber n) :
    scalarPotentialHessian μ z h v = scalarPotentialHessian μ z v h := by
  rw [scalarPotentialHessian_apply μ z h v hz, scalarPotentialHessian_apply μ z v h hz]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · congr 1
    apply Finset.sum_congr rfl
    intro p _
    ring

theorem weightedPairing_single_left {n : ℕ} (μ v : ScalarVector n) (i : Fin n) :
    FourBody.GeneralOperator.weightedPairing μ (Pi.single i 1) v = μ i * v i := by
  unfold FourBody.GeneralOperator.weightedPairing
  simp_rw [scalarSingle_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem scalarPotentialHessian_single_right {n : ℕ} (μ z h : ScalarVector n)
    (hz : z ∈ ambientChamber n) (i : Fin n) :
    scalarPotentialHessian μ z h (Pi.single i 1) =
      μ i * normalizedScalarResidualDerivative μ z h i := by
  rw [scalarPotentialHessian_symm μ z h (Pi.single i 1) hz,
    scalarPotentialHessian_operator_representation μ z (Pi.single i 1) h hz,
    weightedPairing_single_left]
  rfl

theorem scalarPotentialDerivative_hasFDerivAt {n : ℕ} (μ z : ScalarVector n)
    (hz : z ∈ ambientChamber n) :
    HasFDerivAt (scalarPotentialDerivative μ) (scalarPotentialHessian μ z) z := by
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ ambientChamber n :=
    (ambientChamber_isOpen n).mem_nhds hz
  have heq : scalarPotentialDerivative μ =ᶠ[𝓝 z] orderedScalarPotentialDerivative μ :=
    hnear.mono (fun w hw => (orderedScalarPotentialDerivative_eq μ w hw).symm)
  exact (orderedScalarPotentialDerivative_hasFDerivAt μ z hz).congr_of_eventuallyEq heq

/-- Actual vector Frechet derivative, not merely positivity of a matrix
with a matching name. The source function is the original normalized force residual. -/
theorem normalizedScalarResidual_hasFDerivAt {n : ℕ} (μ z : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (hz : z ∈ ambientChamber n) :
    HasFDerivAt (normalizedScalarResidual μ) (normalizedScalarResidualDerivative μ z) z := by
  apply hasFDerivAt_pi''
  intro i
  have hd := (scalarPotentialDerivative_hasFDerivAt μ z hz).clm_apply
    (hasFDerivAt_const (Pi.single i 1 : ScalarVector n) z)
  have hd' : HasFDerivAt
      (fun w : ScalarVector n => scalarPotentialDerivative μ w (Pi.single i 1))
      ((scalarPotentialHessian μ z).flip (Pi.single i 1)) z := by
    simpa only [ContinuousLinearMap.comp_zero, add_zero, zero_add] using hd
  have hi := hd'.const_mul (μ i)⁻¹
  have heq : (fun w : ScalarVector n => (μ i)⁻¹ *
      scalarPotentialDerivative μ w (Pi.single i 1)) =
      (fun w : ScalarVector n => normalizedScalarResidual μ w i) := by
    funext w
    rw [scalarPotentialDerivative_single]
    unfold normalizedScalarResidual
    field_simp [(hμ i).ne']
  rw [heq] at hi
  apply hi.congr_fderiv
  ext h
  change (μ i)⁻¹ * scalarPotentialHessian μ z h (Pi.single i 1) =
    normalizedScalarResidualDerivative μ z h i
  rw [scalarPotentialHessian_single_right μ z h hz i]
  field_simp [(hμ i).ne']

theorem normalizedScalarResidual_fderiv {n : ℕ} (μ z : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (hz : z ∈ ambientChamber n) :
    fderiv ℝ (normalizedScalarResidual μ) z = normalizedScalarResidualDerivative μ z :=
  (normalizedScalarResidual_hasFDerivAt μ z hμ hz).fderiv

theorem normalizedScalarResidual_root_iff {n : ℕ} (μ z : ScalarVector n) :
    normalizedScalarResidual μ z = 0 ↔
      ∀ i, FourBody.ScalarGeometry.scalarForce μ z i = z i := by
  constructor
  · intro hz i
    have hi := congr_fun hz i
    change z i - FourBody.ScalarGeometry.scalarForce μ z i = 0 at hi
    exact (sub_eq_zero.mp hi).symm
  · intro hz
    funext i
    exact sub_eq_zero.mpr (hz i).symm

theorem scalarW_eq_general_centeredSpace {n : ℕ} (μ : ScalarVector n) :
    FourBody.ScalarGeometry.ScalarW μ = FourBody.GeneralOperator.centeredSpace μ := rfl

theorem scalarForce_eq_laplacian {n : ℕ} (μ z : ScalarVector n) :
    FourBody.ScalarGeometry.scalarForce μ z = FourBody.GeneralOperator.laplacian μ
      (FourBody.GeneralOperator.inverseCubeCoefficient z) z := by
  funext i
  rw [FourBody.GeneralOperator.laplacian_inverseCube_apply]
  rfl

/-- The actual residual maps the center-zero subspace into itself, including
points outside the collision-free chamber in Lean's total force definition. -/
theorem normalizedScalarResidual_centered {n : ℕ} (μ z : ScalarVector n)
    (hz : z ∈ FourBody.ScalarGeometry.ScalarW μ) :
    normalizedScalarResidual μ z ∈ FourBody.ScalarGeometry.ScalarW μ := by
  have hf : (∑ i, μ i * FourBody.ScalarGeometry.scalarForce μ z i) = 0 := by
    have h := FourBody.GeneralOperator.scalarCenter_laplacian μ
      (FourBody.GeneralOperator.inverseCubeCoefficient z)
      (FourBody.GeneralOperator.inverseCubeCoefficient_symmetric z) z
    rw [← scalarForce_eq_laplacian] at h
    exact h
  change (∑ i, μ i * z i) = 0 at hz
  change (∑ i, μ i * (z i - FourBody.ScalarGeometry.scalarForce μ z i)) = 0
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hz, hf, sub_self]

def centeredNormalizedScalarResidual {n : ℕ} (μ : ScalarVector n) :
    FourBody.ScalarGeometry.ScalarW μ → FourBody.ScalarGeometry.ScalarW μ :=
  fun z => ⟨normalizedScalarResidual μ z.val, normalizedScalarResidual_centered μ z.val z.property⟩

def centeredNormalizedScalarResidualDerivative {n : ℕ} (μ : ScalarVector n)
    (z : FourBody.ScalarGeometry.ScalarW μ) :
    FourBody.ScalarGeometry.ScalarW μ →L[ℝ] FourBody.ScalarGeometry.ScalarW μ :=
  FourBody.GeneralOperator.shiftedCenteredLaplacianCLM μ
    (FourBody.GeneralOperator.inverseCubeCoefficient z.val)
    (FourBody.GeneralOperator.inverseCubeCoefficient_symmetric z.val)

/-- The actual source and target are the manuscript's centered subspace.
The embedding theorem transfers the already proved ambient derivative back
to this subspace, after an explicit equality of the derivative maps. -/
theorem centeredNormalizedScalarResidual_hasFDerivAt {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (z : FourBody.ScalarGeometry.ScalarW μ)
    (hz : z ∈ FourBody.ScalarGeometry.chamber μ) :
    HasFDerivAt (centeredNormalizedScalarResidual μ)
      (centeredNormalizedScalarResidualDerivative μ z) z := by
  let S := FourBody.ScalarGeometry.ScalarW μ
  have hd := (normalizedScalarResidual_hasFDerivAt μ z.val hμ hz).comp z S.subtypeL.hasFDerivAt
  have he : (normalizedScalarResidualDerivative μ z.val).comp S.subtypeL =
      S.subtypeL.comp (centeredNormalizedScalarResidualDerivative μ z) := by
    ext h i
    rfl
  have hd' := hd.congr_fderiv he
  have hc : ContinuousAt (centeredNormalizedScalarResidual μ) z :=
    hd.continuousAt.codRestrict
      (fun w : FourBody.ScalarGeometry.ScalarW μ =>
        normalizedScalarResidual_centered μ w.val w.property)
  exact HasFDerivAt.of_comp_of_isEmbedding hc S.subtypeL.hasFDerivAt
    S.isEmbedding_subtypeL hd' (Filter.Eventually.of_forall (fun _ => rfl))

theorem centeredNormalizedScalarResidual_fderiv {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (z : FourBody.ScalarGeometry.ScalarW μ)
    (hz : z ∈ FourBody.ScalarGeometry.chamber μ) :
    fderiv ℝ (centeredNormalizedScalarResidual μ) z = centeredNormalizedScalarResidualDerivative μ z :=
  (centeredNormalizedScalarResidual_hasFDerivAt μ hμ z hz).fderiv

/-- Actual centered derivative invertibility, with its calculus and
representation proofs supplied by the preceding declarations. -/
theorem centeredNormalizedScalarResidual_fderiv_isInvertible {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (z : FourBody.ScalarGeometry.ScalarW μ)
    (hz : z ∈ FourBody.ScalarGeometry.chamber μ) :
    (fderiv ℝ (centeredNormalizedScalarResidual μ) z).IsInvertible := by
  rw [centeredNormalizedScalarResidual_fderiv μ hμ z hz]
  exact FourBody.GeneralOperator.inverseCube_shiftedCenteredLaplacian_isInvertible
    μ hμ z.val hz.injective

end FourBody.ScalarMinimizer

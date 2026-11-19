import FourBody.Operators
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Positivity

set_option autoImplicit false

/-!
The actual mass inner product of Lemma 3.1. The concrete diagonal map
z_i ↦ sqrt(μ_i) z_i identifies it with a genuine Euclidean inner product.
Its inverse is explicit and its norm is equivalent to the existing finite
coordinate norm. No new norm instance is installed on the old Pi space.

Initially prepared as a proof candidate. Actual build/audit status is
recorded in strict receipts; this module alone does not attest
whole-paper acceptance.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace FourBody.ScalarMassGeometry

abbrev ScalarVector (n : ℕ) := Fin n → ℝ
abbrev MassEuclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

def massEuclideanLinearEquivalence {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) : ScalarVector n ≃ₗ[ℝ] MassEuclidean n where
  toFun z := WithLp.toLp 2 (fun i => Real.sqrt (μ i) * z i)
  invFun w := fun i => w i / Real.sqrt (μ i)
  left_inv z := by
    funext i
    change Real.sqrt (μ i) * z i / Real.sqrt (μ i) = z i
    exact mul_div_cancel_left₀ (z i) (ne_of_gt (Real.sqrt_pos.mpr (hμ i)))
  right_inv w := by
    ext i
    change Real.sqrt (μ i) * (w i / Real.sqrt (μ i)) = w i
    exact mul_div_cancel₀ (w i) (ne_of_gt (Real.sqrt_pos.mpr (hμ i)))
  map_add' z w := by
    ext i
    change Real.sqrt (μ i) * (z i + w i) =
      Real.sqrt (μ i) * z i + Real.sqrt (μ i) * w i
    exact mul_add _ _ _
  map_smul' a z := by
    ext i
    change Real.sqrt (μ i) * (a * z i) = a * (Real.sqrt (μ i) * z i)
    ring

def massEuclideanEquivalence {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) : ScalarVector n ≃L[ℝ] MassEuclidean n :=
  (massEuclideanLinearEquivalence μ hμ).toContinuousLinearEquiv

@[simp] theorem massEuclideanEquivalence_apply {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (z : ScalarVector n) (i : Fin n) :
    massEuclideanEquivalence μ hμ z i = Real.sqrt (μ i) * z i := rfl

theorem massInner_eq_euclidean {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (z w : ScalarVector n) :
    GeneralOperator.weightedPairing μ z w =
      inner ℝ (massEuclideanEquivalence μ hμ z) (massEuclideanEquivalence μ hμ w) := by
  rw [PiLp.inner_apply]
  unfold GeneralOperator.weightedPairing
  apply Finset.sum_congr rfl
  intro i _
  simp only [massEuclideanEquivalence_apply, RCLike.inner_apply, RCLike.conj_to_real]
  have hsq := Real.sq_sqrt (hμ i).le
  calc
    μ i * z i * w i = (Real.sqrt (μ i)) ^ 2 * z i * w i := by rw [hsq]
    _ = _ := by ring

/-- An explicit genuine inner-product core, kept as a value. Installing its
norm as a second global instance on the existing Pi norm is unnecessary. -/
@[instance_reducible]
def massInnerCore {n : ℕ} (μ : ScalarVector n) (hμ : ∀ i, 0 < μ i) :
    InnerProductSpace.Core ℝ (ScalarVector n) where
  inner z w := inner ℝ (massEuclideanEquivalence μ hμ z) (massEuclideanEquivalence μ hμ w)
  conj_inner_symm z w := by simp only [inner_conj_symm]
  re_inner_nonneg z := by
    simpa only [RCLike.re_to_real] using
      (real_inner_self_nonneg (x := massEuclideanEquivalence μ hμ z))
  add_left z w t := by simp only [map_add, inner_add_left]
  smul_left z w a := by simp only [map_smul, inner_smul_left]
  definite z hz := by
    apply (massEuclideanEquivalence μ hμ).injective
    rw [map_zero]
    exact inner_self_eq_zero.mp hz

theorem massInnerCore_formula {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (z w : ScalarVector n) :
    (massInnerCore μ hμ).inner z w = ∑ i, μ i * z i * w i :=
  (massInner_eq_euclidean μ hμ z w).symm

def massNorm {n : ℕ} (μ : ScalarVector n) (hμ : ∀ i, 0 < μ i)
    (z : ScalarVector n) : ℝ := ‖massEuclideanEquivalence μ hμ z‖

theorem massNorm_sq {n : ℕ} (μ : ScalarVector n) (hμ : ∀ i, 0 < μ i)
    (z : ScalarVector n) : massNorm μ hμ z ^ 2 = ∑ i, μ i * z i ^ 2 := by
  rw [massNorm, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [massEuclideanEquivalence_apply, mul_pow, Real.sq_sqrt (hμ i).le]

/-- The actual mass norm and the existing coordinate norm have one pair
of positive constants for each fixed finite positive mass vector, even
for Fin 0. This introduces no mass-independent bound or extra hypothesis. -/
theorem massNorm_equivalent {n : ℕ} (μ : ScalarVector n) (hμ : ∀ i, 0 < μ i) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ z : ScalarVector n, c * ‖z‖ ≤ massNorm μ hμ z ∧ massNorm μ hμ z ≤ C * ‖z‖ := by
  let e := massEuclideanEquivalence μ hμ
  let b : ℝ := ‖e.symm.toContinuousLinearMap‖ + 1
  let C : ℝ := ‖e.toContinuousLinearMap‖ + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨b⁻¹, C, inv_pos.mpr hb, hC, ?_⟩
  intro z
  have hl := e.symm.toContinuousLinearMap.le_opNorm (e z)
  have hu := e.toContinuousLinearMap.le_opNorm z
  have hnorm : 0 ≤ ‖e z‖ := norm_nonneg _
  have hz : 0 ≤ ‖z‖ := norm_nonneg _
  have hl' : ‖z‖ ≤ b * ‖e z‖ := by
    change ‖e.symm (e z)‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e z‖ at hl
    rw [e.symm_apply_apply] at hl
    dsimp [b]
    nlinarith only [hl, hnorm]
  constructor
  · change b⁻¹ * ‖z‖ ≤ ‖e z‖
    have hdiv : ‖z‖ / b ≤ ‖e z‖ := (div_le_iff₀ hb).mpr (by simpa [mul_comm] using hl')
    simpa only [div_eq_mul_inv, mul_comm] using hdiv
  · change ‖e z‖ ≤ C * ‖z‖
    change ‖e z‖ ≤ ‖e.toContinuousLinearMap‖ * ‖z‖ at hu
    dsimp [C]
    nlinarith only [hu, hz]

end FourBody.ScalarMassGeometry

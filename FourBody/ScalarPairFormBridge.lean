import FourBody.ScalarPotentialOperatorBridge

/-!
STATIC source supplement S3-U16. This is an equality with the actual
Reuse.pairForm, including its ordered-pair convention and reversed square.
It instantiates the original inverse-cube coefficients and proves the
zero-pairing implication before using the positive-pair-form lemma.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace FourBody.ScalarSupplement

open ScalarMinimizer GeneralOperator

theorem weightedPairing_laplacian_eq_pairForm {n : ℕ} (μ h : ScalarVector n)
    (c : Fin n → Fin n → ℝ) (hc : SymmetricCoefficients c) :
    weightedPairing μ h (laplacian μ c h) =
      Reuse.pairForm (fun i j => μ i * μ j * c i j) h := by
  rw [laplacian_pairing_eq_ordered_pairs μ h h c hc,
    scalarPairs_sum_eq_ordered_double]
  unfold Reuse.pairForm
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [hij, if_true]
    ring
  · simp only [hij, if_false]

theorem pairForm_zero_of_weightedPairing_zero {n : ℕ} (μ h : ScalarVector n)
    (c : Fin n → Fin n → ℝ) (hc : SymmetricCoefficients c)
    (hq : weightedPairing μ h (laplacian μ c h) = 0) :
    Reuse.pairForm (fun i j => μ i * μ j * c i j) h = 0 :=
  (weightedPairing_laplacian_eq_pairForm μ h c hc).symm.trans hq

theorem inverseCube_pairForm_zero_of_weightedPairing_zero {n : ℕ}
    (μ z h : ScalarVector n)
    (hq : weightedPairing μ h (laplacian μ (inverseCubeCoefficient z) h) = 0) :
    Reuse.pairForm (fun i j => μ i * μ j * (|z i - z j| ^ 3)⁻¹) h = 0 :=
  pairForm_zero_of_weightedPairing_zero μ h (inverseCubeCoefficient z)
    (inverseCubeCoefficient_symmetric z) hq

theorem constant_of_inverseCube_weightedPairing_zero {n : ℕ}
    (μ z h : ScalarVector n) (hμ : ∀ i, 0 < μ i) (hz : Function.Injective z)
    (hq : weightedPairing μ h (laplacian μ (inverseCubeCoefficient z) h) = 0) :
    ∀ i j, h i = h j := by
  have hzero := inverseCube_pairForm_zero_of_weightedPairing_zero μ z h hq
  apply (Reuse.pairForm_eq_zero_iff_constant _ h ?_).mp hzero
  intro i j hij
  exact mul_pos (mul_pos (hμ i) (hμ j))
    (inverseCubeCoefficient_positive z hz i j (ne_of_lt hij))

end FourBody.ScalarSupplement

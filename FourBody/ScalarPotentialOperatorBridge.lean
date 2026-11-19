import FourBody.ScalarPotentialHessian
import FourBody.Operators

/-!
Exact ordered-pair identity for L and its bridge to the actual Hessian.
The L pairing has coefficient one per pair; D²Phi has coefficient two.
This separates a genuine derivative representation from the independently
proved invertibility of an abstractly specified operator.
Staged source, awaiting serial compilation and full type/trust audit.
-/

noncomputable section
open scoped BigOperators

namespace FourBody.ScalarMinimizer

theorem scalarPairs_sum_eq_ordered_double {n : ℕ} (f : Fin n × Fin n → ℝ) :
    (∑ p ∈ scalarPairs n, f p) = ∑ i, ∑ j, if i < j then f (i, j) else 0 := by
  rw [Finset.sum_finset_product (scalarPairs n) Finset.univ
    (fun i : Fin n => Finset.univ.filter (fun j => i < j))
    (by intro p; simp [scalarPairs])]
  simp only [Finset.sum_filter]

/-- Generic finite symmetrization, with the diagonal explicitly zero. -/
theorem scalar_symmetric_double_sum {n : ℕ} (f : Fin n × Fin n → ℝ)
    (hsym : ∀ i j, f (i, j) = f (j, i)) (hdiag : ∀ i, f (i, i) = 0) :
    (∑ i, ∑ j, f (i, j)) = 2 * ∑ p ∈ scalarPairs n, f p := by
  have hpoint (i j : Fin n) : f (i, j) =
      (if i < j then f (i, j) else 0) + (if j < i then f (i, j) else 0) := by
    rcases lt_trichotomy i j with hij | hij | hji
    · simp [hij, not_lt_of_ge hij.le]
    · subst j
      simp [hdiag]
    · simp [hji, not_lt_of_ge hji.le]
  have hswap : (∑ i, ∑ j, if j < i then f (i, j) else 0) =
      ∑ i, ∑ j, if i < j then f (i, j) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i < j
    · simp only [hij, if_true]
      exact hsym j i
    · simp only [hij, if_false]
  calc
    _ = ∑ i, ∑ j,
        ((if i < j then f (i, j) else 0) + (if j < i then f (i, j) else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hpoint i j
    _ = (∑ i, ∑ j, if i < j then f (i, j) else 0) +
        (∑ i, ∑ j, if j < i then f (i, j) else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = 2 * (∑ i, ∑ j, if i < j then f (i, j) else 0) := by rw [hswap]; ring
    _ = _ := by rw [← scalarPairs_sum_eq_ordered_double]

/-- The exact Lemma 3.1 L pairing, each unordered pair appearing once. -/
theorem laplacian_pairing_eq_ordered_pairs {n : ℕ} (μ h v : ScalarVector n)
    (c : Fin n → Fin n → ℝ) (hc : FourBody.GeneralOperator.SymmetricCoefficients c) :
    FourBody.GeneralOperator.weightedPairing μ h (FourBody.GeneralOperator.laplacian μ c v) =
      ∑ p ∈ scalarPairs n,
        μ p.1 * μ p.2 * c p.1 p.2 * (h p.1 - h p.2) * (v p.1 - v p.2) := by
  let f : Fin n × Fin n → ℝ := fun p =>
    μ p.1 * μ p.2 * c p.1 p.2 * (h p.1 - h p.2) * (v p.1 - v p.2)
  have hsym : ∀ i j, f (i, j) = f (j, i) := by
    intro i j
    dsimp [f]
    rw [hc j i]
    ring
  have hdiag : ∀ i, f (i, i) = 0 := by intro i; simp [f]
  have hdouble := scalar_symmetric_double_sum f hsym hdiag
  have hpair := FourBody.GeneralOperator.twice_pairing_laplacian μ c hc h v
  change (∑ i, ∑ j, μ i * μ j * c i j * (h i - h j) * (v i - v j)) =
    2 * ∑ p ∈ scalarPairs n,
      μ p.1 * μ p.2 * c p.1 p.2 * (h p.1 - h p.2) * (v p.1 - v p.2) at hdouble
  linarith

theorem inverseCube_pairing_eq_ordered_pairs {n : ℕ} (μ z h v : ScalarVector n) :
    FourBody.GeneralOperator.weightedPairing μ h
      (FourBody.GeneralOperator.laplacian μ (FourBody.GeneralOperator.inverseCubeCoefficient z) v) =
      ∑ p ∈ scalarPairs n,
        μ p.1 * μ p.2 * (h p.1 - h p.2) * (v p.1 - v p.2) / |z p.1 - z p.2| ^ 3 := by
  rw [laplacian_pairing_eq_ordered_pairs μ h v _
    (FourBody.GeneralOperator.inverseCubeCoefficient_symmetric z)]
  apply Finset.sum_congr rfl
  intro p _
  simp only [FourBody.GeneralOperator.inverseCubeCoefficient, div_eq_mul_inv]
  ring

/-- The displayed actual Hessian is the mass pairing with Id + 2L. -/
theorem scalarPotentialHessian_operator_representation {n : ℕ} (μ z h v : ScalarVector n)
    (hz : z ∈ ambientChamber n) :
    scalarPotentialHessian μ z h v =
      FourBody.GeneralOperator.weightedPairing μ h
        (v + (2 : ℝ) • FourBody.GeneralOperator.laplacian μ
          (FourBody.GeneralOperator.inverseCubeCoefficient z) v) := by
  rw [FourBody.GeneralOperator.weightedPairing_add_right,
    FourBody.GeneralOperator.weightedPairing_smul_right,
    inverseCube_pairing_eq_ordered_pairs, scalarPotentialHessian_apply μ z h v hz]
  rfl

theorem scalarPotential_second_operator_representation {n : ℕ} (μ z h v : ScalarVector n)
    (hz : z ∈ ambientChamber n) :
    fderiv ℝ (fun w : ScalarVector n => fderiv ℝ (scalarPotential μ) w) z h v =
      FourBody.GeneralOperator.weightedPairing μ h
        (v + (2 : ℝ) • FourBody.GeneralOperator.laplacian μ
          (FourBody.GeneralOperator.inverseCubeCoefficient z) v) := by
  rw [(scalarPotential_second_hasFDerivAt μ z hz).fderiv]
  exact scalarPotentialHessian_operator_representation μ z h v hz

end FourBody.ScalarMinimizer

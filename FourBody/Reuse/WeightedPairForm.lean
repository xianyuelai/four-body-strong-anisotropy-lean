import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! Extracted from DominantFiveBody/WeightedHessian.lean.
The generic pair-form declarations and proof bodies are unchanged.
Only namespace and imports differ. No cycle-comparison hypothesis is imported.
Applicable to every n, including n=0 and n=1.
-/
noncomputable section
open scoped BigOperators
namespace FourBody.Reuse

def pairForm {n : ℕ} (weight : Fin n → Fin n → ℝ) (u : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then weight i j * (u j - u i) ^ 2 else 0

def weightedAngleForm {n : ℕ} (mass : Fin n → ℝ)
    (coefficient : Fin n → Fin n → ℝ) (u : Fin n → ℝ) : ℝ :=
  pairForm (fun i j => mass i * mass j * coefficient i j) u

theorem pairForm_nonneg {n : ℕ} (weight : Fin n → Fin n → ℝ) (u : Fin n → ℝ)
    (hweight : ∀ i j, i < j → 0 ≤ weight i j) : 0 ≤ pairForm weight u := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs with hij
  · exact mul_nonneg (hweight i j hij) (sq_nonneg _)
  · exact le_rfl

/-- A nonpositive energy with every pair weighted positively forces a
constant vector. This is the precise sum-of-squares argument at the end of
the proof of manuscript Lemma `lem:cycle`. -/
theorem constant_of_pairForm_nonpos {n : ℕ}
    (weight : Fin n → Fin n → ℝ) (u : Fin n → ℝ)
    (hweight : ∀ i j, i < j → 0 < weight i j)
    (hQ : pairForm weight u ≤ 0) : ∀ i j, u i = u j := by
  have hterm : ∀ i j, 0 ≤ if i < j then weight i j * (u j - u i) ^ 2 else 0 := by
    intro i j
    split_ifs with hij
    · exact mul_nonneg (le_of_lt (hweight i j hij)) (sq_nonneg _)
    · exact le_rfl
  have hlt : ∀ i j, i < j → u i = u j := by
    intro i j hij
    have hrow : (∑ j : Fin n, if i < j then weight i j * (u j - u i) ^ 2 else 0)
        ≤ pairForm weight u :=
      Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hterm k l))
        (Finset.mem_univ i)
    have hentry := Finset.single_le_sum (fun k _ => hterm i k) (Finset.mem_univ j)
    have hle : weight i j * (u j - u i) ^ 2 ≤ 0 := by
      have h := le_trans hentry (le_trans hrow hQ)
      simpa only [hij, if_true] using h
    have hsq : (u j - u i) ^ 2 ≤ 0 :=
      nonpos_of_mul_nonpos_right hle (hweight i j hij)
    nlinarith [sq_nonneg (u j - u i)]
  intro i j
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hlt i j hij
  · subst j; rfl
  · exact (hlt j i hij).symm

theorem pairForm_zero_of_constant {n : ℕ}
    (weight : Fin n → Fin n → ℝ) (u : Fin n → ℝ)
    (hu : ∀ i j, u i = u j) : pairForm weight u = 0 := by
  unfold pairForm
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rw [hu j i]
  simp

theorem pairForm_eq_zero_iff_constant {n : ℕ}
    (weight : Fin n → Fin n → ℝ) (u : Fin n → ℝ)
    (hweight : ∀ i j, i < j → 0 < weight i j) :
    pairForm weight u = 0 ↔ ∀ i j, u i = u j := by
  constructor
  · intro hQ
    exact constant_of_pairForm_nonpos weight u hweight (le_of_eq hQ)
  · exact pairForm_zero_of_constant weight u

theorem pairForm_pos_of_nonconstant {n : ℕ}
    (weight : Fin n → Fin n → ℝ) (u : Fin n → ℝ)
    (hweight : ∀ i j, i < j → 0 < weight i j)
    (hu : ¬ ∀ i j, u i = u j) : 0 < pairForm weight u := by
  by_contra hQ
  exact hu (constant_of_pairForm_nonpos weight u hweight (le_of_not_gt hQ))

theorem weightedAngleForm_pos_of_nonconstant {n : ℕ}
    (mass : Fin n → ℝ) (coefficient : Fin n → Fin n → ℝ) (u : Fin n → ℝ)
    (hmass : ∀ i, 0 < mass i)
    (hcoeff : ∀ i j, i < j → 0 < coefficient i j)
    (hu : ¬ ∀ i j, u i = u j) : 0 < weightedAngleForm mass coefficient u := by
  exact pairForm_pos_of_nonconstant _ u
    (fun i j hij => mul_pos (mul_pos (hmass i) (hmass j)) (hcoeff i j hij)) hu


end FourBody.Reuse

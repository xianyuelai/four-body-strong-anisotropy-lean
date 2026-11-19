import FourBody.Reuse.WeightedPairForm
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
The weighted operators in Lemma 3.1 and Proposition 4.1 of the frozen v2:
four_body_strong_anisotropy_pro_v2.tex, SHA256
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

This module proves operator properties for an explicitly given scalar
configuration. It does not assert existence or uniqueness of that configuration.
The finite label type can be `Fin n`, including the singleton and empty cases.
The formula `inverseCubeCoefficient` uses the manuscript's actual denominator.
All proof assumptions are explicitly displayed; no analytic theorem is postulated.
-/

noncomputable section

open scoped BigOperators

namespace FourBody.GeneralOperator

variable {ι : Type*} [Fintype ι] [instDecEq : DecidableEq ι]

omit [DecidableEq ι]

abbrev Coordinates (ι : Type*) := ι → ℝ

def PositiveMasses (m : Coordinates ι) : Prop := ∀ i, 0 < m i

def SymmetricCoefficients (c : ι → ι → ℝ) : Prop := ∀ i j, c i j = c j i

def PositiveOffDiagonal (c : ι → ι → ℝ) : Prop :=
  ∀ i j, i ≠ j → 0 < c i j

def scalarCenter (m : Coordinates ι) : Coordinates ι →ₗ[ℝ] ℝ where
  toFun h := ∑ i, m i * h i
  map_add' h t := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a h := by
    change (∑ i, m i * (a * h i)) = a * ∑ i, m i * h i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

@[simp] theorem scalarCenter_apply (m h : Coordinates ι) :
    scalarCenter m h = ∑ i, m i * h i := rfl

abbrev centeredSpace (m : Coordinates ι) : Submodule ℝ (Coordinates ι) :=
  (scalarCenter m).ker

theorem centeredSpace_eq_zero (m : Coordinates ι) (h : centeredSpace m) :
    scalarCenter m (h : Coordinates ι) = 0 := h.property

/-- The mass-weighted scalar inner product as an explicit finite sum. -/
def weightedPairing (m h t : Coordinates ι) : ℝ := ∑ i, m i * h i * t i

theorem weightedPairing_symm (m h t : Coordinates ι) :
    weightedPairing m h t = weightedPairing m t h := by
  unfold weightedPairing
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem weightedPairing_zero_right (m h : Coordinates ι) :
    weightedPairing m h 0 = 0 := by simp [weightedPairing]

theorem weightedPairing_add_right (m h t u : Coordinates ι) :
    weightedPairing m h (t + u) =
      weightedPairing m h t + weightedPairing m h u := by
  simp only [weightedPairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem weightedPairing_smul_right (m h t : Coordinates ι) (a : ℝ) :
    weightedPairing m h (a • t) = a * weightedPairing m h t := by
  unfold weightedPairing
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem weightedPairing_self_nonneg (m : Coordinates ι)
    (hm : PositiveMasses m) (h : Coordinates ι) :
    0 ≤ weightedPairing m h h := by
  unfold weightedPairing
  apply Finset.sum_nonneg
  intro i _
  nlinarith [mul_nonneg (hm i).le (sq_nonneg (h i))]

theorem weightedPairing_self_pos (m : Coordinates ι)
    (hm : PositiveMasses m) (h : Coordinates ι) (hne : h ≠ 0) :
    0 < weightedPairing m h h := by
  have hex : ∃ i, h i ≠ 0 := by
    by_contra hex
    push Not at hex
    apply hne
    funext i
    exact hex i
  obtain ⟨i, hi⟩ := hex
  unfold weightedPairing
  have hterms : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ m j * h j * h j := by
    intro j _
    nlinarith [mul_nonneg (hm j).le (sq_nonneg (h j))]
  apply (Finset.sum_pos_iff_of_nonneg hterms).2
  exact ⟨i, Finset.mem_univ i, by
    nlinarith [mul_pos (hm i) (sq_pos_of_ne_zero hi)]⟩

/-- The diagonal term vanishes, so this is the manuscript's `j ≠ i` sum. -/
def laplacian (m : Coordinates ι) (c : ι → ι → ℝ) :
    Coordinates ι →ₗ[ℝ] Coordinates ι where
  toFun h i := ∑ j, m j * c i j * (h i - h j)
  map_add' h t := by
    funext i
    change (∑ j, m j * c i j * ((h i + t i) - (h j + t j))) =
      (∑ j, m j * c i j * (h i - h j)) +
      ∑ j, m j * c i j * (t i - t j)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  map_smul' a h := by
    funext i
    change (∑ j, m j * c i j * (a * h i - a * h j)) =
      a * ∑ j, m j * c i j * (h i - h j)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

@[simp] theorem laplacian_apply (m : Coordinates ι) (c : ι → ι → ℝ)
    (h : Coordinates ι) (i : ι) :
    laplacian m c h i = ∑ j, m j * c i j * (h i - h j) := rfl

/-- Symmetrization of the finite double sum, with no choice of label order. -/
theorem twice_pairing_laplacian (m : Coordinates ι) (c : ι → ι → ℝ)
    (hc : SymmetricCoefficients c) (h t : Coordinates ι) :
    2 * weightedPairing m h (laplacian m c t) =
      ∑ i, ∑ j, m i * m j * c i j * (h i - h j) * (t i - t j) := by
  let X := ∑ i, ∑ j, m i * m j * c i j * h i * (t i - t j)
  let Y := ∑ i, ∑ j, m i * m j * c i j * h j * (t j - t i)
  have hX : weightedPairing m h (laplacian m c t) = X := by
    unfold weightedPairing laplacian X
    apply Finset.sum_congr rfl
    intro i _
    change m i * h i * (∑ j, m j * c i j * (t i - t j)) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hXY : X = Y := by
    unfold X Y
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hc j i]
    ring
  calc
    2 * weightedPairing m h (laplacian m c t) = X + X := by rw [hX]; ring
    _ = X + Y := by rw [hXY]
    _ = ∑ i, ∑ j,
        (m i * m j * c i j * h i * (t i - t j) +
          m i * m j * c i j * h j * (t j - t i)) := by
      simp only [X, Y, Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem twice_pairing_laplacian_self (m : Coordinates ι) (c : ι → ι → ℝ)
    (hc : SymmetricCoefficients c) (h : Coordinates ι) :
    2 * weightedPairing m h (laplacian m c h) =
      ∑ i, ∑ j, m i * m j * c i j * (h i - h j) ^ 2 := by
  simpa only [pow_two, mul_assoc] using twice_pairing_laplacian m c hc h h

/-- Self-adjointness with respect to the actual mass-weighted pairing. -/
theorem laplacian_selfAdjoint (m : Coordinates ι) (c : ι → ι → ℝ)
    (hc : SymmetricCoefficients c) (h t : Coordinates ι) :
    weightedPairing m h (laplacian m c t) =
      weightedPairing m (laplacian m c h) t := by
  have h₁ := twice_pairing_laplacian m c hc h t
  have h₂ := twice_pairing_laplacian m c hc t h
  have hsum : (∑ i, ∑ j, m i * m j * c i j * (h i - h j) * (t i - t j)) =
      ∑ i, ∑ j, m i * m j * c i j * (t i - t j) * (h i - h j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [← weightedPairing_symm m t (laplacian m c h)]
  linarith

theorem scalarCenter_laplacian (m : Coordinates ι) (c : ι → ι → ℝ)
    (hc : SymmetricCoefficients c) (h : Coordinates ι) :
    scalarCenter m (laplacian m c h) = 0 := by
  have hx := twice_pairing_laplacian m c hc (fun _ => 1) h
  simp only [sub_self, zero_mul, mul_zero, Finset.sum_const_zero] at hx
  have hy : weightedPairing m (fun _ => 1) (laplacian m c h) =
      scalarCenter m (laplacian m c h) := by
    simp [weightedPairing, scalarCenter]
  rw [hy] at hx
  linarith

def centeredLaplacian (m : Coordinates ι) (c : ι → ι → ℝ)
    (hc : SymmetricCoefficients c) : centeredSpace m →ₗ[ℝ] centeredSpace m where
  toFun h := ⟨laplacian m c h, scalarCenter_laplacian m c hc h⟩
  map_add' h t := by
    apply Subtype.ext
    exact (laplacian m c).map_add h t
  map_smul' a h := by
    apply Subtype.ext
    exact (laplacian m c).map_smul a h

@[simp] theorem centeredLaplacian_coe (m : Coordinates ι) (c : ι → ι → ℝ)
    (hc : SymmetricCoefficients c) (h : centeredSpace m) :
    (centeredLaplacian m c hc h : Coordinates ι) = laplacian m c h := rfl

theorem centeredLaplacian_selfAdjoint (m : Coordinates ι) (c : ι → ι → ℝ)
    (hc : SymmetricCoefficients c) (h t : centeredSpace m) :
    weightedPairing m h (centeredLaplacian m c hc t) =
      weightedPairing m (centeredLaplacian m c hc h) t :=
  laplacian_selfAdjoint m c hc h t

/-- A centered constant vector is zero; the proof also covers the empty label type. -/
theorem centered_constant_eq_zero (m : Coordinates ι) (hm : PositiveMasses m)
    (h : centeredSpace m)
    (hconst : ∀ i j, (h : Coordinates ι) i = (h : Coordinates ι) j) : h = 0 := by
  by_cases hι : Nonempty ι
  · obtain ⟨i₀⟩ := hι
    have hmass : 0 < ∑ i, m i :=
      Finset.sum_pos (fun i _ => hm i) ⟨i₀, Finset.mem_univ i₀⟩
    have hmul : (∑ i, m i) * (h : Coordinates ι) i₀ = 0 := by
      rw [Finset.sum_mul]
      calc
        (∑ i, m i * (h : Coordinates ι) i₀) = scalarCenter m h := by
          rw [scalarCenter_apply]
          apply Finset.sum_congr rfl
          intro i _
          rw [hconst i i₀]
        _ = 0 := centeredSpace_eq_zero m h
    have hzero : (h : Coordinates ι) i₀ = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hmass)
    apply Subtype.ext
    funext i
    exact (hconst i i₀).trans hzero
  · apply Subtype.ext
    funext i
    exact False.elim (hι ⟨i⟩)

theorem centered_nonzero_has_distinct_coordinates (m : Coordinates ι)
    (hm : PositiveMasses m) (h : centeredSpace m) (hne : h ≠ 0) :
    ∃ i j, (h : Coordinates ι) i ≠ (h : Coordinates ι) j := by
  by_contra hnot
  push Not at hnot
  exact hne (centered_constant_eq_zero m hm h hnot)

omit [Fintype ι] in
theorem pair_square_nonneg (m : Coordinates ι) (hm : PositiveMasses m)
    (c : ι → ι → ℝ) (hp : PositiveOffDiagonal c)
    (h : Coordinates ι) (i j : ι) :
    0 ≤ m i * m j * c i j * (h i - h j) ^ 2 := by
  classical
  by_cases hij : i = j
  · subst j
    simp
  · exact mul_nonneg (mul_pos (mul_pos (hm i) (hm j)) (hp i j hij)).le
      (sq_nonneg (h i - h j))

theorem centeredLaplacian_pos (m : Coordinates ι) (hm : PositiveMasses m)
    (c : ι → ι → ℝ) (hc : SymmetricCoefficients c)
    (hp : PositiveOffDiagonal c) (h : centeredSpace m) (hne : h ≠ 0) :
    0 < weightedPairing m h (centeredLaplacian m c hc h) := by
  obtain ⟨i, j, hij⟩ := centered_nonzero_has_distinct_coordinates m hm h hne
  have hindex : i ≠ j := by
    intro heq
    exact hij (congrArg (fun k => (h : Coordinates ι) k) heq)
  have hterm : 0 < m i * m j * c i j *
      ((h : Coordinates ι) i - (h : Coordinates ι) j) ^ 2 :=
    mul_pos (mul_pos (mul_pos (hm i) (hm j)) (hp i j hindex))
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hij))
  have hsum : 0 < ∑ a, ∑ b,
      m a * m b * c a b * ((h : Coordinates ι) a - (h : Coordinates ι) b) ^ 2 := by
    have hrows : ∀ a ∈ (Finset.univ : Finset ι),
        0 ≤ ∑ b, m a * m b * c a b *
          ((h : Coordinates ι) a - (h : Coordinates ι) b) ^ 2 := by
      intro a _
      apply Finset.sum_nonneg
      intro b _
      exact pair_square_nonneg m hm c hp h a b
    apply (Finset.sum_pos_iff_of_nonneg hrows).2
    refine ⟨i, Finset.mem_univ i, ?_⟩
    apply (Finset.sum_pos_iff_of_nonneg (fun b _ =>
      pair_square_nonneg m hm c hp h i b)).2
    exact ⟨j, Finset.mem_univ j, hterm⟩
  have hid := twice_pairing_laplacian_self m c hc (h : Coordinates ι)
  change 0 < weightedPairing m h (laplacian m c h)
  linarith

/-- The exact longitudinal block `Id + 2 L` of the manuscript. -/
def shiftedCenteredLaplacian (m : Coordinates ι) (c : ι → ι → ℝ)
    (hc : SymmetricCoefficients c) : centeredSpace m →ₗ[ℝ] centeredSpace m :=
  LinearMap.id + (2 : ℝ) • centeredLaplacian m c hc

@[simp] theorem shiftedCenteredLaplacian_apply (m : Coordinates ι)
    (c : ι → ι → ℝ) (hc : SymmetricCoefficients c) (h : centeredSpace m) :
    shiftedCenteredLaplacian m c hc h = h + (2 : ℝ) • centeredLaplacian m c hc h := rfl

theorem shiftedCenteredLaplacian_pos (m : Coordinates ι) (hm : PositiveMasses m)
    (c : ι → ι → ℝ) (hc : SymmetricCoefficients c)
    (hp : PositiveOffDiagonal c) (h : centeredSpace m) (hne : h ≠ 0) :
    0 < weightedPairing m h (shiftedCenteredLaplacian m c hc h) := by
  have h₁ := weightedPairing_self_nonneg m hm (h : Coordinates ι)
  have h₂ := centeredLaplacian_pos m hm c hc hp h hne
  change 0 < weightedPairing m h
    ((h : Coordinates ι) + (2 : ℝ) • (centeredLaplacian m c hc h : Coordinates ι))
  rw [weightedPairing_add_right, weightedPairing_smul_right]
  linarith

theorem injective_of_centered_pairing_pos (m : Coordinates ι)
    (A : centeredSpace m →ₗ[ℝ] centeredSpace m)
    (hpos : ∀ h : centeredSpace m, h ≠ 0 → 0 < weightedPairing m h (A h)) :
    Function.Injective A := by
  intro h t heq
  have hdiff : A (h - t) = 0 := by rw [map_sub, heq, sub_self]
  by_cases hzero : h - t = 0
  · exact sub_eq_zero.mp hzero
  · have hp := hpos (h - t) hzero
    rw [hdiff] at hp
    simp at hp

theorem centeredLaplacian_injective (m : Coordinates ι) (hm : PositiveMasses m)
    (c : ι → ι → ℝ) (hc : SymmetricCoefficients c)
    (hp : PositiveOffDiagonal c) : Function.Injective (centeredLaplacian m c hc) :=
  injective_of_centered_pairing_pos m _ (centeredLaplacian_pos m hm c hc hp)

theorem shiftedCenteredLaplacian_injective (m : Coordinates ι) (hm : PositiveMasses m)
    (c : ι → ι → ℝ) (hc : SymmetricCoefficients c)
    (hp : PositiveOffDiagonal c) : Function.Injective (shiftedCenteredLaplacian m c hc) :=
  injective_of_centered_pairing_pos m _ (shiftedCenteredLaplacian_pos m hm c hc hp)

theorem centeredLaplacian_bijective (m : Coordinates ι) (hm : PositiveMasses m)
    (c : ι → ι → ℝ) (hc : SymmetricCoefficients c) (hp : PositiveOffDiagonal c) :
    Function.Bijective (centeredLaplacian m c hc) := by
  have hinj := centeredLaplacian_injective m hm c hc hp
  exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩

theorem shiftedCenteredLaplacian_bijective (m : Coordinates ι) (hm : PositiveMasses m)
    (c : ι → ι → ℝ) (hc : SymmetricCoefficients c) (hp : PositiveOffDiagonal c) :
    Function.Bijective (shiftedCenteredLaplacian m c hc) := by
  have hinj := shiftedCenteredLaplacian_injective m hm c hc hp
  exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩

def centeredLaplacianCLM (m : Coordinates ι) (c : ι → ι → ℝ)
    (hc : SymmetricCoefficients c) : centeredSpace m →L[ℝ] centeredSpace m :=
  (centeredLaplacian m c hc).toContinuousLinearMap

def shiftedCenteredLaplacianCLM (m : Coordinates ι) (c : ι → ι → ℝ)
    (hc : SymmetricCoefficients c) : centeredSpace m →L[ℝ] centeredSpace m :=
  (shiftedCenteredLaplacian m c hc).toContinuousLinearMap

theorem centeredLaplacian_isInvertible (m : Coordinates ι) (hm : PositiveMasses m)
    (c : ι → ι → ℝ) (hc : SymmetricCoefficients c) (hp : PositiveOffDiagonal c) :
    (centeredLaplacianCLM m c hc).IsInvertible := by
  refine ⟨(LinearEquiv.ofBijective (centeredLaplacian m c hc)
    (centeredLaplacian_bijective m hm c hc hp)).toContinuousLinearEquiv, ?_⟩
  rfl

theorem shiftedCenteredLaplacian_isInvertible (m : Coordinates ι) (hm : PositiveMasses m)
    (c : ι → ι → ℝ) (hc : SymmetricCoefficients c) (hp : PositiveOffDiagonal c) :
    (shiftedCenteredLaplacianCLM m c hc).IsInvertible := by
  refine ⟨(LinearEquiv.ofBijective (shiftedCenteredLaplacian m c hc)
    (shiftedCenteredLaplacian_bijective m hm c hc hp)).toContinuousLinearEquiv, ?_⟩
  rfl

/-- The concrete coefficient from the ordered one-dimensional seed of Lemma 3.1. -/
def inverseCubeCoefficient (z : Coordinates ι) (i j : ι) : ℝ :=
  (|z i - z j| ^ 3)⁻¹

omit [Fintype ι] in
theorem inverseCubeCoefficient_symmetric (z : Coordinates ι) :
    SymmetricCoefficients (inverseCubeCoefficient z) := by
  intro i j
  simp only [inverseCubeCoefficient, abs_sub_comm]

omit [Fintype ι] in
theorem inverseCubeCoefficient_positive (z : Coordinates ι) (hz : Function.Injective z) :
    PositiveOffDiagonal (inverseCubeCoefficient z) := by
  intro i j hij
  apply inv_pos.mpr
  apply pow_pos
  apply abs_pos.mpr
  apply sub_ne_zero.mpr
  exact fun h => hij (hz h)

include instDecEq in
theorem laplacian_inverseCube_apply (m z h : Coordinates ι) (i : ι) :
    laplacian m (inverseCubeCoefficient z) h i =
      ∑ j ∈ Finset.univ.erase i, m j * (h i - h j) / |z i - z j| ^ 3 := by
  rw [laplacian_apply]
  have he : (∑ j ∈ Finset.univ.erase i,
      m j * inverseCubeCoefficient z i j * (h i - h j)) =
      ∑ j, m j * inverseCubeCoefficient z i j * (h i - h j) := by
    have he := Finset.sum_erase_add (Finset.univ : Finset ι)
      (fun j => m j * inverseCubeCoefficient z i j * (h i - h j))
      (Finset.mem_univ i)
    simp only [sub_self, mul_zero, add_zero] at he
    exact he
  rw [← he]
  apply Finset.sum_congr rfl
  intro j _
  simp only [inverseCubeCoefficient, div_eq_mul_inv]
  ring

theorem inverseCube_centeredLaplacian_isInvertible (m : Coordinates ι)
    (hm : PositiveMasses m) (z : Coordinates ι) (hz : Function.Injective z) :
    (centeredLaplacianCLM m (inverseCubeCoefficient z)
      (inverseCubeCoefficient_symmetric z)).IsInvertible :=
  centeredLaplacian_isInvertible m hm (inverseCubeCoefficient z)
    (inverseCubeCoefficient_symmetric z) (inverseCubeCoefficient_positive z hz)

theorem inverseCube_shiftedCenteredLaplacian_isInvertible (m : Coordinates ι)
    (hm : PositiveMasses m) (z : Coordinates ι) (hz : Function.Injective z) :
    (shiftedCenteredLaplacianCLM m (inverseCubeCoefficient z)
      (inverseCubeCoefficient_symmetric z)).IsInvertible :=
  shiftedCenteredLaplacian_isInvertible m hm (inverseCubeCoefficient z)
    (inverseCubeCoefficient_symmetric z) (inverseCubeCoefficient_positive z hz)

omit [Fintype ι]

/-- A direct bridge from the extracted old positive pair form to this paper's
actual inverse-cube operator. No coorbital theorem or equilibrium is assumed. -/
theorem ordered_pairForm_le_full_sum {n : ℕ} (m : Coordinates (Fin n))
    (hm : PositiveMasses m) (c : Fin n → Fin n → ℝ) (hp : PositiveOffDiagonal c)
    (h : Coordinates (Fin n)) :
    FourBody.Reuse.weightedAngleForm m c h ≤
      ∑ i, ∑ j, m i * m j * c i j * (h i - h j) ^ 2 := by
  unfold FourBody.Reuse.weightedAngleForm FourBody.Reuse.pairForm
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs with hij
  · apply le_of_eq
    ring
  · exact pair_square_nonneg m hm c hp h i j

/-- This `Fin n` proof deliberately invokes the old, verbatim-extracted
nonconstant positive-pair-form proof after proving the representation bridge.
It covers the same singleton convention as the generic operator theorem. -/
theorem fin_centeredLaplacian_pos_from_legacy {n : ℕ} (m : Coordinates (Fin n))
    (hm : PositiveMasses m) (c : Fin n → Fin n → ℝ) (hc : SymmetricCoefficients c)
    (hp : PositiveOffDiagonal c) (h : centeredSpace m) (hne : h ≠ 0) :
    0 < weightedPairing m h (centeredLaplacian m c hc h) := by
  have hnonconstant : ¬ ∀ i j,
      (h : Coordinates (Fin n)) i = (h : Coordinates (Fin n)) j := by
    intro hconstant
    exact hne (centered_constant_eq_zero m hm h hconstant)
  have hQ := FourBody.Reuse.weightedAngleForm_pos_of_nonconstant
    m c (h : Coordinates (Fin n)) hm (fun i j hij => hp i j (ne_of_lt hij))
    hnonconstant
  have hle := ordered_pairForm_le_full_sum m hm c hp (h : Coordinates (Fin n))
  have hid := twice_pairing_laplacian_self m c hc (h : Coordinates (Fin n))
  change 0 < weightedPairing m h (laplacian m c h)
  linarith

theorem fin_centeredLaplacian_isInvertible_from_legacy {n : ℕ}
    (m : Coordinates (Fin n)) (hm : PositiveMasses m)
    (c : Fin n → Fin n → ℝ) (hc : SymmetricCoefficients c)
    (hp : PositiveOffDiagonal c) : (centeredLaplacianCLM m c hc).IsInvertible := by
  have hinj := injective_of_centered_pairing_pos m (centeredLaplacian m c hc)
    (fin_centeredLaplacian_pos_from_legacy m hm c hc hp)
  have hbij : Function.Bijective (centeredLaplacian m c hc) :=
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩
  refine ⟨(LinearEquiv.ofBijective (centeredLaplacian m c hc) hbij).toContinuousLinearEquiv,
    ?_⟩
  rfl

theorem fin_inverseCube_centeredLaplacian_isInvertible_from_legacy {n : ℕ}
    (m : Coordinates (Fin n)) (hm : PositiveMasses m)
    (z : Coordinates (Fin n)) (hz : Function.Injective z) :
    (centeredLaplacianCLM m (inverseCubeCoefficient z)
      (inverseCubeCoefficient_symmetric z)).IsInvertible :=
  fin_centeredLaplacian_isInvertible_from_legacy m hm (inverseCubeCoefficient z)
    (inverseCubeCoefficient_symmetric z) (inverseCubeCoefficient_positive z hz)

theorem fin_shiftedCenteredLaplacian_isInvertible_from_legacy {n : ℕ}
    (m : Coordinates (Fin n)) (hm : PositiveMasses m)
    (c : Fin n → Fin n → ℝ) (hc : SymmetricCoefficients c)
    (hp : PositiveOffDiagonal c) : (shiftedCenteredLaplacianCLM m c hc).IsInvertible := by
  have hpos : ∀ h : centeredSpace m, h ≠ 0 →
      0 < weightedPairing m h (shiftedCenteredLaplacian m c hc h) := by
    intro h hne
    have h₁ := weightedPairing_self_nonneg m hm (h : Coordinates (Fin n))
    have h₂ := fin_centeredLaplacian_pos_from_legacy m hm c hc hp h hne
    change 0 < weightedPairing m h
      ((h : Coordinates (Fin n)) +
        (2 : ℝ) • (centeredLaplacian m c hc h : Coordinates (Fin n)))
    rw [weightedPairing_add_right, weightedPairing_smul_right]
    linarith
  have hinj := injective_of_centered_pairing_pos m (shiftedCenteredLaplacian m c hc) hpos
  have hbij : Function.Bijective (shiftedCenteredLaplacian m c hc) :=
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩
  refine ⟨(LinearEquiv.ofBijective (shiftedCenteredLaplacian m c hc) hbij)
    |>.toContinuousLinearEquiv, ?_⟩
  rfl

theorem fin_inverseCube_shiftedCenteredLaplacian_isInvertible_from_legacy {n : ℕ}
    (m : Coordinates (Fin n)) (hm : PositiveMasses m)
    (z : Coordinates (Fin n)) (hz : Function.Injective z) :
    (shiftedCenteredLaplacianCLM m (inverseCubeCoefficient z)
      (inverseCubeCoefficient_symmetric z)).IsInvertible :=
  fin_shiftedCenteredLaplacian_isInvertible_from_legacy m hm (inverseCubeCoefficient z)
    (inverseCubeCoefficient_symmetric z) (inverseCubeCoefficient_positive z hz)

end FourBody.GeneralOperator

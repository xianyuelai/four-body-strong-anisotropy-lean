import FourBody.Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
Actual mass-dependent constants of v2 Proposition 2.2. These are real
minimums and positive real cube roots. No solution-scale estimate is an
assumption of the positivity or exterior-smallness conclusions.
-/
noncomputable section
open scoped BigOperators
namespace FourBody.ScaleConstants

def minimumMass (m : Masses) : ℝ :=
  (Finset.univ.image m).min' (Finset.univ_nonempty.image m)

theorem minimumMass_le (m : Masses) (i : Label) : minimumMass m ≤ m i := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem minimumMass_pos (m : Masses) (hm : PositiveMasses m) : 0 < minimumMass m := by
  have h := Finset.min'_mem (Finset.univ.image m) (Finset.univ_nonempty.image m)
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  change m i = minimumMass m at hi
  rw [← hi]
  exact hm i

theorem minimumMass_le_total (m : Masses) (hm : PositiveMasses m) :
    minimumMass m ≤ totalMass m := by
  exact (minimumMass_le m 0).trans
    (Finset.single_le_sum (fun i _ => (hm i).le) (Finset.mem_univ (0 : Label)))

def T (m : Masses) : ℝ := (192 * totalMass m / minimumMass m) ^ (1 / (3 : ℝ))
def G (m : Masses) : ℝ := (1 + T m) ^ 2
def c₀ (m : Masses) : ℝ := (minimumMass m) ^ (1 / (3 : ℝ)) / G m
def c₁ (m : Masses) : ℝ := (minimumMass m / 2) ^ (1 / (3 : ℝ)) / G m
def C (m : Masses) : ℝ := 6 * (totalMass m) ^ (1 / (3 : ℝ))

theorem T_pos (m : Masses) (hm : PositiveMasses m) : 0 < T m := by
  apply Real.rpow_pos_of_pos
  exact div_pos (mul_pos (by norm_num) (totalMass_pos hm)) (minimumMass_pos m hm)

theorem T_cube (m : Masses) (hm : PositiveMasses m) :
    T m ^ 3 = 192 * totalMass m / minimumMass m := by
  unfold T
  have hp : 0 ≤ 192 * totalMass m / minimumMass m := by
    exact (div_pos (mul_pos (by norm_num) (totalMass_pos hm)) (minimumMass_pos m hm)).le
  simpa only [one_div, Nat.cast_ofNat] using
    Real.rpow_inv_natCast_pow hp (by norm_num : (3 : ℕ) ≠ 0)

theorem T_gt_two (m : Masses) (hm : PositiveMasses m) : 2 < T m := by
  have hmin := minimumMass_pos m hm
  have hM := minimumMass_le_total m hm
  have hcube := T_cube m hm
  have h192 : 192 ≤ 192 * totalMass m / minimumMass m :=
    (le_div_iff₀ hmin).mpr (by nlinarith)
  by_contra h
  have hT := le_of_not_gt h
  have hpow := pow_le_pow_left₀ (T_pos m hm).le hT 3
  norm_num at hpow
  linarith

theorem constants_positive (m : Masses) (hm : PositiveMasses m) :
    0 < G m ∧ 0 < c₀ m ∧ 0 < c₁ m ∧ 0 < C m := by
  have ht := T_pos m hm
  have hmin := minimumMass_pos m hm
  have hM := totalMass_pos hm
  have hg : 0 < G m := by unfold G; positivity
  refine ⟨hg, ?_, ?_, ?_⟩
  · exact div_pos (Real.rpow_pos_of_pos hmin _) hg
  · exact div_pos (Real.rpow_pos_of_pos (by positivity) _) hg
  · exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hM _)

/-- The exact source constant 192 leaves exterior error at most m₀/12. -/
theorem exterior_smallness (m : Masses) (hm : PositiveMasses m)
    {outside r : ℝ} (houtside : outside ≤ totalMass m)
    (hr : 0 < r) :
    (16 * outside / (T m * r) ^ 3) * r ^ 3 ≤ minimumMass m / 12 := by
  have hT := T_pos m hm
  have hmin := minimumMass_pos m hm
  have hM := totalMass_pos hm
  have he : (16 * outside / (T m * r) ^ 3) * r ^ 3 = 16 * outside / T m ^ 3 := by
    field_simp [ne_of_gt hr, ne_of_gt hT]
  rw [he, T_cube m hm]
  have he' : 16 * outside / (192 * totalMass m / minimumMass m) =
      (outside / totalMass m) * (minimumMass m / 12) := by
    field_simp [ne_of_gt hmin, ne_of_gt hM]
    ring
  rw [he']
  have hratio : outside / totalMass m ≤ 1 := (div_le_one hM).mpr houtside
  exact (mul_le_mul_of_nonneg_right hratio (by positivity)).trans_eq (one_mul _)

end FourBody.ScaleConstants

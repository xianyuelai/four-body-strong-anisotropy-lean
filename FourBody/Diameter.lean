import FourBody.Cuts
import FourBody.PointGap

/-!
Proof draft for the full v2 Lemma 2.1 coordinate-diameter statement,
including all positive anisotropy parameters, not only s ≥ 1.
Baseline TeX SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
The force equations, largest-gap partition and weighted cut bounds are
actual definitions/theorems from the imported proof modules. This file
does not take a diameter estimate or seed classification as an assumption.
Actual compilation status is retained in the separate logs and source hashes.
-/

noncomputable section
open scoped BigOperators

namespace FourBody

theorem coordinate_diameter_bound {m : Masses} (hm : PositiveMasses m)
    (q : Configuration) (k : Axis) {lam : ℝ} (hlam : 0 < lam)
    (hEq : ∀ i, force m q i k = lam * q i k) :
    coordinateDiameter (fun i => q i k) ≤ 3 * (totalMass m / lam) ^ (1 / (3 : ℝ)) := by
  by_cases hD : 0 < coordinateDiameter (fun i => q i k)
  · rcases coordinate_largest_gap_partition (fun i => q i k) hD with
      ⟨A, B, g, hA, hB, hBdef, _hdisj, _hunion, hg, hDg, hcross⟩
    have hB' : (cutComplement A).Nonempty := by
      simpa only [hBdef, cutComplement] using hB
    have hcross' : ∀ i ∈ A, ∀ j ∈ cutComplement A, g ≤ q j k - q i k := by
      simpa only [hBdef, cutComplement] using hcross
    have hcube := cut_gap_cube_bound hm q k hlam hEq hA hB' hg hcross'
    have hroot := gap_le_mass_cube_root hm hlam hg hcube
    exact hDg.trans (mul_le_mul_of_nonneg_left hroot (by norm_num))
  · have hDle : coordinateDiameter (fun i => q i k) ≤ 0 := le_of_not_gt hD
    have hroot : 0 ≤ (totalMass m / lam) ^ (1 / (3 : ℝ)) :=
      Real.rpow_nonneg (div_nonneg (totalMass_pos hm).le hlam.le) _
    nlinarith

/-- v2 Lemma 2.1 horizontal bound, with the original s > 0 quantifier. -/
theorem diameter_x {m : Masses} (hm : PositiveMasses m) {s : ℝ} (hs : 0 < s)
    {q : Configuration} (hq : IsSolution m s q) :
    coordinateDiameter (fun i => q i 0) ≤ 3 * (totalMass m / s) ^ (1 / (3 : ℝ)) := by
  apply coordinate_diameter_bound hm q 0 hs
  intro i
  have h := congrArg (fun p : Point => p 0) (hq.2 i)
  simpa only [anisotropy_x] using h

/-- v2 Lemma 2.1 vertical bound; applies to every solution for s > 0. -/
theorem diameter_y {m : Masses} (hm : PositiveMasses m) {s : ℝ} (_hs : 0 < s)
    {q : Configuration} (hq : IsSolution m s q) :
    coordinateDiameter (fun i => q i 1) ≤ 3 * (totalMass m) ^ (1 / (3 : ℝ)) := by
  have hEq : ∀ i, force m q i 1 = (1 : ℝ) * q i 1 := by
    intro i
    have h := congrArg (fun p : Point => p 1) (hq.2 i)
    simpa only [anisotropy_y, one_mul] using h
  simpa only [div_one] using
    coordinate_diameter_bound hm q 1 (show (0 : ℝ) < 1 by norm_num) hEq

theorem center_coordinate_zero {m : Masses} {q : Configuration}
    (hc : centerLM m q = 0) (k : Axis) : (∑ i, m i * q i k) = 0 := by
  have h := congrArg (coordinateLM k) hc
  change coordinateLM k (∑ i, m i • q i) = coordinateLM k 0 at h
  rw [map_sum, map_zero] at h
  exact h

/-- The coordinate origin lies between the actual extrema whenever all
masses are positive and their exact weighted center is zero. -/
theorem centered_coordinate_extrema {m : Masses} (hm : PositiveMasses m)
    {q : Configuration} (hc : centerLM m q = 0) (k : Axis) :
    q (Tuple.sort (fun i => q i k) 0) k ≤ 0 ∧
      0 ≤ q (Tuple.sort (fun i => q i k) 3) k := by
  let t : Label → ℝ := fun i => q i k
  have hsum : (∑ i, m i * t i) = 0 := center_coordinate_zero hc k
  rcases coordinate_extrema t with ⟨hmin, hmax⟩
  constructor
  · by_contra h
    have hpos : 0 < t (Tuple.sort t 0) := lt_of_not_ge h
    have hp : 0 < ∑ i, m i * t i := by
      apply Finset.sum_pos
      · intro i hi
        exact mul_pos (hm i) (hpos.trans_le (hmin i))
      · exact Finset.univ_nonempty
    linarith
  · by_contra h
    have hneg : t (Tuple.sort t 3) < 0 := lt_of_not_ge h
    have hp : 0 < ∑ i, -(m i * t i) := by
      apply Finset.sum_pos
      · intro i hi
        exact neg_pos.mpr (mul_neg_of_pos_of_neg (hm i) ((hmax i).trans_lt hneg))
      · exact Finset.univ_nonempty
    rw [Finset.sum_neg_distrib, hsum, neg_zero] at hp
    linarith

theorem centered_coordinate_abs_le_diameter {m : Masses} (hm : PositiveMasses m)
    {q : Configuration} (hc : centerLM m q = 0) (k : Axis) (i : Label) :
    |q i k| ≤ coordinateDiameter (fun j => q j k) := by
  rcases centered_coordinate_extrema hm hc k with ⟨hmin0, hmax0⟩
  rcases coordinate_extrema (fun j => q j k) with ⟨hmin, hmax⟩
  apply abs_le.mpr
  unfold coordinateDiameter
  constructor
  · have hi := hmin i
    linarith
  · have hi := hmax i
    linarith

/-- Coordinate range control used at the start of Proposition seed-limits.
The centering premise is discharged from the original equations. -/
theorem solution_coordinate_abs_bounds {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : IsSolution m s q) (i : Label) :
    |q i 0| ≤ 3 * (totalMass m / s) ^ (1 / (3 : ℝ)) ∧
      |q i 1| ≤ 3 * (totalMass m) ^ (1 / (3 : ℝ)) := by
  have hc := solution_center_zero m hs hq
  constructor
  · exact (centered_coordinate_abs_le_diameter hm hc 0 i).trans (diameter_x hm hs hq)
  · exact (centered_coordinate_abs_le_diameter hm hc 1 i).trans (diameter_y hm hs hq)

end FourBody

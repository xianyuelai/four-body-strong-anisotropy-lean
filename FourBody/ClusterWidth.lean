import FourBody.Geometry
import FourBody.ClusterGap
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Abs

/-!
The wide-cluster geometric step in v2 `prop:scales`, TeX lines 327--330.
Original manuscript SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

The points are the actual `FourBody.Point = EuclideanSpace ℝ (Fin 2)`
and retain the manuscript's fixed x/y axes. The cluster diameter is the
attained maximum minus minimum defined in `ClusterGap`. These lemmas
prove the geometric height lower bound, not the remaining force estimates
or the complete two-scale proposition.
-/

noncomputable section

namespace FourBody

/-- The actual cluster coordinate range bounds an unoriented difference. -/
theorem cluster_coordinate_abs_difference_le_diameter
    (J : Finset (Fin 4)) (t : Fin 4 → ℝ) (hJ : J.Nonempty)
    (i j : Fin 4) (hi : i ∈ J) (hj : j ∈ J) :
    |t i - t j| ≤ clusterCoordinateDiameter J t hJ := by
  have hforward := cluster_coordinate_difference_le_diameter J t hJ j i hj hi
  have hreverse := cluster_coordinate_difference_le_diameter J t hJ i j hi hj
  exact abs_le.mpr ⟨by linarith, hforward⟩

/-- The Euclidean distance squared in the manuscript's two actual axes. -/
theorem point_dist_sq_eq_coord_sum (p z : Point) :
    dist p z ^ 2 = (p 0 - z 0) ^ 2 + (p 1 - z 1) ^ 2 := by
  rw [dist_eq_norm]
  simpa only [Fin.sum_univ_two, PiLp.sub_apply] using
    EuclideanSpace.real_norm_sq_eq (p - z)

/-- The stronger squared vertical estimate used implicitly before the
manuscript weakens the separation to r/2. -/
theorem vertical_separation_sq_of_horizontal_le_half
    (p z : Point) {r : ℝ} (hdist : dist p z = r)
    (hx : |p 0 - z 0| ≤ r / 2) :
    3 * r ^ 2 ≤ 4 * (p 1 - z 1) ^ 2 := by
  have hsq := point_dist_sq_eq_coord_sum p z
  rw [hdist] at hsq
  have hxSq : (p 0 - z 0) ^ 2 ≤ (r / 2) ^ 2 :=
    sq_le_sq.mpr (hx.trans (le_abs_self (r / 2)))
  nlinarith

theorem vertical_separation_half_of_horizontal_le_half
    (p z : Point) {r : ℝ} (hr : 0 < r) (hdist : dist p z = r)
    (hx : |p 0 - z 0| ≤ r / 2) :
    r / 2 ≤ |p 1 - z 1| := by
  have hySq := vertical_separation_sq_of_horizontal_le_half p z hdist hx
  by_contra h
  have hy : |p 1 - z 1| ≤ r / 2 := (lt_of_not_ge h).le
  have hyUpperSq : (p 1 - z 1) ^ 2 ≤ (r / 2) ^ 2 :=
    sq_le_sq.mpr (hy.trans (le_abs_self (r / 2)))
  nlinarith [mul_pos hr hr]

/-- For a pair attaining a positive cluster distance r, horizontal
separation at most r/2 forces the actual vertical cluster range to be
at least r/2, and in particular strictly positive. -/
theorem cluster_vertical_diameter_ge_half_of_wide_pair
    (q : Configuration) (J : Finset Label) (hJ : J.Nonempty)
    (a b : Label) (ha : a ∈ J) (hb : b ∈ J)
    {r : ℝ} (hr : 0 < r) (hpair : dist (q a) (q b) = r)
    (hx : |q a 0 - q b 0| ≤ r / 2) :
    r / 2 ≤ clusterCoordinateDiameter J (fun i => q i 1) hJ ∧
      0 < clusterCoordinateDiameter J (fun i => q i 1) hJ := by
  have hy := vertical_separation_half_of_horizontal_le_half (q a) (q b) hr hpair hx
  have hdiam := cluster_coordinate_abs_difference_le_diameter
    J (fun i => q i 1) hJ a b ha hb
  have hlower : r / 2 ≤ clusterCoordinateDiameter J (fun i => q i 1) hJ :=
    hy.trans hdiam
  exact ⟨hlower, lt_of_lt_of_le (by linarith : 0 < r / 2) hlower⟩

end FourBody

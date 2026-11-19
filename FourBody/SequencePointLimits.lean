import FourBody.VerticalPartition
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Actual physical point and distance limits at the initial extraction

These are continuity consequences of the SAME four-coordinate subsequence
constructed in SequenceStart. They apply to physical Euclidean points,
not to an arbitrary norm proxy. This file does not prove the two-scale
internal bounds or compactness of the rescaled internal coordinates.

Frozen v2 source: lines 429--438; SHA256
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
Compilation status is recorded separately.
-/

noncomputable section
open Filter

namespace FourBody.SequencePointLimits

def verticalPoint (y : ℝ) : Point := !₂[0, y]

theorem verticalPoint_dist (y z : ℝ) :
    dist (verticalPoint y) (verticalPoint z) = |y - z| := by
  simp [verticalPoint, EuclideanSpace.dist_eq, Fin.sum_univ_two,
    Real.dist_eq, Real.sqrt_sq_eq_abs]

/-- The actual Euclidean topology is recovered from its two coordinates. -/
theorem point_tendsto {p : ℕ → Point} {y : ℝ}
    (hx : Tendsto (fun ν => p ν 0) atTop (nhds 0))
    (hy : Tendsto (fun ν => p ν 1) atTop (nhds y)) :
    Tendsto p atTop (nhds (verticalPoint y)) := by
  have htuple : Tendsto (fun ν => WithLp.ofLp (p ν)) atTop
      (nhds (WithLp.ofLp (verticalPoint y))) := by
    apply tendsto_pi_nhds.mpr
    intro k
    fin_cases k
    · simpa [verticalPoint] using hx
    · simpa [verticalPoint] using hy
  simpa only [Function.comp_def, WithLp.toLp_ofLp] using
    (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Axis => ℝ)).continuousAt.tendsto.comp htuple

theorem selected_point_tendsto {m : Masses} {s : ℕ → ℝ} {q : ℕ → Configuration}
    {φ : ℕ → ℕ} {y : Label → ℝ}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y) (i : Label) :
    Tendsto (fun ν => q (φ ν) i) atTop (nhds (verticalPoint (y i))) := by
  apply point_tendsto
  · exact hlim.2.2.2.2.2.2.1 i
  · exact tendsto_pi_nhds.mp hlim.2.2.2.2.2.1 i

theorem selected_distance_tendsto {m : Masses} {s : ℕ → ℝ} {q : ℕ → Configuration}
    {φ : ℕ → ℕ} {y : Label → ℝ}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y) (i j : Label) :
    Tendsto (fun ν => dist (q (φ ν) i) (q (φ ν) j)) atTop (nhds |y i - y j|) := by
  simpa only [verticalPoint_dist] using
    (selected_point_tendsto hlim i).dist (selected_point_tendsto hlim j)

/-- All same-class physical pair distances vanish, including the vacuous
singleton case, without yet claiming a lower bound after ε scaling. -/
theorem internal_distance_tendsto_zero {m : Masses} {s : ℕ → ℝ}
    {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    {i j : Label}
    (hij : blockOf (VerticalPartition.verticalPartitionDatum y) i =
      blockOf (VerticalPartition.verticalPartitionDatum y) j) :
    Tendsto (fun ν => dist (q (φ ν) i) (q (φ ν) j)) atTop (nhds 0) := by
  have heq := (VerticalPartition.blockOf_eq_iff_vertical_eq y i j).mp hij
  simpa only [heq, sub_self, abs_zero] using selected_distance_tendsto hlim i j

/-- The literal source cross-block distance limit with strictly positive
distinct ordered height difference. -/
theorem cross_distance_tendsto {m : Masses} {s : ℕ → ℝ}
    {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    {a b : BlockIndex (VerticalPartition.verticalPartitionDatum y)} (hab : a ≠ b)
    {i j : Label} (hi : i ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) a)
    (hj : j ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) b) :
    0 < |VerticalPartition.verticalHeight y a - VerticalPartition.verticalHeight y b| ∧
      Tendsto (fun ν => dist (q (φ ν) i) (q (φ ν) j)) atTop
        (nhds |VerticalPartition.verticalHeight y a - VerticalPartition.verticalHeight y b|) := by
  have hne : VerticalPartition.verticalHeight y a ≠ VerticalPartition.verticalHeight y b :=
    fun h => hab ((VerticalPartition.verticalHeight_strictMono y).injective h)
  refine ⟨abs_pos.mpr (sub_ne_zero.mpr hne), ?_⟩
  simpa only [(VerticalPartition.mem_datumBlock_iff_height y a i).mp hi,
    (VerticalPartition.mem_datumBlock_iff_height y b j).mp hj] using
    selected_distance_tendsto hlim i j

end FourBody.SequencePointLimits


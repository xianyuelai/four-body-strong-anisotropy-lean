import FourBody.SequencePointLimits
import Mathlib.Order.Filter.Finite
import Mathlib.Data.Finset.Max
import Mathlib.Topology.Order.OrderClosed

/-!
# One actual cross-distance lower bound on the selected sequence

Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD,
lines 437--439.
The bound is constructed as the minimum of half the positive attained
cross-height differences. If there are no cross pairs, δ=1 and the
universal separation conclusion is vacuous. No separation certificate is
an assumption. Static proof preparation; compiler verification pending.
-/

noncomputable section
open Filter

namespace FourBody.CrossSeparation

def crossPairs (y : Label → ℝ) : Finset (Label × Label) := by
  classical
  exact Finset.univ.filter (fun p => y p.1 ≠ y p.2)

def crossHalfGaps (y : Label → ℝ) : Finset ℝ := by
  classical
  exact (crossPairs y).image (fun p => |y p.1 - y p.2| / 2)

theorem crossHalfGaps_positive (y : Label → ℝ) {r : ℝ} (hr : r ∈ crossHalfGaps y) :
    0 < r := by
  classical
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
  have hne : y p.1 ≠ y p.2 := (Finset.mem_filter.mp hp).2
  exact div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) (by norm_num)

/-- Actual common δ from the finite nonempty height gaps; empty cross set
is handled explicitly. This is not an input to the main theorem. -/
theorem exists_cross_half_gap_bound (y : Label → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j : Label, y i ≠ y j → δ ≤ |y i - y j| / 2 := by
  classical
  by_cases hne : (crossHalfGaps y).Nonempty
  · let δ := (crossHalfGaps y).min' hne
    refine ⟨δ, crossHalfGaps_positive y ((crossHalfGaps y).min'_mem hne), ?_⟩
    intro i j hij
    exact (crossHalfGaps y).min'_le _
      (Finset.mem_image.mpr ⟨(i, j),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩)
  · refine ⟨1, by norm_num, ?_⟩
    intro i j hij
    exact (hne ⟨|y i - y j| / 2,
      Finset.mem_image.mpr ⟨(i, j),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩⟩).elim

/-- ONE eventual index gives a fixed positive lower bound for every
cross pair of the actual initial partition, including the one-block case. -/
theorem exists_eventual_cross_separation {m : Masses} {s : ℕ → ℝ}
    {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ν in atTop, ∀ i j : Label,
      blockOf (VerticalPartition.verticalPartitionDatum y) i ≠
        blockOf (VerticalPartition.verticalPartitionDatum y) j →
      δ ≤ dist (q (φ ν) i) (q (φ ν) j) := by
  obtain ⟨δ, hδ, hhalf⟩ := exists_cross_half_gap_bound y
  refine ⟨δ, hδ, ?_⟩
  apply eventually_all.mpr
  intro i
  apply eventually_all.mpr
  intro j
  by_cases hne : y i ≠ y j
  · have hgap : 0 < |y i - y j| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hsmall : |y i - y j| / 2 < |y i - y j| := by linarith
    exact ((SequencePointLimits.selected_distance_tendsto hlim i j).eventually
      (eventually_gt_nhds hsmall)).mono
      (fun ν hν => fun _ => (hhalf i j hne).trans hν.le)
  · have hblock := (VerticalPartition.blockOf_eq_iff_vertical_eq y i j).mpr
      (not_ne_iff.mp hne)
    exact Eventually.of_forall (fun _ => fun h => (h hblock).elim)

end FourBody.CrossSeparation


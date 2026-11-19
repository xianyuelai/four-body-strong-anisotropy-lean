import FourBody.SequencePointLimits
import FourBody.TwoScaleEstimates
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Order.OrderClosed

/-!
# The actual internal epsilon scale on the initial vertical blocks

Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD,
lines 432--436. This module invokes the actual TwoScale.twoScaleEstimates
proof candidate, not a scale certificate supplied as a hypothesis.
Its current source dependency is geometry-prep/TwoScaleEstimates.lean,
SHA256 25EDCF3AA712ACC2DC6B24606AF191F65BC9541DE4A7CCCAEE4B59E766B23570.
That module and these proof bodies have NOT yet been compiled.

All selected solutions come from arbitrary real sν → +∞ through the
single initial subsequence. Internal label order is still provisional.
-/

noncomputable section
open Filter

namespace FourBody.InternalScale

/-- Inherited initial limits after a genuine further subsequence.
Every conclusion uses the composed SAME physical subsequence φ ∘ ψ. -/
theorem initial_limit_comp {m : Masses} {s : ℕ → ℝ} {q : ℕ → Configuration}
    {φ : ℕ → ℕ} {y : Label → ℝ}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    SequenceStart.InitialVerticalLimit m s q (fun ν => φ (ψ ν)) y := by
  rcases hlim with ⟨hφ, hgt, hs, hepos, he, hy, hx, hbound, hcenter⟩
  refine ⟨hφ.comp hψ, (fun ν => hgt (ψ ν)), hs.comp hψ.tendsto_atTop,
    (fun ν => hepos (ψ ν)), he.comp hψ.tendsto_atTop,
    hy.comp hψ.tendsto_atTop, ?_, hbound, hcenter⟩
  intro i
  exact (hx i).comp hψ.tendsto_atTop

/-- A fixed internal pair excludes the source's positive macroscopic
alternative because its actual physical distance tends to zero. -/
theorem internal_pair_eventually_scaled {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    (hq : ∀ ν, IsSolution m (s ν) (q ν))
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    {i j : Label} (hij : i ≠ j)
    (hblock : blockOf (VerticalPartition.verticalPartitionDatum y) i =
      blockOf (VerticalPartition.verticalPartitionDatum y) j) :
    ∀ᶠ ν in atTop,
      ScaleConstants.c₀ m * epsilon (s (φ ν)) ≤ dist (q (φ ν) i) (q (φ ν) j) ∧
      dist (q (φ ν) i) (q (φ ν) j) < ScaleConstants.C m * epsilon (s (φ ν)) := by
  have hdist := SequencePointLimits.internal_distance_tendsto_zero hlim hblock
  have hc₁ : 0 < ScaleConstants.c₁ m := (ScaleConstants.constants_positive m hm).2.2.1
  filter_upwards [hdist.eventually (eventually_lt_nhds hc₁)] with ν hν
  have hscale := TwoScale.twoScaleEstimates m hm (hlim.2.1 ν).le (hq (φ ν)) i j hij
  exact ⟨hscale.1, hscale.2.resolve_right (not_le_of_gt hν)⟩

/-- ONE eventual index works for every actual internal pair in every block.
Finite conjunction is proved over actual Fin block positions and four labels;
the empty pair sets of singleton blocks cause no exception. -/
theorem eventually_all_internal_scaled {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    (hq : ∀ ν, IsSolution m (s ν) (q ν))
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y) :
    ∀ᶠ ν in atTop, ∀ (a : BlockIndex (VerticalPartition.verticalPartitionDatum y))
      (i j : Label),
      i ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) a →
      j ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) a → i ≠ j →
        ScaleConstants.c₀ m * epsilon (s (φ ν)) ≤ dist (q (φ ν) i) (q (φ ν) j) ∧
        dist (q (φ ν) i) (q (φ ν) j) < ScaleConstants.C m * epsilon (s (φ ν)) := by
  apply eventually_all.mpr
  intro a
  apply eventually_all.mpr
  intro i
  apply eventually_all.mpr
  intro j
  by_cases hi : i ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) a
  · by_cases hj : j ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) a
    · by_cases hij : i ≠ j
      · have hblock := (blockOf_eq_of_mem (VerticalPartition.verticalPartitionDatum y) hi).trans
          (blockOf_eq_of_mem (VerticalPartition.verticalPartitionDatum y) hj).symm
        exact (internal_pair_eventually_scaled hm hq hlim hij hblock).mono
          (fun _ h => fun _ _ _ => h)
      · exact Eventually.of_forall (fun _ => fun _ _ h => (hij h).elim)
    · exact Eventually.of_forall (fun _ => fun _ h _ => (hj h).elim)
  · exact Eventually.of_forall (fun _ => fun h _ _ => (hi h).elim)

end FourBody.InternalScale


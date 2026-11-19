import FourBody.TwoScaleEstimates
import Mathlib.Topology.Order.OrderClosed

/-!
Independent S2-U29 bridge candidate from the actual v2 lines 340--343.
No Lean/Lake invocation is asserted. Actual acceptance must be supplied
by a later owner-granted strict build and complete type/axiom audit.
The sequence is the original arbitrary sequence; no subsequence or
previously constructed branch is an input.
-/

noncomputable section
open Filter
namespace FourBody.SourceAllSequenceScale

theorem eventually_small_scale_of_distance_tendsto_zero
    {m : Masses} (hm : PositiveMasses m)
    (s : ℕ → ℝ) (q : ℕ → Configuration)
    (hs : Tendsto s atTop atTop)
    (hq : ∀ ν, IsSolution m (s ν) (q ν))
    (i j : Label) (hij : i ≠ j)
    (hdist : Tendsto (fun ν => dist (q ν i) (q ν j)) atTop (nhds 0)) :
    ∀ᶠ ν in atTop,
      ScaleConstants.c₀ m * epsilon (s ν) ≤ dist (q ν i) (q ν j) ∧
      dist (q ν i) (q ν j) < ScaleConstants.C m * epsilon (s ν) := by
  have hc₁ : 0 < ScaleConstants.c₁ m := (ScaleConstants.constants_positive m hm).2.2.1
  have hsone : ∀ᶠ ν in atTop, 1 ≤ s ν := hs.eventually (eventually_ge_atTop 1)
  have hsmall : ∀ᶠ ν in atTop, dist (q ν i) (q ν j) < ScaleConstants.c₁ m :=
    hdist.eventually (eventually_lt_nhds hc₁)
  filter_upwards [hsone, hsmall] with ν hνs hνsmall
  have hscale := TwoScale.twoScaleEstimates m hm hνs (hq ν) i j hij
  exact ⟨hscale.1, hscale.2.resolve_right (not_le_of_gt hνsmall)⟩

end FourBody.SourceAllSequenceScale

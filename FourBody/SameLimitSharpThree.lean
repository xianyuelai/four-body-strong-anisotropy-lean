import FourBody.ScalarCubicSharp
import FourBody.CanonicalSeedLimit

set_option autoImplicit false

/-!
A literal-coefficient corollary on ONE selected original solution
subsequence. Actual build and kernel-replay evidence is recorded separately.
The inputs hlim, hdata and heq are the actual outputs of
InternalEquationLimits.exists_internal_equation_limit hm hs hq; hhnew and
hhold are the actual physical mean coordinates for this SAME subsequence.
There is no assumed cubic estimate, seed, branch or main theorem input.
The existing canonical endpoint and its valid coefficient 6 are unchanged.
-/

noncomputable section
open Filter

namespace FourBody.SameLimitSharpThree
open ReorderedLimitCoordinates

/-- The actual final datum, physical mean coordinates and canonical seed
use the same φ,y,P₀. One actual cross gap supplies the literal source
constant 3 simultaneously for fields, old block means and final H.
The final H estimate is transported by equality of actual means, with
no change of δ, coefficient, selected subsequence or physical configuration. -/
theorem final_seed_and_sharp_cubic_same_limit {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    {P₀ : Configuration} (hq : ∀ ν, IsSolution m (s ν) (q ν))
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀)
    (heq : InternalEquationLimits.InternalEquationAtLimit m y P₀)
    {hnew : ℕ → BlowupCoordinates m (finalDatum y P₀)}
    {hold : ℕ → BlowupCoordinates m (VerticalPartition.verticalPartitionDatum y)}
    (hhnew : ∀ ν, CoordinatesOfConfiguration m (finalDatum y P₀)
      (epsilon (s (φ ν))) (q (φ ν)) (hnew ν))
    (hhold : ∀ ν, CoordinatesOfConfiguration m (VerticalPartition.verticalPartitionDatum y)
      (epsilon (s (φ ν))) (q (φ ν)) (hold ν)) :
    finalCoordinates hlim hdata = seedCoordinates hm (finalDatum y P₀) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ν in atTop,
        (∀ i : Label, |NewtonFieldLimits.physicalExternalField m
          (VerticalPartition.verticalPartitionDatum y) (q (φ ν)) i 0| ≤
            (3 * (totalMass m) ^ ((4 : ℝ) / 3) / δ ^ 3) * epsilon (s (φ ν))) ∧
        (∀ a : BlockIndex (VerticalPartition.verticalPartitionDatum y),
          |NewtonFieldLimits.physicalExternalMean m (VerticalPartition.verticalPartitionDatum y)
            (q (φ ν)) a 0| ≤
              (3 * (totalMass m) ^ ((4 : ℝ) / 3) / δ ^ 3) * epsilon (s (φ ν))) ∧
        (∀ a : BlockIndex (finalDatum y P₀), |outerH (hnew ν) a| ≤
          (3 * (totalMass m) ^ ((4 : ℝ) / 3) / δ ^ 3) * (epsilon (s (φ ν))) ^ 3) := by
  refine ⟨CanonicalSeedLimit.seed_eq_seedCoordinates hm
    (finalCoordinates_isSeed hm hq hlim hdata heq), ?_⟩
  obtain ⟨δ, hδ, hsep⟩ := CrossSeparation.exists_eventual_cross_separation hlim
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hsep] with ν hν
  have hsν : 0 < s (φ ν) := lt_trans (by norm_num) (hlim.2.1 ν)
  refine ⟨fun i => ScalarSupplement.external_horizontal_bound_sharp hm _ hsν
    (hq (φ ν)) hδ hν i,
    fun a => ScalarSupplement.external_mean_horizontal_bound_sharp hm _ hsν
      (hq (φ ν)) hδ hν a, ?_⟩
  intro a
  rw [SeedLimitCandidate.actual_horizontal_coordinates_eq (hhnew ν) (hhold ν) a]
  exact ScalarSupplement.horizontal_centers_cubic_bound_sharp hm hsν
    (hq (φ ν)) (hhold ν) hδ hν (oldIndex y P₀ a)

end FourBody.SameLimitSharpThree

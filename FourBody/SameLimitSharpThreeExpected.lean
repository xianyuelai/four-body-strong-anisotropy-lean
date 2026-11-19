import FourBody.ScalarCubicSharp
import FourBody.CanonicalSeedLimit

set_option autoImplicit false

/-!
Independently authored complete source-facing Prop for v2 S3-U39/U40.
Frozen before Root elaborates this specification or the separate corollary.
Actual build and kernel-replay evidence is recorded separately. It is not a proof, a certificate, an expected AST
copied from an actual theorem, or a changed Main statement.

The argument order and binder modes are explicit and match the intended
same-limit corollary: m implicit, hm explicit; s,q,φ,y,P₀ implicit;
hq,hlim,hdata,heq explicit; hnew,hold implicit; hhnew,hhold explicit.
The actual inner-limit data and coordinates are the same witnesses from
the original solution-sequence proof, not a second subsequence.
-/

noncomputable section
open Filter

namespace FourBody.SameLimitSharpThreeExpected
open ReorderedLimitCoordinates

def Statement : Prop :=
  ∀ {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    {P₀ : Configuration} (_hq : ∀ ν, IsSolution m (s ν) (q ν))
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀)
    (_heq : InternalEquationLimits.InternalEquationAtLimit m y P₀)
    {hnew : ℕ → BlowupCoordinates m (finalDatum y P₀)}
    {hold : ℕ → BlowupCoordinates m (VerticalPartition.verticalPartitionDatum y)}
    (_hhnew : ∀ ν, CoordinatesOfConfiguration m (finalDatum y P₀)
      (epsilon (s (φ ν))) (q (φ ν)) (hnew ν))
    (_hhold : ∀ ν, CoordinatesOfConfiguration m (VerticalPartition.verticalPartitionDatum y)
      (epsilon (s (φ ν))) (q (φ ν)) (hold ν)),
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
          (3 * (totalMass m) ^ ((4 : ℝ) / 3) / δ ^ 3) * (epsilon (s (φ ν))) ^ 3)

end FourBody.SameLimitSharpThreeExpected

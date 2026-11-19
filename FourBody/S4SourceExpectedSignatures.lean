import FourBody.SourceExpectedS4

/-!
STATIC independent expected TYPE signatures for S4SourceFidelityBridges.
These are propositions, not assumed proof certificates. Their definition
values are written from the already frozen paper-source propositions before
any actual bridge type output exists. They must be compiled and audited
independently; no actual declaration's type/hash is used to construct them.

For each bridge theorem, compare its complete type Expr to the corresponding
expected signature's complete definition value Expr after independently
checking all thirteen underlying source proposition bodies. The latter
check is essential: matching the same alias constant alone is insufficient.
No compiler invocation was made while preparing this file.
-/

set_option autoImplicit false
noncomputable section
namespace FourBody.SourceFidelityS4.ExpectedSignatures

open SourceExpectedS4

def sourceWeightedConstraintType : Prop := WeightedConstraintType
def sourceDimensionBreakdownType : Prop := DimensionBreakdownType
def sourceBoundaryFactorsType : Prop := BoundaryFactorsType
def sourcePositionMapType : Prop := PositionMapType

def analyticLocalBranchBody_iff_actual : Prop :=
  ∀ (m : Masses) (d : OrderedClusterDatum)
    (seed : BlowupCoordinates m d) (η : ℝ)
    (N : Set (BlowupCoordinates m d)) (h : ℝ → BlowupCoordinates m d),
    AnalyticLocalBranchBody m d seed η N h ↔
      AnalyticLocalBranch m d seed η N h

def sourceAllDatumBranchType : Prop := AllDatumBranchType
def sourceActualFAnalyticAtSeedType : Prop := ActualFAnalyticAtSeedType
def sourceActualSeedZeroType : Prop := ActualSeedZeroType
def sourceEntireSeedDerivativeType : Prop := EntireSeedDerivativeType
def sourceActualSeedDerivativeInverseType : Prop := ActualSeedDerivativeInverseType
def sourceActualIFTGraphType : Prop := ActualIFTGraphType
def sourceFixedParameterChainRuleType : Prop := FixedParameterChainRuleType
def sourceOriginalWDerivativeType : Prop := OriginalWDerivativeType

end FourBody.SourceFidelityS4.ExpectedSignatures

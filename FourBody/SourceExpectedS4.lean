import FourBody.LocalBranches

/-!
Independent source-derived TYPE EXPECTATION CANDIDATES for v2 section 4.
This file is outside the formal project and has not been compiled.
It defines propositions only: no theorem, axiom, assumed analytic interface,
certificate for the main theorem, or proof-completion assertion is supplied.
Each quantifier is derived from frozen v2 lines 512--651 and the 41-item source
ledger. Actual AST equality and independent expected-AST compilation remain
pending. Actual historical AST hashes must not be substituted for these goals.
-/

noncomputable section
open scoped BigOperators
open Set
namespace FourBody.SourceExpectedS4

/-- eq:constraints means these actual four weighted equations. -/
def WeightedConstraintType : Prop :=
  ∀ (m : Masses), PositiveMasses m → ∀ (d : OrderedClusterDatum)
    (z : CoordinateAmbient d),
    z ∈ coordinateSpace m d ↔
      (∑ a, datumBlockMass m d a * z.1.1 a) = 0 ∧
      (∑ a, datumBlockMass m d a * z.1.2 a) = 0 ∧
      (∀ a, (∑ i ∈ datumBlockLabels d a, m i * z.2.1 i) = 0) ∧
      (∀ a, (∑ i ∈ datumBlockLabels d a, m i * z.2.2 i) = 0)

/-- The numerical decomposition is an obligation in addition to finrank=6. -/
def DimensionBreakdownType : Prop :=
  ∀ (m : Masses), PositiveMasses m → ∀ d : OrderedClusterDatum,
    Module.finrank ℝ (BlowupCoordinates m d) =
      2 * (d.blocks.length - 1) +
        2 * (∑ a : BlockIndex d, ((datumBlock d a).length - 1)) ∧
    2 * (d.blocks.length - 1) +
      2 * (∑ a : BlockIndex d, ((datumBlock d a).length - 1)) = 6

def BoundaryFactorsType : Prop :=
  ∀ (m : Masses), PositiveMasses m → ∀ d : OrderedClusterDatum,
    (d.blocks.length = 1 →
      ∀ z : CoordinateProduct.OuterSpace m d, z = 0) ∧
    (∀ a : BlockIndex d, (datumBlock d a).length = 1 →
      ∀ z : CoordinateProduct.InnerSpace m d a, z = 0)

/-- Algebraic Q statement; positive epsilon is the source's physical range. -/
def PositionMapType : Prop :=
  ∀ (m : Masses) (hm : PositiveMasses m) (d : OrderedClusterDatum)
    (ε : ℝ) (hε : 0 < ε) (h : BlowupCoordinates m d),
    RepresentsCoordinates m d ε h
      ((coordinateContinuousEquivalence hm d (ne_of_gt hε) h : W m) : Configuration) ∧
    (∀ a : BlockIndex d,
      datumBlockMean m d (physicalCoordinates ε h) a =
        !₂[ε * outerH h a, outerY h a])

/-- This expands the protected source definition rather than trusting its name. -/
def AnalyticLocalBranchBody (m : Masses) (d : OrderedClusterDatum)
    (seed : BlowupCoordinates m d) (η : ℝ)
    (N : Set (BlowupCoordinates m d)) (h : ℝ → BlowupCoordinates m d) : Prop :=
  0 < η ∧ IsOpen N ∧ seed ∈ N ∧ IsSeed m d seed ∧
  AnalyticOnNhd ℝ h (Ioo (-η) η) ∧ h 0 = seed ∧
  ∀ ε : ℝ, 0 < ε → ε < η →
    h ε ∈ N ∧ ∃ q : Configuration,
      IsSolution m (parameterFromEpsilon ε) q ∧
      RepresentsCoordinates m d ε (h ε) q ∧
      (∀ q' : Configuration, IsSolution m (parameterFromEpsilon ε) q' →
        (∃ h' : BlowupCoordinates m d,
          h' ∈ N ∧ RepresentsCoordinates m d ε h' q') → q' = q) ∧
      (∀ h' : BlowupCoordinates m d,
        h' ∈ N → RepresentsCoordinates m d ε h' q → h' = h ε) ∧
      (∃ hq : q ∈ W m,
        DifferentiableAt ℝ (restrictedResidual m (parameterFromEpsilon ε))
          (⟨q, hq⟩ : W m) ∧
        Function.Bijective
          (fderiv ℝ (restrictedResidual m (parameterFromEpsilon ε))
            (⟨q, hq⟩ : W m)))

/-- The standalone local theorem has only original positive masses and datum.
Neither a seed, analytic F, an inverse, nor a branch is an input conclusion. -/
def AllDatumBranchType : Prop :=
  ∀ (m : Masses), PositiveMasses m → ∀ d : OrderedClusterDatum,
    ∃ (seed : BlowupCoordinates m d) (η : ℝ)
      (N : Set (BlowupCoordinates m d)) (h : ℝ → BlowupCoordinates m d),
      AnalyticLocalBranchBody m d seed η N h

def ActualFAnalyticAtSeedType : Prop :=
  ∀ (m : Masses) (hm : PositiveMasses m) (d : OrderedClusterDatum)
    (seed : BlowupCoordinates m d), IsSeed m d seed →
      AnalyticAt ℝ
        (fun p : ℝ × BlowupCoordinates m d => blowupResidual hm p.1 p.2) (0, seed)

def ActualSeedZeroType : Prop :=
  ∀ (m : Masses) (hm : PositiveMasses m) (d : OrderedClusterDatum)
    (seed : BlowupCoordinates m d), IsSeed m d seed →
      blowupResidual hm 0 seed = 0

/-- Correct signs for the complete derivative; forall v checks mixed blocks. -/
def EntireSeedDerivativeType : Prop :=
  ∀ (m : Masses) (hm : PositiveMasses m) (d : OrderedClusterDatum)
    (seed : BlowupCoordinates m d), IsSeed m d seed →
    ∀ v : BlowupCoordinates m d,
      CoordinateProduct.equivalence m d
        (fderiv ℝ (fun h : BlowupCoordinates m d => blowupResidual hm 0 h) seed v) =
      ((-(CoordinateProduct.equivalence m d v).1.1,
        -(SeedJacobian.scalarShift (datumBlockMass m d)
          (CoordinateProduct.equivalence m d seed).1.2
          (CoordinateProduct.equivalence m d v).1.2)),
       fun a =>
        (-(SeedJacobian.scalarShift (CoordinateProduct.internalMass m d a)
          ((CoordinateProduct.equivalence m d seed).2 a).1
          ((CoordinateProduct.equivalence m d v).2 a).1),
         SeedJacobian.scalarL (CoordinateProduct.internalMass m d a)
          ((CoordinateProduct.equivalence m d seed).2 a).1
          ((CoordinateProduct.equivalence m d v).2 a).2))

def ActualSeedDerivativeInverseType : Prop :=
  ∀ (m : Masses) (hm : PositiveMasses m) (d : OrderedClusterDatum)
    (seed : BlowupCoordinates m d), IsSeed m d seed →
      (fderiv ℝ (fun h : BlowupCoordinates m d => blowupResidual hm 0 h) seed).IsInvertible

/-- Full fixed signed rectangle, discharged from the original hm and datum.
This is an expected existential conclusion, never an assumed IFT certificate. -/
def ActualIFTGraphType : Prop :=
  ∀ (m : Masses) (hm : PositiveMasses m) (d : OrderedClusterDatum),
    ∃ (η δ : ℝ) (N : Set (BlowupCoordinates m d))
      (h : ℝ → BlowupCoordinates m d),
      0 < η ∧ 0 < δ ∧ IsOpen N ∧ seedCoordinates hm d ∈ N ∧
      AnalyticOnNhd ℝ h (Ioo (-η) η) ∧ h 0 = seedCoordinates hm d ∧
      AnalyticOnNhd ℝ
        (fun p : ℝ × BlowupCoordinates m d => blowupResidual hm p.1 p.2)
        (Ioo (-η) η ×ˢ N) ∧
      (∀ ε ∈ Ioo (-η) η, h ε ∈ N ∧ blowupResidual hm ε (h ε) = 0) ∧
      (∀ ε ∈ Ioo (-η) η, ∀ z ∈ N,
        BlowupAnalytic.UniformDistanceBound δ (ε, z) ∧
        (fderiv ℝ (fun w : BlowupCoordinates m d => blowupResidual hm ε w) z).IsInvertible ∧
        (blowupResidual hm ε z = 0 ↔ z = h ε))

/-- epsilon is fixed in the derivative, and T differs from Q inverse. -/
def FixedParameterChainRuleType : Prop :=
  ∀ (m : Masses) (hm : PositiveMasses m) (d : OrderedClusterDatum)
    (seed : BlowupCoordinates m d) (r : LocalBranch.ZeroRectangle hm d seed)
    (ε : ℝ) (hε : 0 < ε), ε < r.eta →
    ∀ h : BlowupCoordinates m d, h ∈ r.neighborhood →
      let Q := coordinateContinuousEquivalence hm d (ne_of_gt hε)
      let T := residualTContinuousEquivalence hm d (ne_of_gt hε)
      fderiv ℝ (fun z : BlowupCoordinates m d => blowupResidual hm ε z) h =
        T.toContinuousLinearMap.comp
          ((fderiv ℝ (restrictedResidual m (parameterFromEpsilon ε)) (Q h)).comp
            Q.toContinuousLinearMap)

def OriginalWDerivativeType : Prop :=
  ∀ (m : Masses) (hm : PositiveMasses m) (d : OrderedClusterDatum)
    (seed : BlowupCoordinates m d) (r : LocalBranch.ZeroRectangle hm d seed)
    (ε : ℝ), 0 < ε → ε < r.eta →
    ∀ h : BlowupCoordinates m d, h ∈ r.neighborhood →
      ∃ hq : physicalCoordinates ε h ∈ W m,
        DifferentiableAt ℝ (restrictedResidual m (parameterFromEpsilon ε))
          (⟨physicalCoordinates ε h, hq⟩ : W m) ∧
        Function.Bijective
          (fderiv ℝ (restrictedResidual m (parameterFromEpsilon ε))
            (⟨physicalCoordinates ε h, hq⟩ : W m))

end FourBody.SourceExpectedS4


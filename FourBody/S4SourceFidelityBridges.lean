import FourBody.SourceExpectedS4
import FourBody.ScalarCoordinateDimensions
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
STATIC source-fidelity bridges for the thirteen independently written
section-4 propositions in S4SourceExpectedTypes.candidate.lean.

Planned expected-spec module name: FourBody.SourceExpectedS4. Its source is
the already frozen candidate, copied without changing its bytes. This file
does not modify that candidate, the formal project, Paper, Audit or COVERAGE.
Neither file has been compiled in this preparation step.

Frozen v2 manuscript SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

Theorems below prove independent source-defined propositions from actual
mathematical results. No expected proposition, residual-analyticity interface,
seed-existence certificate, IFT certificate or final branch conclusion is
assumed as an input to the standalone existential conclusions. ZeroRectangle
in the two fixed-parameter local statements is precisely their already frozen
source-local hypothesis; its existence is proved from original positive masses
and datum in sourceActualIFTGraphType and sourceAllDatumBranchType.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Set

namespace FourBody.SourceFidelityS4

open SourceExpectedS4

/-- The actual unconstrained-mass kernel identity is specialized to the
manuscript's fixed-positive-mass scope. Positivity is not an assumed kernel
or constraint equivalence. -/
theorem sourceWeightedConstraintType : WeightedConstraintType := by
  intro m _hm d z
  exact mem_coordinateSpace_iff m d z

/-- The actual factor-dimension decomposition and its literal evaluation are
both retained. Actual nodup block labels identify cardinalities with lengths. -/
theorem sourceDimensionBreakdownType : DimensionBreakdownType := by
  intro m hm d
  simpa only [ScalarDimensions.datumBlockLabels_card_eq_length] using
    (ScalarCoordinateDimensions.blowupCoordinates_finrank_explicit_split hm d)

/-- Zero finrank is proved from the actual factor-dimension formula. The
local Subsingleton instances are consequences, not postulated zero spaces. -/
theorem sourceBoundaryFactorsType : BoundaryFactorsType := by
  intro m hm d
  constructor
  · intro hk z
    have hdim : Module.finrank ℝ (CoordinateProduct.OuterSpace m d) = 0 := by
      rw [ScalarDimensions.outerSpace_finrank hm d, hk]
    let : Subsingleton (CoordinateProduct.OuterSpace m d) :=
      (Module.finrank_zero_iff
        (R := ℝ) (M := CoordinateProduct.OuterSpace m d)).mp hdim
    exact Subsingleton.elim z 0
  · intro a ha z
    have hdim : Module.finrank ℝ (CoordinateProduct.InnerSpace m d a) = 0 := by
      rw [ScalarDimensions.innerSpace_finrank_length hm d a, ha]
    let : Subsingleton (CoordinateProduct.InnerSpace m d a) :=
      (Module.finrank_zero_iff
        (R := ℝ) (M := CoordinateProduct.InnerSpace m d a)).mp hdim
    exact Subsingleton.elim z 0

/-- The actual CLE has coordinateQ as its underlying map, and the same
original mass-centroid calculation recovers the source block means. -/
theorem sourcePositionMapType : PositionMapType := by
  intro m hm d ε hε h
  constructor
  · change RepresentsCoordinates m d ε h (physicalCoordinates ε h)
    exact represents_physicalCoordinates ε h
  · intro a
    exact datumBlockMean_physicalCoordinates hm ε h a

/-- Expanding OriginalNondegenerate exposes the actual W membership witness,
DifferentiableAt and Bijective fderiv conjunction. This is an unconditional
definitional equivalence for the arbitrary displayed branch parameters. -/
theorem analyticLocalBranchBody_iff_actual (m : Masses)
    (d : OrderedClusterDatum) (seed : BlowupCoordinates m d) (η : ℝ)
    (N : Set (BlowupCoordinates m d)) (h : ℝ → BlowupCoordinates m d) :
    AnalyticLocalBranchBody m d seed η N h ↔
      AnalyticLocalBranch m d seed η N h := Iff.rfl

/-- The public actual local theorem has only m, its original positivity and
the actual datum as inputs. Its actual branch output is expanded here. -/
theorem sourceAllDatumBranchType : AllDatumBranchType := by
  intro m hm d
  obtain ⟨seed, η, N, h, hactual⟩ := LocalBranch.allDataLocalBranches m hm d
  exact ⟨seed, η, N, h,
    (analyticLocalBranchBody_iff_actual m d seed η N h).mpr hactual⟩

theorem sourceActualFAnalyticAtSeedType : ActualFAnalyticAtSeedType := by
  intro m hm d seed hs
  exact BlowupAnalytic.blowupResidual_seed_joint_analyticAt hm hs

theorem sourceActualSeedZeroType : ActualSeedZeroType := by
  intro m hm d seed hs
  exact isSeed_blowupResidual_zero hm seed hs

/-- The actual component theorem evaluates every arbitrary tangent and keeps
all four signs; it is not merely a disconnected invertibility conclusion. -/
theorem sourceEntireSeedDerivativeType : EntireSeedDerivativeType := by
  intro m hm d seed hs v
  exact SeedJacobian.blowupResidual_zero_fderiv_components hm hs v

theorem sourceActualSeedDerivativeInverseType : ActualSeedDerivativeInverseType := by
  intro m hm d seed hs
  exact SeedJacobian.blowupResidual_zero_fderiv_isInvertible hm hs

/-- The full raw IFT graph is an existential conclusion constructed with
zeroRectangle_exists. The record itself is not an input to this theorem.
The final iff explicitly reverses the actual graph's equality by Eq.symm. -/
theorem sourceActualIFTGraphType : ActualIFTGraphType := by
  intro m hm d
  obtain ⟨r⟩ := LocalBranch.zeroRectangle_exists hm d
  refine ⟨r.eta, r.delta, r.neighborhood, r.branch,
    r.eta_pos, r.delta_pos, r.neighborhood_open, r.seed_mem,
    r.branch_analytic, r.branch_zero, r.residual_analytic, ?_, ?_⟩
  · intro ε hε
    exact ⟨r.branch_mem ε hε, r.branch_root ε hε⟩
  · intro ε hε z hz
    refine ⟨r.distances ε hε z hz, ?_, ?_⟩
    · exact r.derivative_invertible ε hε z hz
    · constructor
      · intro hzero
        exact ((r.graph_exact ε hε z hz).mp hzero).symm
      · intro hcoord
        exact (r.graph_exact ε hε z hz).mpr hcoord.symm

/-- Epsilon is held fixed. The true partial jacobian definition is fderiv
of that fixed slice; the actual chain rule has two different outside CLEs. -/
theorem sourceFixedParameterChainRuleType : FixedParameterChainRuleType := by
  intro m hm d seed r ε hε hη h hh
  exact LocalBranch.derivative_physical_identity_on_rectangle hm r hε hη h hh

/-- The actual original residual nondegeneracy predicate reduces exactly to
the independently written membership/differentiability/bijectivity body. -/
theorem sourceOriginalWDerivativeType : OriginalWDerivativeType := by
  intro m hm d seed r ε hε hη h hh
  change OriginalNondegenerate m (parameterFromEpsilon ε) (physicalCoordinates ε h)
  exact LocalBranch.originalNondegenerate_of_zeroRectangle hm r hε hη h hh

end FourBody.SourceFidelityS4

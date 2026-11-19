import FourBody.SeedLimitCandidate
import FourBody.SeedConstruction

/-!
# Identification of the actual Proposition 3.2 seed with the canonical seed

Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
Source lines 477--489 identify the ordered internal and external scalar roots;
lines 665--672 use that identity with a fixed local seed neighborhood.

STATIC SUPPLEMENT: this new module has not been elaborated or kernel audited.
It imports the actually checked arbitrary-sequence Proposition 3.2 proof and
the concrete scalar-minimization seed construction. It takes no assumed seed
limit theorem, branch certificate, canonical identity or main theorem input.
The original selected subsequence, datum and physical mean coordinates are
kept unchanged. Only the proved equality of their seed is substituted.
-/

noncomputable section
open Filter

namespace FourBody.CanonicalSeedLimit

/-- The unique seed is the actual tuple built from the ordered scalar roots,
including the one-block and singleton cases. This equality is derived from
the proved uniqueness predicate, rather than assumed as an interface. -/
theorem seed_eq_seedCoordinates {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d}
    (hseed : IsSeed m d seed) : seed = seedCoordinates hm d :=
  (seed_existsUnique hm d).unique hseed (seedCoordinates_isSeed hm d)

/-- A locally constructed family's seed is the same canonical seed for the
same literal ordered datum. No change of labels, block order or coordinates
is hidden in this equality. -/
theorem local_branch_seed_eq_seedCoordinates {m : Masses}
    (hm : PositiveMasses m) {d : OrderedClusterDatum}
    {seed : BlowupCoordinates m d} {eta : ℝ}
    {N : Set (BlowupCoordinates m d)} {branch : ℝ → BlowupCoordinates m d}
    (hlocal : AnalyticLocalBranch m d seed eta N branch) :
    seed = seedCoordinates hm d := by
  rcases hlocal with ⟨_heta, _hopen, _hmem, hseed, _hanalytic, _hzero, _hphysical⟩
  exact seed_eq_seedCoordinates hm hseed

/-- Full original arbitrary-sequence conclusion with the canonical seed.
Every coordinate, distance regime and cubic bound uses the SAME φ,d,h
produced by the checked Proposition 3.2 theorem. The only input hypotheses
are positivity of the fixed masses, sν→∞ and the actual original equations.
No positivity is imposed on all original sequence parameters. -/
theorem canonical_seed_limit (m : Masses) (hm : PositiveMasses m)
    (s : ℕ → ℝ) (q : ℕ → Configuration)
    (hs : Tendsto s atTop atTop)
    (hq : ∀ ν : ℕ, IsSolution m (s ν) (q ν)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ d : OrderedClusterDatum,
      ∃ h : ℕ → BlowupCoordinates m d,
        IsSeed m d (seedCoordinates hm d) ∧
        (∀ ν : ℕ, 1 < s (φ ν)) ∧
        Tendsto (fun ν => epsilon (s (φ ν))) atTop (nhds 0) ∧
        (∀ ν : ℕ, CoordinatesOfConfiguration m d (epsilon (s (φ ν)))
          (q (φ ν)) (h ν)) ∧
        (∀ a : BlockIndex d,
          Tendsto (fun ν => outerH (h ν) a) atTop (nhds 0) ∧
          Tendsto (fun ν => outerY (h ν) a) atTop
            (nhds (outerY (seedCoordinates hm d) a))) ∧
        (∀ (a : BlockIndex d) (i : Label), i ∈ datumBlock d a →
          Tendsto
            (fun ν => internalVectorCoordinate m d (epsilon (s (φ ν))) (q (φ ν)) a i)
            atTop (nhds (!₂[innerU (seedCoordinates hm d) i, 0] : Point))) ∧
        HorizontalCentersCubicBound m d (fun ν => epsilon (s (φ ν))) h ∧
        SequenceDistanceRegimes m d (seedCoordinates hm d)
          (fun ν => epsilon (s (φ ν))) (fun ν => q (φ ν)) := by
  obtain ⟨φ, hφ, d, seed, h, hseed, hsone, hepsilon, hcoordinates,
      houter, hinner, hcubic, hdistances⟩ :=
    SeedLimitCandidate.seedLimitStatement_candidate m hm s q hs hq
  have hcanonical : seed = seedCoordinates hm d :=
    seed_eq_seedCoordinates hm hseed
  subst seed
  exact ⟨φ, hφ, d, h, hseed, hsone, hepsilon, hcoordinates,
    houter, hinner, hcubic, hdistances⟩

end FourBody.CanonicalSeedLimit

import FourBody.BranchRecoveryContinuity
import FourBody.ParameterThreshold
import FourBody.CoverageSequence

/-!
Frozen Pro v2 Section 5, lines 650--673. SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

Failure of eventual coverage produces original solutions at s tending to
infinity. The actual Proposition 3.2 proof produces a common subsequence
and genuine seed, seed uniqueness identifies the chosen local seed, and
full coordinate convergence enters its FIXED open N. Local uniqueness
then contradicts the actual missing branch value. No seed-limit theorem,
compactness, coverage or main theorem is assumed.

Initially prepared as a proof candidate. Actual build/audit status is
recorded in strict receipts; this module alone does not attest
whole-paper acceptance.
-/

noncomputable section
open Filter Topology
namespace FourBody.Global

/-- The physical values of the SAME actual coordinate family. This set
definition includes no assertion of existence, uniqueness or exhaustion. -/
def branchConfigurations {m : Masses}
    (h : ∀ d : OrderedClusterDatum, ℝ → BlowupCoordinates m d)
    (s : ℝ) : Set Configuration :=
  {q | ∃ d : OrderedClusterDatum,
    RepresentsCoordinates m d (epsilon s) (h d (epsilon s)) q}

/-- The source contradiction argument, proved for an already constructed
actual local family. The main theorem below DISCHARGES that family input
by LocalBranch.allDataLocalBranches with only positive masses. -/
theorem eventually_all_solutions_are_branch_values {m : Masses}
    (hm : PositiveMasses m)
    (seed : ∀ d : OrderedClusterDatum, BlowupCoordinates m d)
    (eta : OrderedClusterDatum → ℝ)
    (N : ∀ d : OrderedClusterDatum, Set (BlowupCoordinates m d))
    (h : ∀ d : OrderedClusterDatum, ℝ → BlowupCoordinates m d)
    (hlocal : ∀ d, AnalyticLocalBranch m d (seed d) (eta d) (N d) (h d)) :
    CoverageSequence.EventuallyCovered m (branchConfigurations h) := by
  classical
  by_contra hnot
  obtain ⟨s, q, _hsbound, hs, hq⟩ :=
    CoverageSequence.counterexample_sequence m (branchConfigurations h) hnot
  obtain ⟨φ, _hφ, d, seed₀, coords, hseed₀, hsone, hεlim, hcoords,
      houter, hinner, _hcubic, _hdistances⟩ :=
    SeedLimitCandidate.seedLimitStatement_candidate m hm s q hs (fun ν => (hq ν).1)
  rcases hlocal d with ⟨hη, hNopen, hseedN, hseed, _han, _hzero, hphys⟩
  have hseedEq : seed₀ = seed d := (seed_existsUnique hm d).unique hseed₀ hseed
  have ht : Tendsto coords atTop (nhds (seed d)) := by
    rw [← hseedEq]
    exact coordinates_tendsto_seed hseed₀ hcoords houter hinner
  have hmem : ∀ᶠ ν in atTop, coords ν ∈ N d :=
    ht.eventually (hNopen.mem_nhds hseedN)
  have hsmall : ∀ᶠ ν in atTop, epsilon (s (φ ν)) < eta d :=
    hεlim.eventually_lt_const hη
  have hfalse : ∀ᶠ (_ν : ℕ) in atTop, False := by
    filter_upwards [hmem, hsmall] with ν hmem hsmall
    have hspos : 0 < s (φ ν) := (by norm_num : (0 : ℝ) < 1).trans (hsone ν)
    have hεpos := TwoScale.epsilon_pos hspos
    have hparameter : parameterFromEpsilon (epsilon (s (φ ν))) = s (φ ν) :=
      parameterFromEpsilon_epsilon hspos
    obtain ⟨_hbranchN, q₀, _hq₀sol, hq₀repr, hunique, _hcoordUnique, _hND⟩ :=
      hphys (epsilon (s (φ ν))) hεpos hsmall
    have hsol : IsSolution m (parameterFromEpsilon (epsilon (s (φ ν)))) (q (φ ν)) := by
      rw [hparameter]
      exact (hq (φ ν)).1
    have heq : q (φ ν) = q₀ := hunique (q (φ ν)) hsol
      ⟨coords ν, hmem, (hcoords ν).1⟩
    apply (hq (φ ν)).2
    refine ⟨d, ?_⟩
    rw [heq]
    exact hq₀repr
  obtain ⟨_ν, hFalse⟩ := hfalse.exists
  exact hFalse

end FourBody.Global

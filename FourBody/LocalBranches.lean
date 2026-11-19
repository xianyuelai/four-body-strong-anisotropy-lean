import FourBody.PhysicalBranchNondegeneracy

/-!
Literal Proposition 4.1 target assembled from the actual analytic IFT,
positive-distance rectangle, physical Q/T identities and original W derivative.
The final theorem has only the manuscript's positive-mass input. These modules
are STATIC proof candidates and do not constitute compiler acceptance.
-/

noncomputable section
open Filter Set Topology
namespace FourBody.LocalBranch

open BlowupAnalytic

theorem analyticLocalBranch_of_zeroRectangle {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d}
    (r : ZeroRectangle hm d seed) :
    AnalyticLocalBranch m d seed r.eta r.neighborhood r.branch := by
  refine ⟨r.eta_pos, r.neighborhood_open, r.seed_mem, r.seed_isSeed,
    r.branch_analytic, r.branch_zero, ?_⟩
  intro ε hε hη
  have hparam := positive_parameter_mem r hε hη
  have hmem := r.branch_mem ε hparam
  have hroot := r.branch_root ε hparam
  have hrepr := represents_physicalCoordinates ε (r.branch ε)
  refine ⟨hmem, physicalCoordinates ε (r.branch ε),
    physical_solution_of_zeroRectangle hm r hε hη (r.branch ε) hmem hroot,
    hrepr, ?_, ?_,
    originalNondegenerate_of_zeroRectangle hm r hε hη (r.branch ε) hmem⟩
  · intro q' hq' hrepresented
    obtain ⟨h', h'N, h'q⟩ := hrepresented
    have hqeq := (represents_iff_eq_physicalCoordinates ε h' q').mp h'q
    have hR : restrictedResidual m (parameterFromEpsilon ε)
        (coordinateQ m d ε h') = 0 := by
      apply Subtype.ext
      funext i
      change force m (physicalCoordinates ε h') i -
        anisotropy (parameterFromEpsilon ε) (physicalCoordinates ε h' i) = 0
      rw [← hqeq]
      exact sub_eq_zero.mpr (hq'.2 i)
    have hsep := (separated_of_uniformDistanceBound r.delta_pos
      (r.distances ε hparam h' h'N)).1
    have hF := (blowupResidual_zero_iff_restrictedResidual_zero hm hε h' hsep).mpr hR
    have hh' := (r.graph_exact ε hparam h' h'N).mp hF
    exact hqeq.trans (congrArg (physicalCoordinates ε) hh'.symm)
  · intro h' _ h'q
    exact represents_unique_coordinates hm (ne_of_gt hε) h'q hrepr

/-- The original datum-local existence statement. Neither F analyticity,
seed existence, a Jacobian formula/inverse nor a branch certificate is an
input. Their proof bodies occur in the preceding actual modules. -/
theorem allDataLocalBranches : AllDataLocalBranchesStatement := by
  intro m hm d
  obtain ⟨r⟩ := zeroRectangle_exists hm d
  exact ⟨seedCoordinates hm d, r.eta, r.neighborhood, r.branch,
    analyticLocalBranch_of_zeroRectangle hm r⟩

end FourBody.LocalBranch

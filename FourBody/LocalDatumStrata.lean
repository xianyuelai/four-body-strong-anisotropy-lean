import FourBody.AxisSeedStrata
import FourBody.MixedDatumStrata

/-!
# Exact local datum/axis/noncollinear equivalences

Frozen manuscript SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
Source Section 5 lines 718--724 and 726--734, using Section 4's fixed-N
local uniqueness. STATIC CANDIDATE; not compiled.

This is a local proof-composition lemma with its fixed-neighborhood
uniqueness premise exposed in full, on the actual original equation and
actual coordinate representation. The future genuinely proved local
branch theorem must supply that premise. No analytic interface, branch
existence, MainStatement, classification, counts or nondegeneracy theorem
is postulated. It does not yet assert an unconditional branch-family
stratification or a global classification theorem.
-/

noncomputable section
namespace FourBody

/-- Both directions of the actual strata, from only local fixed-N
uniqueness and the previously proved concrete seed/rectangle geometry. -/
theorem fixed_neighborhood_unique_solution_strata {m : Masses}
    (hm : PositiveMasses m) {d : OrderedClusterDatum} {ε γ A : ℝ}
    (hε : 0 < ε) (hs : 1 < parameterFromEpsilon ε) (hγ : 0 < γ)
    (seed : BlowupCoordinates m d) (hseed : IsSeed m d seed)
    (N : Set (BlowupCoordinates m d)) (hseedN : seed ∈ N)
    (h : BlowupCoordinates m d) (q : Configuration)
    (hr : RecoveryRectangle m d γ A h)
    (hq : RepresentsCoordinates m d ε h q)
    (hsol : IsSolution m (parameterFromEpsilon ε) q)
    (hunique : ∀ q' : Configuration,
      IsSolution m (parameterFromEpsilon ε) q' →
      (∃ h' : BlowupCoordinates m d, h' ∈ N ∧ RepresentsCoordinates m d ε h' q') → q' = q) :
    (OnXAxis q ↔ d.blocks.length = 1) ∧
      (OnYAxis q ↔ d.blocks.length = 4) ∧
      (¬Collinear q ↔ 1 < d.blocks.length ∧ d.blocks.length < 4) := by
  have ho := orderedByConfiguration_of_recoveryRectangle hm hγ hε hr hq
  have hxiff : OnXAxis q ↔ d.blocks.length = 1 := by
    constructor
    · exact onXAxis_blockCount_eq_one_of_orderedByConfiguration ho
    · intro hk
      exact (one_block_seed_identified_by_fixed_neighborhood_uniqueness
        hm hk hε seed hseed N hseedN q hunique).2
  have hyiff : OnYAxis q ↔ d.blocks.length = 4 := by
    constructor
    · exact onYAxis_blockCount_eq_four_of_orderedByConfiguration ho
    · intro hk
      exact (four_block_seed_identified_by_fixed_neighborhood_uniqueness
        hm hk ε seed hseed N hseedN q hunique).2
  refine ⟨hxiff, hyiff, ?_⟩
  constructor
  · intro hn
    have hkone : d.blocks.length ≠ 1 := by
      intro hk
      exact hn (onXAxis_collinear (hxiff.mpr hk))
    have hkfour : d.blocks.length ≠ 4 := by
      intro hk
      exact hn (onYAxis_collinear (hyiff.mpr hk))
    have hpos : 0 < d.blocks.length := d.blockCount_pos
    have hle : d.blocks.length ≤ 4 := d.blockCount_le_four
    constructor <;> omega
  · rintro ⟨hklo, hkhi⟩
    exact mixed_ordered_solution_noncollinear hm hs hsol ho hklo hkhi

/-- The original source-facing strata predicate is obtained from the
proved local equivalences, with the same physical q and actual datum. -/
theorem fixed_neighborhood_unique_solution_datumSolutionStrata {m : Masses}
    (hm : PositiveMasses m) {d : OrderedClusterDatum} {ε γ A : ℝ}
    (hε : 0 < ε) (hs : 1 < parameterFromEpsilon ε) (hγ : 0 < γ)
    (seed : BlowupCoordinates m d) (hseed : IsSeed m d seed)
    (N : Set (BlowupCoordinates m d)) (hseedN : seed ∈ N)
    (h : BlowupCoordinates m d) (q : Configuration)
    (hr : RecoveryRectangle m d γ A h)
    (hq : RepresentsCoordinates m d ε h q)
    (hsol : IsSolution m (parameterFromEpsilon ε) q)
    (hunique : ∀ q' : Configuration,
      IsSolution m (parameterFromEpsilon ε) q' →
      (∃ h' : BlowupCoordinates m d, h' ∈ N ∧ RepresentsCoordinates m d ε h' q') → q' = q) :
    DatumSolutionStrata d q := by
  have hsall := fixed_neighborhood_unique_solution_strata hm hε hs hγ
    seed hseed N hseedN h q hr hq hsol hunique
  exact ⟨hsall.1.symm, hsall.2.1.symm, hsall.2.2.symm⟩

end FourBody
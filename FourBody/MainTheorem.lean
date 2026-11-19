import FourBody.GlobalExhaustion
import FourBody.LocalDatumStrata
import FourBody.SolutionCountTransport

/-!
Frozen Pro v2 Theorem 1.1 and Section 5, SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

The only final mathematical hypothesis is positivity of the four fixed
original masses. One mass-dependent s0>1 and the SAME actual local
analytic coordinate family witness every conclusion at every s>s0.
The route uses the actual arbitrary-sequence limit, finite continuity
comparisons, physical datum recovery, fixed-N local uniqueness, exact
axis solutions and literal labelled solution equivalences.

Initially prepared as a proof candidate. Actual build/audit status is
recorded in strict receipts; this module alone does not attest
whole-paper acceptance.
Final whole-paper acceptance requires Root's final frozen-source,
semantic, dependency and kernel-verification records.
-/

noncomputable section
namespace FourBody.Global

/-- Eliminate the local existential physical value through its actual
Q-epsilon representation, keeping the original residual derivative. -/
theorem local_branch_physical_value {m : Masses} {d : OrderedClusterDatum}
    {seed : BlowupCoordinates m d} {eta : ℝ}
    {N : Set (BlowupCoordinates m d)} {h : ℝ → BlowupCoordinates m d}
    (hl : AnalyticLocalBranch m d seed eta N h) {ε : ℝ}
    (hε : 0 < ε) (hη : ε < eta) :
    IsSolution m (parameterFromEpsilon ε) (physicalCoordinates ε (h ε)) ∧
      OriginalNondegenerate m (parameterFromEpsilon ε) (physicalCoordinates ε (h ε)) ∧
      (∀ q' : Configuration, IsSolution m (parameterFromEpsilon ε) q' →
        (∃ z : BlowupCoordinates m d, z ∈ N ∧ RepresentsCoordinates m d ε z q') →
        q' = physicalCoordinates ε (h ε)) := by
  rcases hl with ⟨_hηpos, _hopen, _hseedN, _hseed, _han, _hzero, hphys⟩
  obtain ⟨_hmem, q, hsol, hrepr, hunique, _hcoordinateUnique, hND⟩ := hphys ε hε hη
  have heq := (represents_iff_eq_physicalCoordinates ε (h ε) q).mp hrepr
  rw [heq] at hsol hND hunique
  exact ⟨hsol, hND, hunique⟩

end FourBody.Global

namespace FourBody

open Global

/-- The frozen unconditional source-facing main statement. All branch,
limit, uniqueness, recovery, classification and counting inputs have
actual named proof dependencies, rather than assumed interfaces. -/
theorem mainTheorem : MainStatement := by
  classical
  intro m hm
  choose seed eta N h hlocal using (LocalBranch.allDataLocalBranches m hm)
  obtain ⟨ρ, hρ, _hρone, hρrecovery, hρfamily⟩ :=
    common_recovery_range hm seed eta N h hlocal
  obtain ⟨S, hcover⟩ :=
    eventually_all_solutions_are_branch_values hm seed eta N h hlocal
  let s₀ : ℝ := max S (thresholdFromRange ρ)
  have hs₀ : 1 < s₀ := (thresholdFromRange_gt_one ρ).trans_le (le_max_right _ _)
  refine ⟨s₀, hs₀, finrank_W hm, seed, eta, N, h, hlocal, ?_⟩
  intro s hs
  have hSl : S < s := (le_max_left _ _).trans_lt hs
  have hthreshold : thresholdFromRange ρ < s := (le_max_right _ _).trans_lt hs
  obtain ⟨hsone, hε, hερ, hparameter⟩ := thresholdFromRange_admissible hρ hthreshold
  have hη (d : OrderedClusterDatum) : epsilon s < eta d :=
    hερ.trans (hρfamily d).1
  have hcomparisons (d : OrderedClusterDatum) :
      SeedComparisonBounds hm d (h d (epsilon s)) := by
    apply (hρfamily d).2
    simpa only [abs_of_pos hε] using hερ
  have hrectangle (d : OrderedClusterDatum) :
      RecoveryRectangle m d (commonSeedGap hm) (commonSeedInnerBound hm)
        (h d (epsilon s)) := recoveryRectangle_of_seedComparisons hm (hcomparisons d)
  have hvalues (d : OrderedClusterDatum) :
      IsSolution m s (physicalCoordinates (epsilon s) (h d (epsilon s))) ∧
        OriginalNondegenerate m s (physicalCoordinates (epsilon s) (h d (epsilon s))) := by
    have hv := local_branch_physical_value (hlocal d) hε (hη d)
    rw [hparameter] at hv
    exact ⟨hv.1, hv.2.1⟩
  let b : OrderedClusterDatum → SolutionSpace m s := fun d =>
    ⟨physicalCoordinates (epsilon s) (h d (epsilon s)), (hvalues d).1⟩
  have hinjective : Function.Injective b := by
    intro d e heq
    apply actual_common_constants_determine_datum hm hε (hερ.trans hρrecovery)
      (hrectangle d) (hrectangle e)
    exact congrArg Subtype.val heq
  have hsurjective : Function.Surjective b := by
    intro q
    obtain ⟨d, hd⟩ := hcover s hSl q.val q.property
    refine ⟨d, Subtype.ext ?_⟩
    exact ((represents_iff_eq_physicalCoordinates (epsilon s) (h d (epsilon s)) q.val).mp hd).symm
  let e : OrderedClusterDatum ≃ SolutionSpace m s :=
    Equiv.ofBijective b ⟨hinjective, hsurjective⟩
  have hstrata (d : OrderedClusterDatum) : DatumSolutionStrata d (e d).val := by
    rcases hlocal d with ⟨_heta, _hopen, hseedN, hseed, _han, _hzero, _hphys⟩
    have hv := local_branch_physical_value (hlocal d) hε (hη d)
    have hparameterOne : 1 < parameterFromEpsilon (epsilon s) := by
      rw [hparameter]
      exact hsone
    exact fixed_neighborhood_unique_solution_datumSolutionStrata hm hε hparameterOne
      (commonSeedGap_positive hm) (seed d) hseed (N d) hseedN
      (h d (epsilon s)) (physicalCoordinates (epsilon s) (h d (epsilon s)))
      (hrectangle d) (represents_physicalCoordinates _ _) hv.1 hv.2.2
  refine ⟨exactSolutionCounts_of_datum_equivalence e hstrata, ?_, e, ?_⟩
  · intro q hq
    obtain ⟨d, hd⟩ := hsurjective ⟨q, hq⟩
    have heq : physicalCoordinates (epsilon s) (h d (epsilon s)) = q :=
      congrArg Subtype.val hd
    rw [← heq]
    exact (hvalues d).2
  · intro d
    refine ⟨hε, hη d, ?_, hstrata d⟩
    exact represents_physicalCoordinates (epsilon s) (h d (epsilon s))

/-- The count/nondegeneracy projection retains the single s0 and W=6. -/
theorem mainCountNondegeneracyTheorem : MainCountNondegeneracyStatement := by
  intro m hm
  obtain ⟨s₀, hs₀, hW, seed, eta, N, h, _hlocal, hmain⟩ := mainTheorem m hm
  refine ⟨s₀, hs₀, hW, ?_⟩
  intro s hs
  have hfull := hmain s hs
  exact ⟨hfull.1, hfull.2.1⟩

end FourBody

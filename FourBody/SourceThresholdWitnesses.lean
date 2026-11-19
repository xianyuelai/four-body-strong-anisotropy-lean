import FourBody.SourceFixedNeighborhoodCoverage
import FourBody.BranchRecoveryContinuity

/-!
Independent literal threshold witness candidate for frozen v2 654--706.
Raw manuscript SHA256 97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
This own-preparation file has not been staged, compiled, or kernel audited.
It explicitly preserves the same seed, fixed neighborhoods and branch h
while choosing eta below local, recovery, and genuine coverage thresholds.
All premises of the internal local-family lemmas are discharged here.
This corollary never supplies a hypothesis to Main or GlobalExhaustion.
-/

noncomputable section
namespace FourBody.SourceThresholdWitnesses
open Global SourceFixedNeighborhoodCoverage

theorem all_preceding_thresholds_same_family (m : Masses) (hm : PositiveMasses m) :
    ∃ η₁ ρ η₂ η : ℝ,
      0 < η₁ ∧ η₁ < 1 ∧
      0 < ρ ∧ ρ < 1 ∧
      ρ < recoveryParameterBound (commonSeedGap hm) (commonSeedInnerBound hm) ∧
      ρ < η₁ ∧
      0 < η₂ ∧ η₂ ≤ η₁ ∧
      0 < η ∧ η < η₁ ∧ η < ρ ∧ η < η₂ ∧ η < 1 ∧
      1 < parameterFromEpsilon η ∧
      ∃ seed : ∀ d : OrderedClusterDatum, BlowupCoordinates m d,
      ∃ N : ∀ d : OrderedClusterDatum, Set (BlowupCoordinates m d),
      ∃ h : ∀ d : OrderedClusterDatum, ℝ → BlowupCoordinates m d,
        (∀ d, AnalyticLocalBranch m d (seed d) η₁ (N d) (h d)) ∧
        (∀ d, AnalyticLocalBranch m d (seed d) η (N d) (h d)) ∧
        (∀ d : OrderedClusterDatum, ∀ ε : ℝ, |ε| < ρ →
          SeedComparisonBounds hm d (h d ε)) ∧
        (∀ ε : ℝ, 0 < ε → ε < η₂ →
          ∀ q : Configuration, IsSolution m (parameterFromEpsilon ε) q →
            ∃ d : OrderedClusterDatum, ∃ z : BlowupCoordinates m d,
              z ∈ N d ∧ RepresentsCoordinates m d ε z q) ∧
        ∀ s : ℝ, parameterFromEpsilon η < s →
          ExactSolutionCounts m s ∧ AllSolutionsNondegenerate m s ∧
          ∃ e : OrderedClusterDatum ≃ SolutionSpace m s,
            ∀ d : OrderedClusterDatum,
              0 < epsilon s ∧ epsilon s < η ∧
              RepresentsCoordinates m d (epsilon s)
                (h d (epsilon s)) (e d).val ∧
              DatumSolutionStrata d (e d).val := by
  obtain ⟨η₁, hη₁, hη₁one, _hs₁, _hW, seed, N, h, hlocal, hmain⟩ :=
    sourceCommonThreshold m hm
  obtain ⟨ρ, hρ, hρone, hρrecovery, hρfamily⟩ :=
    common_recovery_range hm seed (fun _ => η₁) N h hlocal
  obtain ⟨η₂, hη₂, hη₂le, _hη₂one, _hη₂family, hcoverage⟩ :=
    eventual_fixed_neighborhood_epsilon_coverage
      hm seed (fun _ => η₁) N h hlocal η₁ hη₁
  let r : ℝ := min η₁ (min ρ η₂)
  have hr : 0 < r := lt_min hη₁ (lt_min hρ hη₂)
  let η : ℝ := r / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηr : η < r := by dsimp [η]; linarith
  have hrη₁ : r ≤ η₁ := min_le_left _ _
  have hrρ : r ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hrη₂ : r ≤ η₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hηη₁ : η < η₁ := hηr.trans_le hrη₁
  have hηρ : η < ρ := hηr.trans_le hrρ
  have hηη₂ : η < η₂ := hηr.trans_le hrη₂
  have hηone : η < 1 := hηη₁.trans hη₁one
  have hsη : 1 < parameterFromEpsilon η := by
    have hlt := parameterFromEpsilon_lt_of_lt hη hηone
    simpa only [parameterFromEpsilon, one_pow, inv_one] using hlt
  have hρ₁ : ρ < η₁ :=
    (hρfamily (datumEncoding.symm (Equiv.refl Label, fun _ => false))).1
  have hbranches (d : OrderedClusterDatum) :
      AnalyticLocalBranch m d (seed d) η (N d) (h d) :=
    analyticLocalBranch_restrict (hlocal d) hη hηη₁.le
  refine ⟨η₁, ρ, η₂, η, hη₁, hη₁one, hρ, hρone, hρrecovery,
    hρ₁, hη₂, hη₂le, hη, hηη₁, hηρ, hηη₂, hηone, hsη,
    seed, N, h, hlocal, hbranches, ?_, hcoverage, ?_⟩
  · intro d ε hε
    exact (hρfamily d).2 ε hε
  · intro s hs
    have hspos : 0 < s := by linarith
    have hslarge : parameterFromEpsilon η₁ < s :=
      (parameterFromEpsilon_lt_of_lt hη hηη₁).trans hs
    have hsmall : epsilon s < η := epsilon_lt_of_parameter_gt hspos hη hs
    obtain ⟨hcount, hND, e, he⟩ := hmain s hslarge
    refine ⟨hcount, hND, e, ?_⟩
    intro d
    exact ⟨(he d).1, hsmall, (he d).2.2⟩

end FourBody.SourceThresholdWitnesses

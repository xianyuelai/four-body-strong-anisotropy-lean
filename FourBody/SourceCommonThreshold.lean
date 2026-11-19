import FourBody.MainTheorem

/-!
Source Section 5's literal common analytic epsilon range and inverse-cube
threshold. This is a corollary of the unconditional main theorem, with no
feedback into that theorem's proof. All original branch functions, fixed
neighborhoods, physical solutions and datum equivalences are retained.

Initially prepared as a proof candidate. Actual build/audit status is
recorded in strict receipts; this module alone does not attest
whole-paper acceptance.
-/

noncomputable section
namespace FourBody

/-- Genuine restriction of the same analytic branch to a smaller signed
epsilon interval. Physical uniqueness and the original W derivative are
retained because the same fixed N and branch function occur throughout. -/
theorem analyticLocalBranch_restrict {m : Masses} {d : OrderedClusterDatum}
    {seed : BlowupCoordinates m d} {η η' : ℝ}
    {N : Set (BlowupCoordinates m d)} {h : ℝ → BlowupCoordinates m d}
    (hl : AnalyticLocalBranch m d seed η N h) (hη' : 0 < η') (hle : η' ≤ η) :
    AnalyticLocalBranch m d seed η' N h := by
  rcases hl with ⟨_hη, hN, hseedN, hs, han, hzero, hphysical⟩
  refine ⟨hη', hN, hseedN, hs, han.mono ?_, hzero, ?_⟩
  · intro ε hε
    exact ⟨(neg_le_neg hle).trans_lt hε.1, hε.2.trans_le hle⟩
  · intro ε hε hsmall
    exact hphysical ε hε (hsmall.trans_le hle)

/-- The source's common η and s₀=η⁻³. The inverse cube is the existing
literal parameterFromEpsilon definition (η^3)⁻¹. The same h/N/seed
family and actual physical equivalences witness every s>s₀. -/
def SourceCommonThresholdStatement : Prop :=
  ∀ m : Masses, PositiveMasses m →
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ 1 < parameterFromEpsilon η ∧
      Module.finrank ℝ (W m) = 6 ∧
      ∃ seed : ∀ d : OrderedClusterDatum, BlowupCoordinates m d,
      ∃ N : ∀ d : OrderedClusterDatum, Set (BlowupCoordinates m d),
      ∃ h : ∀ d : OrderedClusterDatum, ℝ → BlowupCoordinates m d,
        (∀ d, AnalyticLocalBranch m d (seed d) η (N d) (h d)) ∧
        ∀ s : ℝ, parameterFromEpsilon η < s →
          ExactSolutionCounts m s ∧ AllSolutionsNondegenerate m s ∧
          ∃ e : OrderedClusterDatum ≃ SolutionSpace m s,
            ∀ d : OrderedClusterDatum,
              0 < epsilon s ∧ epsilon s < η ∧
              RepresentsCoordinates m d (epsilon s)
                (h d (epsilon s)) (e d).val ∧
              DatumSolutionStrata d (e d).val

/-- Unconditional source-facing common threshold corollary. Taking
S=s₀+1 lets the already proved main family at S show η=epsilon S is
strictly inside every local range; all branches are genuinely restricted. -/
theorem sourceCommonThreshold : SourceCommonThresholdStatement := by
  intro m hm
  obtain ⟨s₀, hs₀, hW, seed, oldEta, N, h, hlocal, hmain⟩ := mainTheorem m hm
  let S : ℝ := s₀ + 1
  let η : ℝ := epsilon S
  have hs₀S : s₀ < S := by dsimp [S]; linarith
  have hSone : 1 < S := hs₀.trans hs₀S
  have hSpos : 0 < S := (by norm_num : (0 : ℝ) < 1).trans hSone
  have hη : 0 < η := TwoScale.epsilon_pos hSpos
  have hparameter : parameterFromEpsilon η = S := parameterFromEpsilon_epsilon hSpos
  have hηone : η < 1 := by
    apply epsilon_lt_of_parameter_gt hSpos (by norm_num : (0 : ℝ) < 1)
    simpa only [parameterFromEpsilon, one_pow, inv_one] using hSone
  obtain ⟨_hcountS, _hNDS, _eS, heS⟩ := hmain S hs₀S
  have hηle (d : OrderedClusterDatum) : η ≤ oldEta d := (heS d).2.1.le
  have hbranches (d : OrderedClusterDatum) :
      AnalyticLocalBranch m d (seed d) η (N d) (h d) :=
    analyticLocalBranch_restrict (hlocal d) hη (hηle d)
  refine ⟨η, hη, hηone, ?_, hW, seed, N, h, hbranches, ?_⟩
  · rw [hparameter]
    exact hSone
  · intro s hs
    have hSs : S < s := by simpa only [hparameter] using hs
    have hslarge : s₀ < s := hs₀S.trans hSs
    have hspos : 0 < s := hSpos.trans hSs
    have hsmall : epsilon s < η := epsilon_lt_of_parameter_gt hspos hη hs
    obtain ⟨hcount, hND, e, he⟩ := hmain s hslarge
    refine ⟨hcount, hND, e, ?_⟩
    intro d
    exact ⟨(he d).1, hsmall, (he d).2.2⟩

end FourBody

import FourBody.GlobalSeedConvergence
import FourBody.LocalBranches
import FourBody.RecoveryBounds
import FourBody.FiniteBranchRange
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FunProp

/-!
Frozen Pro v2 Section 5, lines 641--649 and 677--691, SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

The common comparisons are derived from actual analytic branch continuity.
Only finite coordinate comparisons occur in the intermediate hypotheses.
The final main proof obtains its local branch witnesses from the proved
allDataLocalBranches declaration.

Initially prepared as a proof candidate. Actual build/audit status is
recorded in strict receipts; this module alone does not attest
whole-paper acceptance.
-/

noncomputable section
open Filter Topology
namespace FourBody.Global

theorem continuous_outerY {m : Masses} {d : OrderedClusterDatum} (a : BlockIndex d) :
    Continuous (fun z : BlowupCoordinates m d => outerY z a) := by
  unfold outerY
  fun_prop

theorem continuous_innerU {m : Masses} {d : OrderedClusterDatum} (i : Label) :
    Continuous (fun z : BlowupCoordinates m d => innerU z i) := by
  unfold innerU
  fun_prop

theorem continuous_innerV {m : Masses} {d : OrderedClusterDatum} (i : Label) :
    Continuous (fun z : BlowupCoordinates m d => innerV z i) := by
  unfold innerV
  fun_prop

/-- Finitely many strict continuity comparisons provide exactly the raw
seed deviations needed by the physical recovery proof. -/
theorem seedComparisonBounds_eventually {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {h : ℝ → BlowupCoordinates m d}
    (hc : ContinuousAt h 0) (hzero : h 0 = seedCoordinates hm d) :
    ∀ᶠ ε in nhds (0 : ℝ), SeedComparisonBounds hm d (h ε) := by
  have houter : ∀ᶠ ε in nhds (0 : ℝ), ∀ a : BlockIndex d,
      |outerY (h ε) a - outerY (seedCoordinates hm d) a| ≤ commonSeedGap hm / 4 := by
    apply eventually_all.mpr
    intro a
    have hc' : ContinuousAt
        (fun ε : ℝ => |outerY (h ε) a - outerY (seedCoordinates hm d) a|) 0 :=
      (((continuous_outerY a).continuousAt.comp hc).sub continuousAt_const).abs
    have ht : Tendsto (fun ε => |outerY (h ε) a - outerY (seedCoordinates hm d) a|)
        (nhds 0) (nhds 0) := by
      simpa only [hzero, sub_self, abs_zero] using hc'.tendsto
    have hb : 0 < commonSeedGap hm / 4 := div_pos (commonSeedGap_positive hm) (by norm_num)
    exact (ht.eventually_lt_const hb).mono (fun _ he => he.le)
  have hu : ∀ᶠ ε in nhds (0 : ℝ), ∀ i : Label,
      |innerU (h ε) i - innerU (seedCoordinates hm d) i| ≤ 1 := by
    apply eventually_all.mpr
    intro i
    have hc' : ContinuousAt
        (fun ε : ℝ => |innerU (h ε) i - innerU (seedCoordinates hm d) i|) 0 :=
      (((continuous_innerU i).continuousAt.comp hc).sub continuousAt_const).abs
    have ht : Tendsto (fun ε => |innerU (h ε) i - innerU (seedCoordinates hm d) i|)
        (nhds 0) (nhds 0) := by
      simpa only [hzero, sub_self, abs_zero] using hc'.tendsto
    exact (ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).mono (fun _ he => he.le)
  have hv : ∀ᶠ ε in nhds (0 : ℝ), ∀ i : Label,
      |innerV (h ε) i - innerV (seedCoordinates hm d) i| ≤ 1 := by
    apply eventually_all.mpr
    intro i
    have hc' : ContinuousAt
        (fun ε : ℝ => |innerV (h ε) i - innerV (seedCoordinates hm d) i|) 0 :=
      (((continuous_innerV i).continuousAt.comp hc).sub continuousAt_const).abs
    have ht : Tendsto (fun ε => |innerV (h ε) i - innerV (seedCoordinates hm d) i|)
        (nhds 0) (nhds 0) := by
      simpa only [hzero, sub_self, abs_zero] using hc'.tendsto
    exact (ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).mono (fun _ he => he.le)
  have hgap : ∀ᶠ ε in nhds (0 : ℝ),
      ∀ (a : BlockIndex d) (i j : InternalIndex d a), i < j →
      |(innerU (h ε) (internalLabel d a j) - innerU (h ε) (internalLabel d a i)) -
        (innerU (seedCoordinates hm d) (internalLabel d a j) -
          innerU (seedCoordinates hm d) (internalLabel d a i))| <
        (innerU (seedCoordinates hm d) (internalLabel d a j) -
          innerU (seedCoordinates hm d) (internalLabel d a i)) / 2 := by
    apply eventually_all.mpr
    intro a
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i < j
    · have hc' : ContinuousAt
          (fun ε : ℝ => |(innerU (h ε) (internalLabel d a j) -
            innerU (h ε) (internalLabel d a i)) -
              (innerU (seedCoordinates hm d) (internalLabel d a j) -
                innerU (seedCoordinates hm d) (internalLabel d a i))|) 0 :=
        ((((continuous_innerU (internalLabel d a j)).continuousAt.comp hc).sub
          ((continuous_innerU (internalLabel d a i)).continuousAt.comp hc)).sub
          continuousAt_const).abs
      have ht : Tendsto
          (fun ε => |(innerU (h ε) (internalLabel d a j) -
            innerU (h ε) (internalLabel d a i)) -
              (innerU (seedCoordinates hm d) (internalLabel d a j) -
                innerU (seedCoordinates hm d) (internalLabel d a i))|)
          (nhds 0) (nhds 0) := by
        simpa only [hzero, sub_self, abs_zero] using hc'.tendsto
      have hs := ((seedCoordinates_isSeed hm d).2.2.2.2 a).1 hij
      have hp : 0 < (innerU (seedCoordinates hm d) (internalLabel d a j) -
          innerU (seedCoordinates hm d) (internalLabel d a i)) / 2 := by linarith
      exact (ht.eventually_lt_const hp).mono (fun _ he _ => he)
    · exact Eventually.of_forall (fun _ hlt => (hij hlt).elim)
  filter_upwards [houter, hu, hv, hgap] with ε houter hu hv hgap
  exact ⟨houter, hu, hv, hgap⟩

/-- A single mass-dependent positive interval simultaneously retains
analytic branch existence, the actual seed comparisons and the two
literal Section 5 recovery inequalities for every one of the 192 data. -/
theorem common_recovery_range {m : Masses} (hm : PositiveMasses m)
    (seed : ∀ d : OrderedClusterDatum, BlowupCoordinates m d)
    (eta : OrderedClusterDatum → ℝ)
    (N : ∀ d : OrderedClusterDatum, Set (BlowupCoordinates m d))
    (h : ∀ d : OrderedClusterDatum, ℝ → BlowupCoordinates m d)
    (hlocal : ∀ d, AnalyticLocalBranch m d (seed d) (eta d) (N d) (h d)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ρ < recoveryParameterBound (commonSeedGap hm) (commonSeedInnerBound hm) ∧
      ∀ d : OrderedClusterDatum, ρ < eta d ∧
        ∀ ε : ℝ, |ε| < ρ → SeedComparisonBounds hm d (h d ε) := by
  classical
  have hnear (d : OrderedClusterDatum) :
      ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, |ε| < κ → SeedComparisonBounds hm d (h d ε) := by
    rcases hlocal d with ⟨hη, _hopen, _hmem, hs, han, hzero, _hphys⟩
    have hc : ContinuousAt (h d) 0 :=
      (han 0 ⟨neg_lt_zero.mpr hη, hη⟩).continuousAt
    have hzero' : h d 0 = seedCoordinates hm d := hzero.trans (seed_eq_canonical hm hs)
    obtain ⟨κ, hκ, hball⟩ := Metric.eventually_nhds_iff_ball.mp
      (seedComparisonBounds_eventually hm hc hzero')
    refine ⟨κ, hκ, ?_⟩
    intro ε hε
    apply hball ε
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hε
  choose κ hκ hκnear using hnear
  obtain ⟨ρ₀, hρ₀, hρ₀one, hρ₀all⟩ := finitePositiveCommonRange
    (fun d => min (eta d) (κ d)) (fun d => lt_min (hlocal d).1 (hκ d))
  let B := recoveryParameterBound (commonSeedGap hm) (commonSeedInnerBound hm)
  have hB : 0 < B := recoveryParameterBound_pos (commonSeedGap_positive hm)
    (commonSeedInnerBound_ge_one hm)
  let ρ : ℝ := min ρ₀ (B / 2)
  have hρ : 0 < ρ := lt_min hρ₀ (half_pos hB)
  have hρle : ρ ≤ ρ₀ := min_le_left _ _
  refine ⟨ρ, hρ, hρle.trans_lt hρ₀one, ?_, ?_⟩
  · have hhalf : B / 2 < B := by linarith
    exact (min_le_right _ _).trans_lt hhalf
  · intro d
    have hηd : ρ₀ < eta d := (hρ₀all d).trans_le (min_le_left _ _)
    have hκd : ρ₀ < κ d := (hρ₀all d).trans_le (min_le_right _ _)
    refine ⟨hρle.trans_lt hηd, ?_⟩
    intro ε hε
    exact hκnear d ε ((hε.trans_le hρle).trans hκd)

end FourBody.Global

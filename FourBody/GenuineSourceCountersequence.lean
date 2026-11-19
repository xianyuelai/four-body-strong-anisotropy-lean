import FourBody.CoverageSequence
import FourBody.ParameterThreshold
import FourBody.SequenceStart
import Mathlib.Algebra.Order.Field.Basic

/-!
# Literal small-epsilon counterexample choice in Pro v2 Section 5

Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
Source lines 665--670, baseline obligations S5-U03/S5-U04.

STATIC ONLY: this supplement is outside the formal project and has not
been elaborated. All epsilon convergence and inverse-cube identities are
derived from the actual selected real parameters, never assumed.
Index zero is handled by 1/(nu+1); the literal 1/nu bound is recovered
for nu >= 1. The input family may be the actual set of configurations
represented in any fixed local neighborhood, or the physical branch
value set. A separate local uniqueness application identifies those two
coverage formulations on their common positive parameter range.
-/

noncomputable section
open Filter

namespace FourBody.GenuineSourceCountersequence

/-- Every finite-index reciprocal used as a real epsilon cutoff is positive. -/
theorem successor_reciprocal_pos (ν : ℕ) : 0 < ((ν : ℝ) + 1)⁻¹ := by
  positivity

/-- The exact real cutoff used before choosing an uncovered original solution.
Both small-epsilon constraints and the unbounded real-parameter constraint
are imposed simultaneously, without assuming any conclusion about the
subsequent actual solutions or limiting seeds. -/
def sourceCutoff (η : ℝ) (ν : ℕ) : ℝ :=
  max (thresholdFromRange η)
    (max (thresholdFromRange (((ν : ℝ) + 1)⁻¹)) ((ν : ℝ) + 1))

/-- Complete source-facing countersequence with actual original equations.
No positive-mass hypothesis is needed for this elementary negation/choice
step. Fixed positive masses enter only when Proposition 3.2 is applied. -/
theorem genuineSourceCountersequence (m : Masses)
    (family : ℝ → Set Configuration) (η : ℝ) (hη : 0 < η)
    (hnot : ¬ CoverageSequence.EventuallyCovered m family) :
    ∃ s : ℕ → ℝ, ∃ q : ℕ → Configuration,
      (∀ ν : ℕ, sourceCutoff η ν < s ν) ∧
      Tendsto s atTop atTop ∧
      Tendsto (fun ν => epsilon (s ν)) atTop (nhds 0) ∧
      (∀ ν : ℕ,
        1 < s ν ∧
        IsSolution m (s ν) (q ν) ∧ q ν ∉ family (s ν) ∧
        parameterFromEpsilon (epsilon (s ν)) = s ν ∧
        0 < epsilon (s ν) ∧
        epsilon (s ν) < min η (((ν : ℝ) + 1)⁻¹)) ∧
      (∀ ν : ℕ, 1 ≤ ν →
        epsilon (s ν) < min η ((ν : ℝ)⁻¹)) := by
  classical
  have hex (ν : ℕ) :=
    CoverageSequence.uncovered_above m family hnot (sourceCutoff η ν)
  choose s hs q hsolution hmissing using hex
  have hsη (ν : ℕ) : thresholdFromRange η < s ν :=
    (le_max_left _ _).trans_lt (hs ν)
  have hsinv (ν : ℕ) : thresholdFromRange (((ν : ℝ) + 1)⁻¹) < s ν :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt (hs ν)
  have hsnatural (ν : ℕ) : (ν : ℝ) + 1 < s ν :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt (hs ν)
  have hinfinity : Tendsto s atTop atTop := by
    apply tendsto_atTop_mono (fun ν : ℕ => show (ν : ℝ) ≤ s ν by
      linarith [hsnatural ν])
    exact tendsto_natCast_atTop_atTop
  have hadmissible (ν : ℕ) := thresholdFromRange_admissible hη (hsη ν)
  have hreciprocal (ν : ℕ) := thresholdFromRange_admissible
    (successor_reciprocal_pos ν) (hsinv ν)
  refine ⟨s, q, hs, hinfinity, SequenceStart.epsilon_tendsto_zero hinfinity, ?_, ?_⟩
  · intro ν
    exact ⟨(hadmissible ν).1, hsolution ν, hmissing ν,
      (hadmissible ν).2.2.2, (hadmissible ν).2.1,
      lt_min (hadmissible ν).2.2.1 (hreciprocal ν).2.2.1⟩
  · intro ν hν
    have hνpos : 0 < (ν : ℝ) := by
      have hνnat : 0 < ν := lt_of_lt_of_le Nat.zero_lt_one hν
      exact_mod_cast hνnat
    have hinv : ((ν : ℝ) + 1)⁻¹ ≤ (ν : ℝ)⁻¹ :=
      (inv_le_inv₀ (by linarith : 0 < (ν : ℝ) + 1) hνpos).mpr (by linarith)
    exact lt_min (hadmissible ν).2.2.1 ((hreciprocal ν).2.2.1.trans_le hinv)

end FourBody.GenuineSourceCountersequence

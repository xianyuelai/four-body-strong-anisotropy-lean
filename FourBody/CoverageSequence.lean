import FourBody.Geometry
import Mathlib.Topology.Order.Real
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
The real counterexample sequence used in v2 Section 5, lines 640--655.
This supplies actual original collision-free solutions at parameters going
to +infinity if eventual coverage fails. It does not assume, or prove,
the missing seed-limit or eventual-coverage theorem.
-/
noncomputable section
namespace FourBody.CoverageSequence
open Filter

def EventuallyCovered (m : Masses) (family : ℝ → Set Configuration) : Prop :=
  ∃ S : ℝ, ∀ s : ℝ, S < s → ∀ q : Configuration, IsSolution m s q → q ∈ family s

theorem uncovered_above (m : Masses) (family : ℝ → Set Configuration)
    (h : ¬ EventuallyCovered m family) (S : ℝ) :
    ∃ s : ℝ, S < s ∧ ∃ q : Configuration, IsSolution m s q ∧ q ∉ family s := by
  classical
  unfold EventuallyCovered at h
  push Not at h
  exact h S

/-- An unbounded sequence of genuine original solutions. The lower bound
uses ν+1, so no reciprocal or accidental index-zero exception is hidden. -/
theorem counterexample_sequence (m : Masses) (family : ℝ → Set Configuration)
    (h : ¬ EventuallyCovered m family) :
    ∃ s : ℕ → ℝ, ∃ q : ℕ → Configuration,
      (∀ ν : ℕ, (ν : ℝ) + 1 < s ν) ∧
      Tendsto s atTop atTop ∧
      (∀ ν, IsSolution m (s ν) (q ν) ∧ q ν ∉ family (s ν)) := by
  classical
  have hc (ν : ℕ) := uncovered_above m family h ((ν : ℝ) + 1)
  choose s hs q hsol hnot using hc
  refine ⟨s, q, hs, ?_, fun ν => ⟨hsol ν, hnot ν⟩⟩
  apply tendsto_atTop_mono (fun (ν : ℕ) => show (ν : ℝ) ≤ s ν by linarith [hs ν])
  exact tendsto_natCast_atTop_atTop

end FourBody.CoverageSequence

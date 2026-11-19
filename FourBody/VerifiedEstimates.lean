import FourBody.Diameter
import FourBody.StatementDiameterBridge
import FourBody.TwoScaleEstimates

/-!
Source-facing forms of Lemma 2.1 and Proposition 2.2.
The statements quantify over all original solutions and contain only the
source hypotheses. All estimates come from the actual physical proofs.
This new wrapper awaits actual strict compilation; no main theorem follows.
-/

noncomputable section
namespace FourBody

theorem diameterEstimateStatement : DiameterEstimateStatement := by
  intro m hm s hs q hq
  rw [actualCoordinateDiameter_eq_sorted q 0, actualCoordinateDiameter_eq_sorted q 1]
  exact ⟨diameter_x hm hs hq, diameter_y hm hs hq⟩

/-- The mass vector is fixed before choosing the three constants. -/
theorem twoScaleEstimateStatement :
    ∀ m : Masses, PositiveMasses m →
      ∃ c₀ c₁ C : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ 0 < C ∧
        ∀ s : ℝ, 1 ≤ s →
          ∀ q : Configuration, IsSolution m s q →
            ∀ i j : Label, i ≠ j →
              c₀ * epsilon s ≤ dist (q i) (q j) ∧
                (dist (q i) (q j) < C * epsilon s ∨ c₁ ≤ dist (q i) (q j)) := by
  intro m hm
  have hpos := (ScaleConstants.constants_positive m hm).2
  refine ⟨ScaleConstants.c₀ m, ScaleConstants.c₁ m, ScaleConstants.C m,
    hpos.1, hpos.2.1, hpos.2.2, ?_⟩
  intro s hs q hq i j hij
  exact TwoScale.twoScaleEstimates m hm hs hq i j hij

end FourBody

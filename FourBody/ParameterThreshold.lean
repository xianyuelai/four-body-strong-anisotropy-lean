import FourBody.TwoScaleEstimates

/-!
The exact s/epsilon interval correspondence used in v2 Section 5.
A positive range is allowed to depend on the fixed masses. No mass-uniform
range or finiteness for all parameters is asserted.

Initially prepared as a proof candidate. Actual build/audit status is
recorded in strict receipts; this module alone does not attest
whole-paper acceptance.
-/

noncomputable section
namespace FourBody

theorem parameterFromEpsilon_epsilon {s : ℝ} (hs : 0 < s) :
    parameterFromEpsilon (epsilon s) = s := by
  rw [parameterFromEpsilon, TwoScale.epsilon_cube hs, inv_inv]

theorem epsilon_lt_of_parameter_gt {s eta : ℝ} (hs : 0 < s) (heta : 0 < eta)
    (hlarge : parameterFromEpsilon eta < s) : epsilon s < eta := by
  have hcube : 0 < eta ^ 3 := pow_pos heta 3
  have hmul : 1 < eta ^ 3 * s := by
    apply (inv_lt_iff_one_lt_mul₀' hcube).mp
    exact hlarge
  have hsmall : epsilon s ^ 3 < eta ^ 3 := by
    rw [TwoScale.epsilon_cube hs]
    apply (inv_lt_iff_one_lt_mul₀' hs).mpr
    simpa only [mul_comm] using hmul
  by_contra hnot
  exact not_le_of_gt hsmall (pow_le_pow_left₀ heta.le (le_of_not_gt hnot) 3)

/-- One concrete conversion from a positive local range to an s-threshold.
The extra constant 2 supplies the paper's strict s0>1 without weakening the
eventual conclusion or introducing a uniform range hypothesis. -/
def thresholdFromRange (eta : ℝ) : ℝ := max 2 (parameterFromEpsilon eta)

theorem thresholdFromRange_gt_one (eta : ℝ) : 1 < thresholdFromRange eta := by
  exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)

theorem thresholdFromRange_admissible {eta s : ℝ} (heta : 0 < eta)
    (hs : thresholdFromRange eta < s) :
    1 < s ∧ 0 < epsilon s ∧ epsilon s < eta ∧
      parameterFromEpsilon (epsilon s) = s := by
  have hsone : 1 < s := (thresholdFromRange_gt_one eta).trans hs
  have hspos : 0 < s := (by norm_num : (0 : ℝ) < 1).trans hsone
  have hlarge : parameterFromEpsilon eta < s := (le_max_right _ _).trans_lt hs
  exact ⟨hsone, TwoScale.epsilon_pos hspos,
    epsilon_lt_of_parameter_gt hspos heta hlarge, parameterFromEpsilon_epsilon hspos⟩

end FourBody

import FourBody.ScaleConstants
import FourBody.ClusterWidth
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Independent STATIC candidate supplement; no Lean/Lake/checker acceptance.
Source: original v2 four_body_strong_anisotropy_pro_v2.tex, SHA256
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
Source-facing obligations: S2-U20 (four positive masses and source constants),
S2-U24 (the equality in eq:external-smallness, source line 314), and
S2-U27 (the sharp sqrt(3)*r/2 vertical separation, source lines 328–330).
All proofs use the actual definitions imported from the current project.
This file is confined to the preparation directory and is not a formal
project amendment, a coverage amendment, or a successful build receipt.
-/

set_option autoImplicit false
set_option warningAsError true
noncomputable section
open scoped BigOperators

namespace FourBody.SourceFaithfulConstantsWidth

/-- Four actual labeled masses contribute four copies of the true minimum.
No positivity assumption is needed for this finite minimum inequality. -/
theorem four_mul_minimumMass_le_totalMass (m : Masses) :
    4 * ScaleConstants.minimumMass m ≤ totalMass m := by
  have hsum :
      (∑ i : Label, ScaleConstants.minimumMass m) ≤ ∑ i : Label, m i :=
    Finset.sum_le_sum (fun i _ => ScaleConstants.minimumMass_le m i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, totalMass] using hsum

/-- The literal equality printed in v2 eq:external-smallness.
This is distinct from the already proved upper bound with exterior mass. -/
theorem source_external_smallness_constant_exact
    (m : Masses) (hm : PositiveMasses m) :
    16 * totalMass m / ScaleConstants.T m ^ 3 =
      ScaleConstants.minimumMass m / 12 := by
  rw [ScaleConstants.T_cube m hm]
  have hmin : ScaleConstants.minimumMass m ≠ 0 :=
    ne_of_gt (ScaleConstants.minimumMass_pos m hm)
  have hmass : totalMass m ≠ 0 := ne_of_gt (totalMass_pos hm)
  field_simp [hmin, hmass]; ring

/-- A radius cancellation written with the source's full mass, before its
exact equality is used. Both nonzero factors come from physical positivity. -/
theorem source_external_smallness_constant_exact_scaled
    (m : Masses) (hm : PositiveMasses m) {r : ℝ} (hr : 0 < r) :
    (16 * totalMass m / (ScaleConstants.T m * r) ^ 3) * r ^ 3 =
      ScaleConstants.minimumMass m / 12 := by
  have hc :
      (16 * totalMass m / (ScaleConstants.T m * r) ^ 3) * r ^ 3 =
        16 * totalMass m / ScaleConstants.T m ^ 3 := by
    field_simp [ne_of_gt hr, ne_of_gt (ScaleConstants.T_pos m hm)]
  rw [hc]
  exact source_external_smallness_constant_exact m hm

/-- The complete typed numerical chain in source eq:external-smallness,
combining the existing exterior estimate with the literal source equality. -/
theorem source_external_smallness_chain
    (m : Masses) (hm : PositiveMasses m) {outside r : ℝ}
    (houtside : outside ≤ totalMass m) (hr : 0 < r) :
    (16 * outside / (ScaleConstants.T m * r) ^ 3) * r ^ 3 ≤
        16 * totalMass m / ScaleConstants.T m ^ 3 ∧
      16 * totalMass m / ScaleConstants.T m ^ 3 =
        ScaleConstants.minimumMass m / 12 := by
  have he := source_external_smallness_constant_exact m hm
  exact ⟨(ScaleConstants.exterior_smallness m hm houtside hr).trans_eq he.symm, he⟩

/-- The source's sharp Pythagorean estimate, rather than its later r/2
weakening. The norm, axes, and distance are the genuine Euclidean ones. -/
theorem vertical_separation_sqrt_three_of_horizontal_le_half
    (p z : Point) {r : ℝ} (hr : 0 < r) (hdist : dist p z = r)
    (hx : |p 0 - z 0| ≤ r / 2) :
    Real.sqrt 3 * r / 2 ≤ |p 1 - z 1| := by
  have hySq := vertical_separation_sq_of_horizontal_le_half p z hdist hx
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hleft : 0 ≤ Real.sqrt 3 * r / 2 := by positivity
  have hleftSq : (Real.sqrt 3 * r / 2) ^ 2 = 3 * r ^ 2 / 4 := by
    rw [div_pow, mul_pow, hs]
    norm_num
  have hsquares : (Real.sqrt 3 * r / 2) ^ 2 ≤ |p 1 - z 1| ^ 2 := by
    rw [hleftSq, sq_abs]
    nlinarith
  exact (sq_le_sq₀ hleft (abs_nonneg _)).mp hsquares

/-- The same sharp estimate is a lower bound for the actual finite-cluster
vertical diameter. The extremizing Euclidean pair remains explicit. -/
theorem cluster_vertical_diameter_ge_sqrt_three_of_wide_pair
    (q : Configuration) (J : Finset Label) (hJ : J.Nonempty)
    (a b : Label) (ha : a ∈ J) (hb : b ∈ J)
    {r : ℝ} (hr : 0 < r) (hpair : dist (q a) (q b) = r)
    (hx : |q a 0 - q b 0| ≤ r / 2) :
    Real.sqrt 3 * r / 2 ≤
      clusterCoordinateDiameter J (fun i => q i 1) hJ ∧
    0 < clusterCoordinateDiameter J (fun i => q i 1) hJ := by
  have hy := vertical_separation_sqrt_three_of_horizontal_le_half
    (q a) (q b) hr hpair hx
  have hdiam := cluster_coordinate_abs_difference_le_diameter
    J (fun i => q i 1) hJ a b ha hb
  have hlower := hy.trans hdiam
  have hsharpPos : 0 < Real.sqrt 3 * r / 2 := by
    exact div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hr) (by norm_num)
  exact ⟨hlower, hsharpPos.trans_le hlower⟩

end FourBody.SourceFaithfulConstantsWidth

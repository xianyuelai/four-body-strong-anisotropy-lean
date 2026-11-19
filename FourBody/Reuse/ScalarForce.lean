import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Renaming-only extraction of the genuine signed inverse-cube scalar
force and its derivatives/monotonicity from TripleScalar. No tripleD0,
three-body seed, weight normalization, or seven-row chart is retained.
This matches the scalar force in the current manuscript's equation (1.3).
-/
noncomputable section
open scoped ContDiff
open Set Filter Topology
namespace FourBody.Reuse

def scalarForce (x : ℝ) : ℝ := x / |x| ^ 3

theorem scalarForce_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt scalarForce (-2 / |x| ^ 3) x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hd := (hasDerivAt_id x).div ((hasDerivAt_abs_neg hneg).pow 3)
      (pow_ne_zero 3 (abs_ne_zero.mpr hx))
    convert! hd using 1
    simp only [Pi.pow_apply, id_eq]
    rw [abs_of_neg hneg]
    field_simp
    ring
  · have hd := (hasDerivAt_id x).div ((hasDerivAt_abs_pos hpos).pow 3)
      (pow_ne_zero 3 (abs_ne_zero.mpr hx))
    convert! hd using 1
    simp only [Pi.pow_apply, id_eq]
    rw [abs_of_pos hpos]
    field_simp
    ring

theorem scalarForce_contDiffAt (n : ℕ∞) {x : ℝ} (hx : x ≠ 0) :
    ContDiffAt ℝ n scalarForce x := by
  unfold scalarForce
  exact contDiffAt_id.div ((contDiffAt_id.abs hx).pow 3) (pow_ne_zero 3 (abs_ne_zero.mpr hx))

theorem scalarForce_strictAntiOn_pos : StrictAntiOn scalarForce (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro x hx
    exact (scalarForce_hasDerivAt (ne_of_gt hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(scalarForce_hasDerivAt (ne_of_gt hx)).deriv]
    exact div_neg_of_neg_of_pos (by norm_num) (pow_pos (abs_pos.mpr (ne_of_gt hx)) 3)

theorem scalarForce_strictAntiOn_neg : StrictAntiOn scalarForce (Iio 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Iio 0)
  · intro x hx
    exact (scalarForce_hasDerivAt (ne_of_lt hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Iio] at hx
    rw [(scalarForce_hasDerivAt (ne_of_lt hx)).deriv]
    exact div_neg_of_neg_of_pos (by norm_num) (pow_pos (abs_pos.mpr (ne_of_lt hx)) 3)


end FourBody.Reuse

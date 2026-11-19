import FourBody.Reuse.NewtonBounds

/-!
Source v2 Section 2 records the exact Newton kernel operator norm 2/r^3.
The accepted NewtonBounds proves the sharp upper bound. This module adds
the radial equality that attains it and hence the actual equality of norms.

Initially prepared as a proof candidate. Actual build/audit status is
recorded in strict receipts; this module alone does not attest
whole-paper acceptance.
-/

set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
namespace FourBody.Reuse

theorem newtonTargetDerivative_radial (source target : Plane)
    (hsep : source ≠ target) :
    newtonTargetDerivative source target (source-target) =
      (2 / ‖source-target‖^3) • (source-target) := by
  have hn : ‖source-target‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hsep)
  rw [newtonTargetDerivative_apply, real_inner_self_eq_norm_sq, ← sub_smul]
  congr 1
  field_simp [hn]
  ring

theorem newtonTargetDerivative_operator_norm_exact (source target : Plane)
    (hsep : source ≠ target) :
    ‖newtonTargetDerivative source target‖ = 2 / ‖source-target‖^3 := by
  have hR : 0 < ‖source-target‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hsep)
  apply le_antisymm (newtonTargetDerivative_operator_norm_bound_sharp source target hsep)
  have hr := (newtonTargetDerivative source target).le_opNorm (source-target)
  rw [newtonTargetDerivative_radial source target hsep, norm_smul,
    Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) (pow_pos hR 3))] at hr
  exact (mul_le_mul_iff_left₀ hR).mp hr

theorem physicalNewtonForce_fderiv_norm_exact (mass : ℝ) (source target : Plane)
    (hsep : source ≠ target) :
    ‖fderiv ℝ (physicalNewtonForce mass source) target‖ =
      |mass| * (2 / dist target source ^ 3) := by
  rw [(physicalNewtonForce_hasFDerivAt mass source target hsep).fderiv,
    norm_smul, Real.norm_eq_abs, abs_neg,
    newtonTargetDerivative_operator_norm_exact source target hsep,
    dist_eq_norm, norm_sub_rev target source]

end FourBody.Reuse

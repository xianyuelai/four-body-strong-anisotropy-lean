import FourBody.NewtonExactNorm
import Mathlib.Tactic.Module

/-!
Direct source-facing Newton kernel, v2 Section 2, S2-U05 and S2-U06.
The actual kernel is K(z)=z/|z|^3 on the original Euclidean plane.
The proven target-field convention is converted with its exact minus sign.
This file was initially prepared as a candidate; actual elaboration and
complete type/axiom evidence must be read from the corresponding receipts.
-/

noncomputable section
open scoped RealInnerProductSpace
namespace FourBody.SourceNewton

def kernel (z : Point) : Point := (‖z‖ ^ 3)⁻¹ • z

def kernelDerivative (z : Point) : Point →L[ℝ] Point :=
  (‖z‖ ^ 3)⁻¹ • ContinuousLinearMap.id ℝ Point -
    (3 / ‖z‖ ^ 5) • ((innerSL ℝ z).smulRight z)

theorem kernel_eq_physicalNewtonForce :
    kernel = Reuse.physicalNewtonForce 1 (0 : Point) := by
  funext z
  simp [kernel, Reuse.physicalNewtonForce]

theorem kernelDerivative_apply (z v : Point) :
    kernelDerivative z v = (‖z‖ ^ 3)⁻¹ • v -
      ((3 / ‖z‖ ^ 5) * inner ℝ z v) • z := by
  simp only [kernelDerivative, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]

theorem kernelDerivative_eq_neg_legacy (z : Point) :
    kernelDerivative z = -Reuse.newtonTargetDerivative 0 z := by
  have hrank : (innerSL ℝ (-z)).smulRight (-z) = (innerSL ℝ z).smulRight z := by
    ext v
    simp [innerSL_apply_apply]
  unfold kernelDerivative Reuse.newtonTargetDerivative
  rw [zero_sub, norm_neg, hrank]
  module

theorem kernel_hasFDerivAt (z : Point) (hz : z ≠ 0) :
    HasFDerivAt kernel (kernelDerivative z) z := by
  rw [kernel_eq_physicalNewtonForce, kernelDerivative_eq_neg_legacy]
  have hd := Reuse.physicalNewtonForce_hasFDerivAt 1 0 z hz.symm
  convert! hd using 1
  module

theorem kernelDerivative_operator_norm_exact (z : Point) (hz : z ≠ 0) :
    ‖kernelDerivative z‖ = 2 / ‖z‖ ^ 3 := by
  rw [kernelDerivative_eq_neg_legacy, norm_neg,
    Reuse.newtonTargetDerivative_operator_norm_exact 0 z hz.symm,
    zero_sub, norm_neg]

theorem kernel_fderiv_norm_exact (z : Point) (hz : z ≠ 0) :
    ‖fderiv ℝ kernel z‖ = 2 / ‖z‖ ^ 3 := by
  rw [(kernel_hasFDerivAt z hz).fderiv]
  exact kernelDerivative_operator_norm_exact z hz

end FourBody.SourceNewton

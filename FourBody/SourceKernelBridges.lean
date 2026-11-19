import FourBody.Geometry
import FourBody.Reuse.NewtonKernel
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Literal analytic-kernel bridges for v2 S4-U02/U11.
Frozen manuscript SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
These supplement the actual already checked vector Newton derivative, rather
than use any requested differentiability conclusion as a premise.
STATIC CANDIDATE ONLY; no Lean/Lake execution or dependency-trust audit for this file.
-/

noncomputable section
open scoped ContDiff
namespace FourBody.SourceKernelBridges

/-- Real inverse-three-halves of the squared norm is the inverse cube. -/
theorem norm_sq_rpow_neg_three_halves (z : Point) :
    Real.rpow (‖z‖ ^ 2) (-(3 : ℝ) / 2) = (‖z‖ ^ 3)⁻¹ := by
  rw [Real.rpow_eq_pow, ← Real.rpow_natCast ‖z‖ 2,
    ← Real.rpow_mul (norm_nonneg z)]
  rw [show ((2 : ℕ) : ℝ) * (-(3 : ℝ) / 2) = -(3 : ℝ) by norm_num,
    Real.rpow_neg (norm_nonneg z), Real.rpow_ofNat]

/-- The actual scalar coefficient is smooth to every order off a collision. -/
theorem inverse_cube_norm_contDiffAt (n : ℕ∞ω) {z : Point} (hz : z ≠ 0) :
    ContDiffAt ℝ n (fun w : Point => (‖w‖ ^ 3)⁻¹) z := by
  have hn : ContDiffAt ℝ n (fun w : Point => ‖w‖) z :=
    contDiffAt_id.norm ℝ hz
  exact (hn.pow 3).inv (pow_ne_zero 3 (norm_ne_zero_iff.mpr hz))

theorem inverse_cube_norm_analyticAt {z : Point} (hz : z ≠ 0) :
    AnalyticAt ℝ (fun w : Point => (‖w‖ ^ 3)⁻¹) z :=
  (inverse_cube_norm_contDiffAt ω hz).analyticAt

/-- The manuscript's literal exponent coefficient is real analytic off zero. -/
theorem norm_sq_rpow_neg_three_halves_analyticAt {z : Point} (hz : z ≠ 0) :
    AnalyticAt ℝ (fun w : Point => Real.rpow (‖w‖ ^ 2) (-(3 : ℝ) / 2)) z := by
  have heq : (fun w : Point => Real.rpow (‖w‖ ^ 2) (-(3 : ℝ) / 2)) =
      (fun w : Point => (‖w‖ ^ 3)⁻¹) := by
    funext w
    exact norm_sq_rpow_neg_three_halves w
  rw [heq]
  exact inverse_cube_norm_analyticAt hz

/-- Literal one-variable signed Newton quotient, proved for both signs. -/
theorem signed_quotient_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => t / |t| ^ 3) (-2 * (|x| ^ 3)⁻¹) x := by
  have hden : |x| ^ 3 ≠ 0 := pow_ne_zero 3 (abs_ne_zero.mpr hx)
  rcases hx.lt_or_gt with hxneg | hxpos
  · have h := (hasDerivAt_id x).div ((hasDerivAt_abs_neg hxneg).pow 3) hden
    change HasDerivAt (fun t : ℝ => t / |t| ^ 3)
      ((1 * |x| ^ 3 - x * (3 * |x| ^ 2 * (-1))) / (|x| ^ 3) ^ 2) x at h
    have hcoef :
        (1 * |x| ^ 3 - x * (3 * |x| ^ 2 * (-1))) / (|x| ^ 3) ^ 2 =
          -2 * (|x| ^ 3)⁻¹ := by
      rw [abs_of_neg hxneg]
      field_simp [hx]
      ring
    rwa [hcoef] at h
  · have h := (hasDerivAt_id x).div ((hasDerivAt_abs_pos hxpos).pow 3) hden
    change HasDerivAt (fun t : ℝ => t / |t| ^ 3)
      ((1 * |x| ^ 3 - x * (3 * |x| ^ 2 * 1)) / (|x| ^ 3) ^ 2) x at h
    have hcoef :
        (1 * |x| ^ 3 - x * (3 * |x| ^ 2 * 1)) / (|x| ^ 3) ^ 2 =
          -2 * (|x| ^ 3)⁻¹ := by
      rw [abs_of_pos hxpos]
      field_simp [hx]
      ring
    rwa [hcoef] at h

theorem signed_quotient_deriv {x : ℝ} (hx : x ≠ 0) :
    deriv (fun t : ℝ => t / |t| ^ 3) x = -2 * (|x| ^ 3)⁻¹ :=
  (signed_quotient_hasDerivAt hx).deriv

theorem signed_quotient_hasDerivAt_rpow {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => t / |t| ^ 3)
      (-2 * Real.rpow |x| (-3 : ℝ)) x := by
  rw [Real.rpow_eq_pow, Real.rpow_neg (abs_nonneg x), Real.rpow_ofNat]
  exact signed_quotient_hasDerivAt hx

end FourBody.SourceKernelBridges


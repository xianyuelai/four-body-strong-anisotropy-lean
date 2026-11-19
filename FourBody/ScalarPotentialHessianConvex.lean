import FourBody.ScalarPotentialHessian
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
Candidate bridge for v2 Lemma 3.1's actual second derivative route.
The line restriction's second ordinary derivative is derived from the
already calculated second Frechet derivative of the literal potential.
The strict convexity theorem below does not use the previously proved
quadratic Jensen strict-convexity theorem or a minimizer/root conclusion.

This file has not been compiled by its author. Parent serial compilation,
full exported types and dependency checks remain required.
-/

noncomputable section
open scoped BigOperators
open Set Filter Topology

namespace FourBody.ScalarMinimizer

/-- First ordinary derivative along a literal affine line in the chamber. -/
theorem scalarPotential_line_hasDerivAt {n : ℕ} (μ x y : ScalarVector n) (t : ℝ)
    (hz : AffineMap.lineMap x y t ∈ ambientChamber n) :
    HasDerivAt (fun u : ℝ => scalarPotential μ (AffineMap.lineMap x y u))
      (fderiv ℝ (scalarPotential μ) (AffineMap.lineMap x y t) (y - x)) t := by
  have hbase :=
    (scalarPotential_hasFDerivAt μ (AffineMap.lineMap x y t) hz).differentiableAt.hasFDerivAt
  simpa only [Function.comp_def] using hbase.comp_hasDerivAt t
    (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t))

/-- The derivative of the actual first Frechet derivative applied to the
constant line direction, followed by the line chain rule. -/
theorem scalarPotential_line_first_hasDerivAt {n : ℕ}
    (μ x y : ScalarVector n) (t : ℝ)
    (hz : AffineMap.lineMap x y t ∈ ambientChamber n) :
    HasDerivAt
      (fun u : ℝ => fderiv ℝ (scalarPotential μ) (AffineMap.lineMap x y u) (y - x))
      (fderiv ℝ (fun w : ScalarVector n => fderiv ℝ (scalarPotential μ) w)
        (AffineMap.lineMap x y t) (y - x) (y - x)) t := by
  have hbase :=
    (scalarPotential_second_hasFDerivAt μ (AffineMap.lineMap x y t) hz).differentiableAt.hasFDerivAt
  have heval := hbase.clm_apply
    (hasFDerivAt_const (y - x) (AffineMap.lineMap x y t))
  simpa only [Function.comp_def, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using heval.comp_hasDerivAt t
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t))

/-- Actual `deriv (deriv ...)` along the line. Chamber openness supplies
the neighborhood needed to replace the ordinary first derivative. -/
theorem scalarPotential_line_second_deriv {n : ℕ} (μ x y : ScalarVector n) (t : ℝ)
    (hz : AffineMap.lineMap x y t ∈ ambientChamber n) :
    deriv (deriv (fun u : ℝ => scalarPotential μ (AffineMap.lineMap x y u))) t =
      fderiv ℝ (fun w : ScalarVector n => fderiv ℝ (scalarPotential μ) w)
        (AffineMap.lineMap x y t) (y - x) (y - x) := by
  have hnear : ∀ᶠ u in 𝓝 t, AffineMap.lineMap x y u ∈ ambientChamber n :=
    (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t)).continuousAt.tendsto.eventually
      ((ambientChamber_isOpen n).mem_nhds hz)
  have heq : deriv (fun u : ℝ => scalarPotential μ (AffineMap.lineMap x y u)) =ᶠ[𝓝 t]
      (fun u : ℝ => fderiv ℝ (scalarPotential μ) (AffineMap.lineMap x y u) (y - x)) := by
    apply hnear.mono
    intro u hu
    exact (scalarPotential_line_hasDerivAt μ x y u hu).deriv
  exact ((scalarPotential_line_first_hasDerivAt μ x y t hz).congr_of_eventuallyEq heq).deriv

/-- The manuscript's Hessian-positive route to strict convexity of Phi.
Every secant is restricted to an affine line. Its actual second derivative
is positive because the line direction is nonzero. -/
theorem scalarPotential_strictConvexOn_from_second_derivative {n : ℕ}
    (μ : ScalarVector n) (hμ : ∀ i, 0 < μ i) :
    StrictConvexOn ℝ (ambientChamber n) (scalarPotential μ) := by
  refine ⟨ambientChamber_convex n, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  let g : ℝ → ℝ := fun t => scalarPotential μ (AffineMap.lineMap x y t)
  have hmap : MapsTo (AffineMap.lineMap x y) (Icc (0 : ℝ) 1) (ambientChamber n) :=
    (ambientChamber_convex n).mapsTo_lineMap hx hy
  have hnonzero : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hcontinuous : ContinuousOn g (Icc (0 : ℝ) 1) := by
    intro t ht
    exact (scalarPotential_line_hasDerivAt μ x y t (hmap ht)).continuousAt.continuousWithinAt
  have hpositive : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (deriv^[2] g) t := by
    intro t ht
    change 0 < deriv (deriv (fun u : ℝ => scalarPotential μ (AffineMap.lineMap x y u))) t
    rw [scalarPotential_line_second_deriv μ x y t (hmap ht)]
    exact scalarPotential_second_fderiv_diagonal_pos μ (AffineMap.lineMap x y t)
      (y - x) hμ (hmap ht) hnonzero
  have hstrict : StrictConvexOn ℝ (Icc (0 : ℝ) 1) g :=
    strictConvexOn_of_deriv2_pos' (convex_Icc (0 : ℝ) 1) hcontinuous hpositive
  have hs := hstrict.2 (x := (0 : ℝ)) (y := (1 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) ha hb hab
  have hba : 1 - b = a := by linarith
  simpa only [g, smul_eq_mul, mul_zero, mul_one, zero_add,
    AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    AffineMap.lineMap_apply_module, hba, sub_zero, sub_self, zero_smul,
    one_smul, add_zero] using hs

/-- Restriction to the paper's original weighted center-zero chamber.
The coercion is injective, so a nonzero centered secant remains nonzero. -/
theorem scalarPotential_centered_strictConvexOn_from_second_derivative {n : ℕ}
    (μ : ScalarVector n) (hμ : ∀ i, 0 < μ i) :
    StrictConvexOn ℝ (FourBody.ScalarGeometry.chamber μ)
      (fun z : FourBody.ScalarGeometry.ScalarW μ => scalarPotential μ z.val) := by
  refine ⟨FourBody.ScalarGeometry.chamber_convex μ, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hneq : x.val ≠ y.val := fun he => hxy (Subtype.ext he)
  simpa only [Submodule.coe_add, Submodule.coe_smul] using
    (scalarPotential_strictConvexOn_from_second_derivative μ hμ).2
      (x := x.val) hx (y := y.val) hy hneq ha hb hab

end FourBody.ScalarMinimizer

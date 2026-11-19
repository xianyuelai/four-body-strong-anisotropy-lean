import FourBody.ScalarPotentialHessianConvex
import FourBody.ScalarPotentialConstraint
import FourBody.ScalarPotentialMinimizer

/-!
Source-only candidate completing v2 Lemma 3.1's actual centered variational
route after the second-derivative strict-convexity bridge. These proofs do
not reference the older Jensen strict-convexity result or a previous root
existence/uniqueness theorem. Actual parent serial compilation is required.
-/

noncomputable section
open scoped BigOperators
open Set Filter Topology

namespace FourBody.ScalarMinimizer

/-- A critical point of the literal potential minimizes that potential,
using convexity derived from the actual positive second derivative. -/
theorem scalarPotential_critical_isMinOn_hessian_route {n : ℕ} (μ z : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (hz : z ∈ ambientChamber n)
    (hcritical : fderiv ℝ (scalarPotential μ) z = 0) :
    IsMinOn (scalarPotential μ) (ambientChamber n) z := by
  intro y hy
  let L : ℝ →ᵃ[ℝ] ScalarVector n := AffineMap.lineMap z y
  have hconv :=
    ((scalarPotential_strictConvexOn_from_second_derivative μ hμ).convexOn.comp_affineMap L).subset
      ((ambientChamber_convex n).mapsTo_lineMap hz hy) (convex_Icc (0 : ℝ) 1)
  have hd0 : HasFDerivAt (scalarPotential μ) (0 : ScalarVector n →L[ℝ] ℝ) z := by
    simpa only [hcritical] using
      (scalarPotential_hasFDerivAt μ z hz).differentiableAt.hasFDerivAt
  have hd : HasDerivAt ((scalarPotential μ) ∘ L) 0 0 := by
    have hbase : HasFDerivAt (scalarPotential μ) (0 : ScalarVector n →L[ℝ] ℝ) (L 0) := by
      simpa only [L, AffineMap.lineMap_apply_zero] using hd0
    simpa only [zero_apply] using hbase.comp_hasDerivAt 0
      (AffineMap.hasDerivAt_lineMap (a := z) (b := y) (x := (0 : ℝ)))
  have hs := hconv.le_slope_of_hasDerivAt (x := (0 : ℝ)) (y := (1 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hd
  have hvalue : 0 ≤ scalarPotential μ y - scalarPotential μ z := by
    simpa [slope, L] using hs
  exact sub_nonneg.mp hvalue

/-- The original weighted center-zero chamber has exactly one actual
normalized scalar solution, via its own compact minimum, constrained
Fermat, the annihilator/common-residual argument, and positive Hessian.
No root existence or uniqueness conclusion is assumed or reused. -/
theorem scalar_chamber_solution_existsUnique_hessian_route {n : ℕ}
    (μ : ScalarVector n) (hμ : ∀ i, 0 < μ i) :
    ∃! z : FourBody.ScalarGeometry.ScalarW μ,
      z ∈ FourBody.ScalarGeometry.chamber μ ∧
      FourBody.ScalarGeometry.IsScalarSolution μ z.val := by
  obtain ⟨z, hz, hmin⟩ := scalarPotential_centered_exists_minimizer μ hμ
  have hroot := scalarPotential_centered_minimizer_root μ hμ z hz hmin
  have hminz := scalarPotential_critical_isMinOn_hessian_route μ z.val hμ hz
    ((scalarPotential_critical_iff_root μ z.val hμ hz).mpr hroot)
  refine ⟨z, ⟨hz, hz.injective, hroot⟩, ?_⟩
  intro y hy
  have hminy := scalarPotential_critical_isMinOn_hessian_route μ y.val hμ hy.1
    ((scalarPotential_critical_iff_root μ y.val hμ hy.1).mpr hy.2.2)
  apply Subtype.ext
  exact (scalarPotential_strictConvexOn_from_second_derivative μ hμ).eq_of_isMinOn
    hminy hminz hy.1 hz

end FourBody.ScalarMinimizer

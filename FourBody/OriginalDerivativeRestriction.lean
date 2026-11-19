import FourBody.Geometry
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
Literal bridges for the actual frozen v2, lines 70--71 and 91--100.
The original derivative is computed in the original labeled ambient space;
the constrained derivative is its restriction to the genuine weighted kernel.
Static proof candidate: actual strict compilation, full types and axiom audit
are still required. This declaration does not assert nondegeneracy.
-/

noncomputable section
namespace FourBody.OriginalGeometrySupplement

theorem anisotropy_one (p : Point) : anisotropy 1 p = p := by
  ext k
  fin_cases k <;> simp

theorem isotropic_solution_iff (m : Masses) (q : Configuration) :
    IsSolution m 1 q ↔ CollisionFree q ∧ ∀ i, force m q i = q i := by
  simp only [IsSolution, anisotropy_one]

/-- The ambient physical Newton residual and the actual restricted residual
are equal after the inclusion of W. No projection enters this identity. -/
theorem restrictedResidual_coe (m : Masses) (s : ℝ) (q : W m) :
    ((restrictedResidual m s q : W m) : Configuration) =
      residual m s (q : Configuration) := rfl

/-- Source notation `D R_s(q)|W`: both sides are actual Frechet derivatives,
computed at the physical collision-free point. -/
theorem original_derivative_restriction (m : Masses) (hm : PositiveMasses m)
    (s : ℝ) (q : W m) (hq : CollisionFree (q : Configuration)) :
    (W m).subtypeL.comp (fderiv ℝ (restrictedResidual m s) q) =
      (fderiv ℝ (residual m s) (q : Configuration)).comp (W m).subtypeL := by
  have hrestricted : DifferentiableAt ℝ (restrictedResidual m s) q :=
    (contDiffAt_restrictedResidual m hm s 1 hq).differentiableAt_one
  have hambient : DifferentiableAt ℝ (residual m s) (q : Configuration) :=
    (contDiffAt_residual m s 1 hq).differentiableAt_one
  have hleft : HasFDerivAt
      (fun t : W m => ((restrictedResidual m s t : W m) : Configuration))
      ((W m).subtypeL.comp (fderiv ℝ (restrictedResidual m s) q)) q :=
    (W m).subtypeL.hasFDerivAt.comp q hrestricted.hasFDerivAt
  have hright : HasFDerivAt
      (fun t : W m => residual m s (t : Configuration))
      ((fderiv ℝ (residual m s) (q : Configuration)).comp (W m).subtypeL) q :=
    hambient.hasFDerivAt.comp q (W m).subtypeL.hasFDerivAt
  exact hleft.unique hright

/-- The actual ambient derivative maps each original centered direction
back into the same original W. -/
theorem ambient_derivative_maps_W (m : Masses) (hm : PositiveMasses m)
    (s : ℝ) (q : W m) (hq : CollisionFree (q : Configuration)) (v : W m) :
    fderiv ℝ (residual m s) (q : Configuration) (v : Configuration) ∈ W m := by
  have h := congrArg (fun L : W m →L[ℝ] Configuration => L v)
    (original_derivative_restriction m hm s q hq)
  change (((fderiv ℝ (restrictedResidual m s) q) v : W m) : Configuration) =
    fderiv ℝ (residual m s) (q : Configuration) (v : Configuration) at h
  rw [← h]
  exact ((fderiv ℝ (restrictedResidual m s) q) v).property

end FourBody.OriginalGeometrySupplement

import FourBody.ScalarPotentialOriginalRoute
import FourBody.ScalarPotentialOrder

/-!
Extending the already checked centered Hessian route to
every prescribed order of the fixed labels. The literal force-relabeling
proofs below are copied from checked ScalarPotentialOrder, with only theorem
names and the root dependency changed. No old Jensen minimizer/root theorem
is used in this candidate.

Initially prepared as a proof candidate. Actual build/audit status is
recorded in strict receipts; this module alone does not attest
whole-paper acceptance.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Set

namespace FourBody.ScalarMinimizer

/-- Raw-vector form of the actual centered Hessian-route theorem. Its
weighted center condition is retained explicitly in the conclusion. -/
theorem scalar_potential_root_existsUnique_centered_hessian_route {n : ℕ}
    (μ : ScalarVector n) (hμ : ∀ i, 0 < μ i) :
    ∃! z : ScalarVector n, z ∈ ambientChamber n ∧
      (∀ i, FourBody.ScalarGeometry.scalarForce μ z i = z i) ∧
      z ∈ FourBody.ScalarGeometry.ScalarW μ := by
  obtain ⟨w, hw, huniq⟩ := scalar_chamber_solution_existsUnique_hessian_route μ hμ
  refine ⟨w.val, ⟨hw.1, hw.2.2, w.property⟩, ?_⟩
  intro y hy
  let y' : FourBody.ScalarGeometry.ScalarW μ := ⟨y, hy.2.2⟩
  have hy' : y' ∈ FourBody.ScalarGeometry.chamber μ ∧
      FourBody.ScalarGeometry.IsScalarSolution μ y'.val :=
    ⟨hy.1, hy.1.injective, hy.2.1⟩
  exact congrArg Subtype.val (huniq y' hy')

/-- Every fixed-label order receives the root from the actual centered
minimum and Hessian route before the exact force/center relabeling. -/
theorem prescribed_scalar_root_existsUnique_hessian_route {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (σ : Equiv.Perm (Fin n)) :
    ∃! z : ScalarVector n, z ∈ prescribedScalarChamber σ ∧
      (∀ i, FourBody.ScalarGeometry.scalarForce μ z i = z i) ∧
      z ∈ FourBody.ScalarGeometry.ScalarW μ := by
  let ν : ScalarVector n := μ ∘ σ
  obtain ⟨w, hw, huniq⟩ := scalar_potential_root_existsUnique_centered_hessian_route ν (fun i => hμ (σ i))
  let z : ScalarVector n := w ∘ σ.symm
  have hzorder : z ∈ prescribedScalarChamber σ := by
    change StrictMono (z ∘ σ)
    have hwmono : StrictMono w := hw.1
    simpa only [z, Function.comp_def, Equiv.symm_apply_apply] using hwmono
  have hzroot : ∀ i, FourBody.ScalarGeometry.scalarForce μ z i = z i := by
    intro i
    have hrel := scalarForce_relabel μ z σ (σ.symm i)
    have hrel' : FourBody.ScalarGeometry.scalarForce ν w (σ.symm i) =
        FourBody.ScalarGeometry.scalarForce μ z i := by
      simpa only [ν, z, Function.comp_def, Equiv.symm_apply_apply,
        Equiv.apply_symm_apply] using hrel
    have hroot := hw.2.1 (σ.symm i)
    exact hrel'.symm.trans hroot
  have hzcenter : z ∈ FourBody.ScalarGeometry.ScalarW μ := by
    change (∑ i, μ i * z i) = 0
    have hsum := Equiv.sum_comp σ (fun i => μ i * z i)
    have hc : (∑ i, μ (σ i) * z (σ i)) = 0 := by
      have hcw : (∑ i, ν i * w i) = 0 := hw.2.2
      simpa only [ν, z, Function.comp_def, Equiv.symm_apply_apply] using hcw
    exact hsum.symm.trans hc
  refine ⟨z, ⟨hzorder, hzroot, hzcenter⟩, ?_⟩
  intro y hy
  have hyroot : ∀ i, FourBody.ScalarGeometry.scalarForce ν (y ∘ σ) i = (y ∘ σ) i := by
    intro i
    rw [show ν = μ ∘ σ from rfl, scalarForce_relabel]
    exact hy.2.1 (σ i)
  have hycenter : (y ∘ σ) ∈ FourBody.ScalarGeometry.ScalarW ν := by
    change (∑ i, μ (σ i) * y (σ i)) = 0
    have hc : (∑ i, μ i * y i) = 0 := hy.2.2
    exact (Equiv.sum_comp σ (fun i => μ i * y i)).trans hc
  have he := huniq (y ∘ σ) ⟨hy.1, hyroot, hycenter⟩
  funext i
  have hi := congr_fun he (σ.symm i)
  simpa only [z, Function.comp_def, Equiv.apply_symm_apply] using hi

theorem prescribed_scalar_solution_existsUnique_hessian_route {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (σ : Equiv.Perm (Fin n)) :
    ∃! z : FourBody.ScalarGeometry.ScalarW μ,
      z.val ∈ prescribedScalarChamber σ ∧ FourBody.ScalarGeometry.IsScalarSolution μ z.val := by
  obtain ⟨x, hx, huniq⟩ := prescribed_scalar_root_existsUnique_hessian_route μ hμ σ
  let z : FourBody.ScalarGeometry.ScalarW μ := ⟨x, hx.2.2⟩
  have hxinj : Function.Injective x := by
    intro i j hij
    have he : σ.symm i = σ.symm j := hx.1.injective (by simpa using hij)
    exact σ.symm.injective he
  refine ⟨z, ⟨hx.1, hxinj, hx.2.1⟩, ?_⟩
  intro y hy
  apply Subtype.ext
  exact huniq y.val ⟨hy.1, hy.2.2, y.property⟩


end FourBody.ScalarMinimizer

import FourBody.ScalarPotentialMinimizer
import FourBody.ScalarPotentialConstraint

/-!
The prescribed order in Lemma 3.1 is an arbitrary permutation of fixed
labels. This file proves the literal force system is equivariant under
relabeling and transfers the actual unique centered root. No mass equality,
normalization, fixed dimension, or quotient by symmetry is introduced.
These source proof bodies still require serial Lean verification.
-/

noncomputable section
open scoped BigOperators
open Set

namespace FourBody.ScalarMinimizer

theorem scalarForce_full_sum {n : ℕ} (μ z : ScalarVector n) (i : Fin n) :
    FourBody.ScalarGeometry.scalarForce μ z i =
      ∑ j, μ j * (z i - z j) / |z i - z j| ^ 3 := by
  simp [FourBody.ScalarGeometry.scalarForce]

/-- Exact relabeling of the original erased-self force sum. -/
theorem scalarForce_relabel {n : ℕ} (μ z : ScalarVector n)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    FourBody.ScalarGeometry.scalarForce (μ ∘ σ) (z ∘ σ) i =
      FourBody.ScalarGeometry.scalarForce μ z (σ i) := by
  rw [scalarForce_full_sum, scalarForce_full_sum]
  exact Equiv.sum_comp σ (fun j => μ j * (z (σ i) - z j) / |z (σ i) - z j| ^ 3)

def prescribedScalarChamber {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Set (ScalarVector n) := {z | StrictMono (z ∘ σ)}

/-- Unique normalized scalar root for every prescribed label order and
every finite positive mass vector, with the literal weighted center zero. -/
theorem prescribed_scalar_root_existsUnique {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (σ : Equiv.Perm (Fin n)) :
    ∃! z : ScalarVector n, z ∈ prescribedScalarChamber σ ∧
      (∀ i, FourBody.ScalarGeometry.scalarForce μ z i = z i) ∧
      z ∈ FourBody.ScalarGeometry.ScalarW μ := by
  let ν : ScalarVector n := μ ∘ σ
  obtain ⟨w, hw, huniq⟩ := scalar_potential_root_existsUnique_centered ν (fun i => hμ (σ i))
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

theorem prescribed_scalar_solution_existsUnique {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (σ : Equiv.Perm (Fin n)) :
    ∃! z : FourBody.ScalarGeometry.ScalarW μ,
      z.val ∈ prescribedScalarChamber σ ∧ FourBody.ScalarGeometry.IsScalarSolution μ z.val := by
  obtain ⟨x, hx, huniq⟩ := prescribed_scalar_root_existsUnique μ hμ σ
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

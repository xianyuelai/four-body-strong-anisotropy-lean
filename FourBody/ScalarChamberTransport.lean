import FourBody.ScalarPotentialOrder
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
STATIC supplement for frozen v2 Lemma 3.1, S3-D02/S3-U01.
Every prescribed order is transported by the literal permutation of labels
and corresponding permuted masses. The relative topology is on the actual
mass-center kernel. Fin 0 and Fin 1 are included. No Lean execution yet.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace FourBody.ScalarSupplement

open ScalarGeometry ScalarMinimizer

def centeredOrderLinearEquivalence {n : ℕ} (μ : ScalarVector n)
    (σ : Equiv.Perm (Fin n)) : ScalarW μ ≃ₗ[ℝ] ScalarW (μ ∘ σ) where
  toFun z := ⟨z.val ∘ σ, by
    change (∑ i, μ (σ i) * z.val (σ i)) = 0
    exact (Equiv.sum_comp σ (fun i => μ i * z.val i)).trans z.property⟩
  invFun w := ⟨w.val ∘ σ.symm, by
    change (∑ i, μ i * w.val (σ.symm i)) = 0
    have hc : (∑ i, (μ ∘ σ) i * w.val i) = 0 := w.property
    have he := Equiv.sum_comp σ.symm (fun i => μ (σ i) * w.val i)
    simpa only [Equiv.apply_symm_apply] using he.trans hc⟩
  left_inv z := by
    apply Subtype.ext
    funext i
    exact congrArg z.val (σ.apply_symm_apply i)
  right_inv w := by
    apply Subtype.ext
    funext i
    exact congrArg w.val (σ.symm_apply_apply i)
  map_add' z w := by
    apply Subtype.ext
    funext i
    rfl
  map_smul' a z := by
    apply Subtype.ext
    funext i
    rfl

def centeredOrderEquivalence {n : ℕ} (μ : ScalarVector n)
    (σ : Equiv.Perm (Fin n)) : ScalarW μ ≃L[ℝ] ScalarW (μ ∘ σ) :=
  (centeredOrderLinearEquivalence μ σ).toContinuousLinearEquiv

@[simp] theorem centeredOrderEquivalence_apply {n : ℕ} (μ : ScalarVector n)
    (σ : Equiv.Perm (Fin n)) (z : ScalarW μ) (i : Fin n) :
    (centeredOrderEquivalence μ σ z).val i = z.val (σ i) := rfl

def prescribedCenteredChamber {n : ℕ} (μ : ScalarVector n)
    (σ : Equiv.Perm (Fin n)) : Set (ScalarW μ) :=
  {z | z.val ∈ prescribedScalarChamber σ}

theorem prescribedCenteredChamber_eq_preimage {n : ℕ} (μ : ScalarVector n)
    (σ : Equiv.Perm (Fin n)) :
    prescribedCenteredChamber μ σ =
      centeredOrderEquivalence μ σ ⁻¹' chamber (μ ∘ σ) := rfl

theorem chamber_isOpen {n : ℕ} (μ : ScalarVector n) : IsOpen (chamber μ) := by
  change IsOpen ((Subtype.val : ScalarW μ → ScalarVector n) ⁻¹' ambientChamber n)
  exact (ambientChamber_isOpen n).preimage continuous_subtype_val

theorem prescribedCenteredChamber_isOpen {n : ℕ} (μ : ScalarVector n)
    (σ : Equiv.Perm (Fin n)) : IsOpen (prescribedCenteredChamber μ σ) := by
  rw [prescribedCenteredChamber_eq_preimage]
  exact (chamber_isOpen (μ ∘ σ)).preimage (centeredOrderEquivalence μ σ).continuous

theorem prescribedCenteredChamber_convex {n : ℕ} (μ : ScalarVector n)
    (σ : Equiv.Perm (Fin n)) : Convex ℝ (prescribedCenteredChamber μ σ) := by
  rw [prescribedCenteredChamber_eq_preimage]
  exact (ScalarGeometry.chamber_convex (μ ∘ σ)).linear_preimage
    (centeredOrderEquivalence μ σ).toLinearMap

theorem prescribedCenteredChamber_nonempty {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (σ : Equiv.Perm (Fin n)) :
    (prescribedCenteredChamber μ σ).Nonempty := by
  obtain ⟨w, hw⟩ := ScalarGeometry.chamber_nonempty (μ ∘ σ) (fun i => hμ (σ i))
  refine ⟨(centeredOrderEquivalence μ σ).symm w, ?_⟩
  rw [prescribedCenteredChamber_eq_preimage]
  change centeredOrderEquivalence μ σ ((centeredOrderEquivalence μ σ).symm w) ∈
    chamber (μ ∘ σ)
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hw

end FourBody.ScalarSupplement

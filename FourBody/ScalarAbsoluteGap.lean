import FourBody.ScalarPotentialProper
import FourBody.ScalarPotentialOrder

/-!
STATIC source supplement S3-U04: every i != j, not only i < j.
The original absolute-pair energy is symmetric; trichotomy transports the
checked ordered-pair bound. Injectivity supplies the physical denominator.
The prescribed-order wrapper covers every permutation and every finite n.
-/

set_option autoImplicit false
noncomputable section
namespace FourBody.ScalarSupplement

open ScalarMinimizer

theorem scalarPotential_pair_term_le_of_ne {n : ℕ} (μ z : ScalarVector n)
    (hμ : ∀ i, 0 ≤ μ i) (i j : Fin n) (hij : i ≠ j) :
    μ i * μ j / |z i - z j| ≤ scalarPotential μ z := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact scalarPotential_pair_term_le μ z hμ i j hlt
  · have h := scalarPotential_pair_term_le μ z hμ j i hgt
    simpa only [abs_sub_comm, mul_comm] using h

theorem scalarPotential_sublevel_absolute_gap {n : ℕ} (μ z : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (hz : Function.Injective z) (A : ℝ) (hA : 0 < A)
    (hlevel : scalarPotential μ z ≤ A) (i j : Fin n) (hij : i ≠ j) :
    μ i * μ j / A ≤ |z i - z j| := by
  have hgap : 0 < |z i - z j| := abs_pos.mpr
    (sub_ne_zero.mpr (fun h => hij (hz h)))
  have hterm := (scalarPotential_pair_term_le_of_ne μ z
    (fun k => (hμ k).le) i j hij).trans hlevel
  apply (div_le_iff₀ hA).mpr
  have hmul := (div_le_iff₀ hgap).mp hterm
  simpa only [mul_comm] using hmul

theorem prescribedScalarChamber_injective {n : ℕ} (σ : Equiv.Perm (Fin n))
    (z : ScalarVector n) (hz : z ∈ prescribedScalarChamber σ) :
    Function.Injective z := by
  intro i j hij
  have he : σ.symm i = σ.symm j := hz.injective (by
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hij)
  exact σ.symm.injective he

theorem prescribed_sublevel_absolute_gap {n : ℕ} (μ z : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (σ : Equiv.Perm (Fin n))
    (hz : z ∈ prescribedScalarChamber σ) (A : ℝ) (hA : 0 < A)
    (hlevel : scalarPotential μ z ≤ A) :
    ∀ i j, i ≠ j → μ i * μ j / A ≤ |z i - z j| := by
  intro i j hij
  exact scalarPotential_sublevel_absolute_gap μ z hμ
    (prescribedScalarChamber_injective σ z hz) A hA hlevel i j hij

end FourBody.ScalarSupplement

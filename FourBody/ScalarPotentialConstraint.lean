import FourBody.ScalarPotentialGradient
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
The original weighted-center constraint route in v2 Lemma 3.1.
This is a proof of the actual annihilator and common-residual elimination,
not an assumption about a minimizer or a separate force interface.
All finite dimensions, including n = 0 and n = 1, are covered.
Staged source only: serial compiler verification remains with the parent.
-/

noncomputable section
open scoped BigOperators
open Set Filter Topology

namespace FourBody.ScalarMinimizer

theorem scalarWeightedSingle_sum {n : ℕ} (a : ScalarVector n) (i : Fin n) (b : ℝ) :
    (∑ j, a j * (Pi.single i b : ScalarVector n) j) = a i * b := by
  simp_rw [scalarSingle_apply]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Every pair of labels has a genuine centered tangent direction. -/
theorem scalar_pair_direction_centered {n : ℕ} (μ : ScalarVector n) (i j : Fin n) :
    (Pi.single i (μ j) - Pi.single j (μ i) : ScalarVector n) ∈
      FourBody.ScalarGeometry.ScalarW μ := by
  change (∑ k, μ k * ((Pi.single i (μ j) : ScalarVector n) k -
    (Pi.single j (μ i) : ScalarVector n) k)) = 0
  simp only [mul_sub, Finset.sum_sub_distrib, scalarWeightedSingle_sum]
  ring

/-- The annihilator of the weighted center-zero space consists of the
constant residuals, expressed without division or an n >= 2 exception. -/
theorem scalar_weighted_center_annihilator {n : ℕ} (μ r : ScalarVector n)
    (hμ : ∀ i, 0 < μ i)
    (hvanish : ∀ h : ScalarVector n, h ∈ FourBody.ScalarGeometry.ScalarW μ →
      (∑ k, μ k * r k * h k) = 0) :
    ∀ i j, r i = r j := by
  intro i j
  have h := hvanish (Pi.single i (μ j) - Pi.single j (μ i))
    (scalar_pair_direction_centered μ i j)
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
    scalarWeightedSingle_sum] at h
  have hp : (μ i * μ j) * (r i - r j) = 0 := by nlinarith [h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left
    (mul_ne_zero (hμ i).ne' (hμ j).ne'))

/-- A common residual with zero weighted sum is zero. The witness index
in the conclusion supplies nonemptiness, so the empty dimension is honest. -/
theorem scalar_weighted_center_annihilator_zero {n : ℕ} (μ r : ScalarVector n)
    (hμ : ∀ i, 0 < μ i)
    (hvanish : ∀ h : ScalarVector n, h ∈ FourBody.ScalarGeometry.ScalarW μ →
      (∑ k, μ k * r k * h k) = 0)
    (hweighted : (∑ i, μ i * r i) = 0) : ∀ i, r i = 0 := by
  intro i
  have hconst := scalar_weighted_center_annihilator μ r hμ hvanish
  have hmass : 0 < ∑ j, μ j :=
    Finset.sum_pos (fun j _ => hμ j) ⟨i, Finset.mem_univ _⟩
  have he : (∑ j, μ j) * r i = 0 := by
    rw [Finset.sum_mul]
    calc
      _ = ∑ j, μ j * r j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hconst j i]
      _ = 0 := hweighted
  exact (mul_eq_zero.mp he).resolve_left hmass.ne'

theorem scalarQuadraticPotentialDerivative_one {n : ℕ} (μ z : ScalarVector n) :
    scalarQuadraticPotentialDerivative μ z (fun _ => 1) = ∑ i, μ i * z i := by
  unfold scalarQuadraticPotentialDerivative
  simp only [smul_apply, sum_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The pair terms annihilate the common translation direction. -/
theorem orderedScalarPotentialDerivative_one {n : ℕ} (μ z : ScalarVector n) :
    orderedScalarPotentialDerivative μ z (fun _ => 1) = ∑ i, μ i * z i := by
  unfold orderedScalarPotentialDerivative
  simp only [add_apply, sum_apply,
    smul_apply, sub_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, sub_self, mul_zero,
    Finset.sum_const_zero, add_zero]
  exact scalarQuadraticPotentialDerivative_one μ z

/-- Actual action-reaction cancellation for the original scalarForce.
The already proved finite-pair incidence identity supplies cancellation. -/
theorem scalarForce_weighted_sum_zero {n : ℕ} (μ z : ScalarVector n)
    (hz : z ∈ ambientChamber n) :
    (∑ i, μ i * FourBody.ScalarGeometry.scalarForce μ z i) = 0 := by
  have hd : (∑ i, μ i * (z i - FourBody.ScalarGeometry.scalarForce μ z i)) =
      ∑ i, μ i * z i := by
    calc
      _ = scalarPotentialDerivative μ z (fun _ => 1) := by
        symm
        simpa only [mul_one] using scalarPotentialDerivative_apply μ z (fun _ => 1)
      _ = orderedScalarPotentialDerivative μ z (fun _ => 1) := by
        rw [orderedScalarPotentialDerivative_eq μ z hz]
      _ = _ := orderedScalarPotentialDerivative_one μ z
  simp only [mul_sub, Finset.sum_sub_distrib] at hd
  linarith

theorem scalar_residual_weighted_sum_zero {n : ℕ} (μ z : ScalarVector n)
    (hz : z ∈ ambientChamber n) (hcenter : z ∈ FourBody.ScalarGeometry.ScalarW μ) :
    (∑ i, μ i * (z i - FourBody.ScalarGeometry.scalarForce μ z i)) = 0 := by
  change (∑ i, μ i * z i) = 0 at hcenter
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hcenter, scalarForce_weighted_sum_zero μ z hz, sub_self]

/-- The actual constrained first derivative vanishes exactly at the original
normalized scalar force equations, using the paper's common-residual route. -/
theorem scalarPotential_constraint_critical_iff_root {n : ℕ} (μ z : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (hz : z ∈ ambientChamber n)
    (hcenter : z ∈ FourBody.ScalarGeometry.ScalarW μ) :
    (∀ h : FourBody.ScalarGeometry.ScalarW μ, scalarPotentialDerivative μ z h.val = 0) ↔
      ∀ i, FourBody.ScalarGeometry.scalarForce μ z i = z i := by
  constructor
  · intro hderiv
    have hvanish : ∀ h : ScalarVector n, h ∈ FourBody.ScalarGeometry.ScalarW μ →
        (∑ i, μ i * (z i - FourBody.ScalarGeometry.scalarForce μ z i) * h i) = 0 := by
      intro h hh
      rw [← scalarPotentialDerivative_apply]
      exact hderiv ⟨h, hh⟩
    have hzero := scalar_weighted_center_annihilator_zero μ
      (fun i => z i - FourBody.ScalarGeometry.scalarForce μ z i) hμ hvanish
      (scalar_residual_weighted_sum_zero μ z hz hcenter)
    intro i
    exact (sub_eq_zero.mp (hzero i)).symm
  · intro hroot h
    rw [scalarPotentialDerivative_apply]
    simp only [hroot, sub_self, mul_zero, zero_mul, Finset.sum_const_zero]

theorem scalar_centered_chamber_isOpen {n : ℕ} (μ : ScalarVector n) :
    IsOpen (FourBody.ScalarGeometry.chamber μ) :=
  (ambientChamber_isOpen n).preimage continuous_subtype_val

theorem scalarPotentialRestricted_hasFDerivAt {n : ℕ} (μ : ScalarVector n)
    (z : FourBody.ScalarGeometry.ScalarW μ)
    (hz : z ∈ FourBody.ScalarGeometry.chamber μ) :
    HasFDerivAt (fun w : FourBody.ScalarGeometry.ScalarW μ => scalarPotential μ w.val)
      ((scalarPotentialDerivative μ z.val).comp
        (FourBody.ScalarGeometry.ScalarW μ).subtypeL) z := by
  exact (scalarPotential_hasFDerivAt μ z.val hz).comp z
    (FourBody.ScalarGeometry.ScalarW μ).subtypeL.hasFDerivAt

/-- Fermat's theorem is applied to the actual centered subspace, not to an
assumed external calculus certificate. -/
theorem scalarPotential_centered_minimizer_root {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (z : FourBody.ScalarGeometry.ScalarW μ)
    (hz : z ∈ FourBody.ScalarGeometry.chamber μ)
    (hmin : IsMinOn (fun w : FourBody.ScalarGeometry.ScalarW μ => scalarPotential μ w.val)
      (FourBody.ScalarGeometry.chamber μ) z) :
    ∀ i, FourBody.ScalarGeometry.scalarForce μ z.val i = z.val i := by
  have hd := (hmin.isLocalMin ((scalar_centered_chamber_isOpen μ).mem_nhds hz)).hasFDerivAt_eq_zero
    (scalarPotentialRestricted_hasFDerivAt μ z hz)
  apply (scalarPotential_constraint_critical_iff_root μ z.val hμ hz z.property).mp
  intro h
  have he := DFunLike.congr_fun hd h
  simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    zero_apply] using he

theorem scalarPotential_centered_compact_sublevel {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (c : ℝ) :
    IsCompact {z : FourBody.ScalarGeometry.ScalarW μ |
      z ∈ FourBody.ScalarGeometry.chamber μ ∧ scalarPotential μ z.val ≤ c} := by
  have he : IsClosedEmbedding
      (fun z : FourBody.ScalarGeometry.ScalarW μ => z.val) :=
    (FourBody.ScalarGeometry.ScalarW μ).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal
  exact he.isCompact_preimage (scalarPotential_compact_sublevel μ hμ c)

/-- Direct existence in the paper's centered chamber from its compact
sublevels. This supplements the ambient translation argument independently. -/
theorem scalarPotential_centered_exists_minimizer {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) :
    ∃ z : FourBody.ScalarGeometry.ScalarW μ,
      z ∈ FourBody.ScalarGeometry.chamber μ ∧
      IsMinOn (fun w : FourBody.ScalarGeometry.ScalarW μ => scalarPotential μ w.val)
        (FourBody.ScalarGeometry.chamber μ) z := by
  obtain ⟨z0, hz0⟩ := FourBody.ScalarGeometry.chamber_nonempty μ hμ
  let S : Set (FourBody.ScalarGeometry.ScalarW μ) :=
    {z | z ∈ FourBody.ScalarGeometry.chamber μ ∧ scalarPotential μ z.val ≤ scalarPotential μ z0.val}
  have hcompact : IsCompact S := scalarPotential_centered_compact_sublevel μ hμ _
  have hnonempty : S.Nonempty := ⟨z0, hz0, le_rfl⟩
  have hcontinuous : ContinuousOn
      (fun w : FourBody.ScalarGeometry.ScalarW μ => scalarPotential μ w.val) S := by
    intro z hz
    exact ((scalarPotential_continuousAt μ z.val hz.1).comp
      continuous_subtype_val.continuousAt).continuousWithinAt
  obtain ⟨z, hz, hmin⟩ := hcompact.exists_isMinOn hnonempty hcontinuous
  refine ⟨z, hz.1, ?_⟩
  intro y hy
  by_cases hv : scalarPotential μ y.val ≤ scalarPotential μ z0.val
  · exact hmin ⟨hy, hv⟩
  · exact hz.2.trans (le_of_lt (lt_of_not_ge hv))

end FourBody.ScalarMinimizer

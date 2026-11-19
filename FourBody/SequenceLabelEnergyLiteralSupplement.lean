import FourBody.InternalEquationLimits
import FourBody.VerticalPairing

set_option autoImplicit false
set_option warningAsError true

/-!
STATIC literal original-Label i<j energy bridge for v2 S3-U35.
Frozen original Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

Rather than assuming the energy or v=0, restrict the mass by the actual
block-label indicator, pair the actual individual zero vertical fields
on all original four labels, and filter the same original i<j pairs.
This also handles a singleton block: its pair sum is empty.

No Lean/Lake/checker has validated this candidate. The previously frozen
Extreme18 and External14 modules are unchanged.
-/

noncomputable section
open scoped BigOperators
namespace FourBody.SequenceLabelEnergyLiteralSupplement

/-- Removing masses outside J is exactly the erased sum over J. -/
theorem restricted_label_vertical_force (m : Masses) (J : Finset Label)
    (P : Configuration) (v : Label → ℝ) (i : Label) :
    VerticalEnergy.verticalForce (fun j => if j ∈ J then m j else 0) P v i =
      ∑ j ∈ J.erase i, m j * (v i - v j) / dist (P i) (P j) ^ 3 := by
  classical
  rw [VerticalEnergy.verticalForce]
  calc
    (∑ j ∈ (Finset.univ : Finset Label).erase i,
        (if j ∈ J then m j else 0) * (v i - v j) / dist (P i) (P j) ^ 3) =
        ∑ j ∈ (Finset.univ : Finset Label).erase i,
          if j ∈ J then m j * (v i - v j) / dist (P i) (P j) ^ 3 else 0 := by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hj : j ∈ J <;> simp only [hj, if_true, if_false, zero_mul, zero_div]
    _ = ∑ j ∈ ((Finset.univ : Finset Label).erase i).filter (fun j => j ∈ J),
        m j * (v i - v j) / dist (P i) (P j) ^ 3 := by
      rw [Finset.sum_filter]
    _ = ∑ j ∈ J.erase i, m j * (v i - v j) / dist (P i) (P j) ^ 3 := by
      apply Finset.sum_congr
      · ext j
        simp
      · intro j _hj
        rfl

/-- At an actual member the restricted force is the actual physical g_y. -/
theorem restricted_block_vertical_force_eq_actual (m : Masses)
    (d : OrderedClusterDatum) (P : Configuration) (a : BlockIndex d)
    (i : Label) (hi : i ∈ datumBlockLabels d a) :
    VerticalEnergy.verticalForce
        (fun j => if j ∈ datumBlockLabels d a then m j else 0) P
        (fun j => P j 1) i =
      NewtonFieldLimits.physicalInternalField m d P i 1 := by
  classical
  have himem : i ∈ datumBlock d a := by
    simpa only [datumBlockLabels, List.mem_toFinset] using hi
  rw [restricted_label_vertical_force, NewtonFieldLimits.physicalInternalField,
    blockOf_eq_of_mem d himem]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, Reuse.physicalNewtonForce,
    PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Literal original four-label unordered pairing over an arbitrary actual J.
Only its individual force equations enter; no centering or v=0 is assumed. -/
theorem original_label_block_energy_zero (m : Masses) (J : Finset Label)
    (P : Configuration) (v : Label → ℝ)
    (hforce : ∀ i ∈ J, VerticalEnergy.verticalForce
      (fun j => if j ∈ J then m j else 0) P v i = 0) :
    (∑ p ∈ (VerticalEnergy.orderedPairs 4).filter
        (fun p => p.1 ∈ J ∧ p.2 ∈ J),
      m p.1 * m p.2 * (v p.1 - v p.2) ^ 2 /
        dist (P p.1) (P p.2) ^ 3) = 0 := by
  classical
  have hpair :
      (∑ i : Label, (if i ∈ J then m i else 0) * v i *
        VerticalEnergy.verticalForce (fun j => if j ∈ J then m j else 0) P v i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    by_cases hi : i ∈ J
    · rw [hforce i hi, mul_zero]
    · simp only [hi, if_false, zero_mul]
  have henergy :=
    (VerticalEnergy.vertical_force_pairing (fun j => if j ∈ J then m j else 0) P v).symm.trans hpair
  calc
    (∑ p ∈ (VerticalEnergy.orderedPairs 4).filter
        (fun p => p.1 ∈ J ∧ p.2 ∈ J),
      m p.1 * m p.2 * (v p.1 - v p.2) ^ 2 /
        dist (P p.1) (P p.2) ^ 3) =
        ∑ p ∈ VerticalEnergy.orderedPairs 4,
          (if p.1 ∈ J then m p.1 else 0) *
            (if p.2 ∈ J then m p.2 else 0) * (v p.1 - v p.2) ^ 2 /
              dist (P p.1) (P p.2) ^ 3 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases h₁ : p.1 ∈ J <;> by_cases h₂ : p.2 ∈ J <;>
        simp only [h₁, h₂, and_self, and_false, false_and,
          if_true, if_false, mul_zero, zero_mul, zero_div]
    _ = 0 := henergy

/-- The actual individual limit equations give the manuscript's Label i<j sum.
The original label order, true masses and true Euclidean distances remain.
This theorem is proved before any vertical-vanishing conclusion is used. -/
theorem internal_limit_original_label_vertical_energy_zero {m : Masses}
    {y : Label → ℝ} {P₀ : Configuration}
    (heq : InternalEquationLimits.InternalEquationAtLimit m y P₀)
    (a : BlockIndex (VerticalPartition.verticalPartitionDatum y)) :
    (∑ p ∈ (VerticalEnergy.orderedPairs 4).filter
        (fun p =>
          p.1 ∈ datumBlockLabels (VerticalPartition.verticalPartitionDatum y) a ∧
          p.2 ∈ datumBlockLabels (VerticalPartition.verticalPartitionDatum y) a),
      m p.1 * m p.2 * (P₀ p.1 1 - P₀ p.2 1) ^ 2 /
        dist (P₀ p.1) (P₀ p.2) ^ 3) = 0 := by
  apply original_label_block_energy_zero m
    (datumBlockLabels (VerticalPartition.verticalPartitionDatum y) a) P₀
    (fun i => P₀ i 1)
  intro i hi
  rw [restricted_block_vertical_force_eq_actual m _ P₀ a i hi]
  exact (heq i).2

end FourBody.SequenceLabelEnergyLiteralSupplement

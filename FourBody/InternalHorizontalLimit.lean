import FourBody.InternalEquationLimits
import FourBody.SequenceBlockIndices

/-!
# Vertical vanishing at the actual internal limit

Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD,
actual individual limit equations and the pairing at lines 471--478.
The collision separation and mass center come from the proved compactness
route. The force-zero input to VerticalPairing is obtained by the literal
erased finite sum bridge, not by assuming energy or a seed certificate.
The initial natural internal label order is still provisional; a final
ascending-u list must be constructed before claiming IsSeed.
All new proof bodies remain uncompiled.
-/

noncomputable section
open Filter

namespace FourBody.InternalHorizontalLimit

theorem internal_limit_vertical_zero {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    {P₀ : Configuration}
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀)
    (heq : InternalEquationLimits.InternalEquationAtLimit m y P₀) :
    ∀ i : Label, P₀ i 1 = 0 := by
  intro i
  let d := VerticalPartition.verticalPartitionDatum y
  let a : BlockIndex d := blockOf d i
  have hcollision : ∀ j k : InternalIndex d a, j ≠ k →
      P₀ (internalLabel d a j) ≠ P₀ (internalLabel d a k) := by
    intro j k hjk
    have hlabel : internalLabel d a j ≠ internalLabel d a k :=
      fun h => hjk (SequenceBlockIndices.internalLabel_injective d a h)
    have hd : 0 < dist (P₀ (internalLabel d a j)) (P₀ (internalLabel d a k)) :=
      ((ScaleConstants.constants_positive m hm).2.1).trans_le
        (hdata.2.2.2 a _ _ (SequenceBlockIndices.internalLabel_mem d a j)
          (SequenceBlockIndices.internalLabel_mem d a k) hlabel)
    exact dist_pos.mp hd
  have hcenter := SequenceBlockIndices.indexed_coordinate_center_zero m d P₀ a 1
    (hdata.2.2.1 a)
  have hforce : ∀ j : InternalIndex d a,
      VerticalEnergy.verticalForce (fun k => m (internalLabel d a k))
        (fun k => P₀ (internalLabel d a k))
        (fun k => P₀ (internalLabel d a k) 1) j = 0 := by
    intro j
    rw [SequenceBlockIndices.verticalForce_eq_actual_internal_field]
    exact (heq (internalLabel d a j)).2
  have hv := VerticalEnergy.vertical_coordinates_eq_zero_of_force_zero
    (fun j : InternalIndex d a => m (internalLabel d a j))
    (fun j : InternalIndex d a => P₀ (internalLabel d a j))
    (fun j => hm (internalLabel d a j)) hcollision hcenter hforce
  obtain ⟨j, hj⟩ := SequenceBlockIndices.internalLabel_surjective d a
    (label_mem_blockOf d i)
  simpa only [hj] using hv j

/-- The horizontal values of each actual block are distinct, a derived
condition permitting their final increasing order. No order is assumed. -/
theorem internal_limit_horizontal_injective {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    {P₀ : Configuration}
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀)
    (heq : InternalEquationLimits.InternalEquationAtLimit m y P₀)
    (a : BlockIndex (VerticalPartition.verticalPartitionDatum y)) :
    Function.Injective (fun j : InternalIndex (VerticalPartition.verticalPartitionDatum y) a =>
      P₀ (internalLabel (VerticalPartition.verticalPartitionDatum y) a j) 0) := by
  let d := VerticalPartition.verticalPartitionDatum y
  have hcollision : ∀ j k : InternalIndex d a, j ≠ k →
      P₀ (internalLabel d a j) ≠ P₀ (internalLabel d a k) := by
    intro j k hjk
    have hlabel : internalLabel d a j ≠ internalLabel d a k :=
      fun h => hjk (SequenceBlockIndices.internalLabel_injective d a h)
    exact dist_pos.mp (((ScaleConstants.constants_positive m hm).2.1).trans_le
      (hdata.2.2.2 a _ _ (SequenceBlockIndices.internalLabel_mem d a j)
        (SequenceBlockIndices.internalLabel_mem d a k) hlabel))
  exact VerticalEnergy.horizontal_injective_of_vertical_zero
    (fun j : InternalIndex d a => P₀ (internalLabel d a j)) hcollision
    (fun j => internal_limit_vertical_zero hm hdata heq (internalLabel d a j))

/-- Original inputs alone produce the simultaneous unscaled/scaled limits,
the actual internal equations and vertical vanishing on the SAME φ. -/
theorem exists_horizontal_internal_limit {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration}
    (hs : Tendsto s atTop atTop) (hq : ∀ ν, IsSolution m (s ν) (q ν)) :
    ∃ φ : ℕ → ℕ, ∃ y : Label → ℝ, ∃ P₀ : Configuration,
      SequenceStart.InitialVerticalLimit m s q φ y ∧
      InternalSubsequence.InternalLimitData m s q φ y P₀ ∧
      InternalEquationLimits.InternalEquationAtLimit m y P₀ ∧
      (∀ i : Label, P₀ i 1 = 0) ∧
      (∀ a : BlockIndex (VerticalPartition.verticalPartitionDatum y),
        Function.Injective
          (fun j : InternalIndex (VerticalPartition.verticalPartitionDatum y) a =>
            P₀ (internalLabel (VerticalPartition.verticalPartitionDatum y) a j) 0)) := by
  obtain ⟨φ, y, P₀, hlim, hdata, heq, _houter⟩ :=
    InternalEquationLimits.exists_internal_equation_limit hm hs hq
  exact ⟨φ, y, P₀, hlim, hdata, heq,
    internal_limit_vertical_zero hm hdata heq,
    internal_limit_horizontal_injective hm hdata heq⟩

end FourBody.InternalHorizontalLimit

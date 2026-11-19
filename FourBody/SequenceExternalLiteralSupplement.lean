import FourBody.ExternalNormBounds
import FourBody.PhysicalSequenceRows
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Literal exterior-field supplements for the frozen original Pro v2,
SHA256 97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

All fields are the actual physical fields on the actual labeled tuple.
The common positive cross distance and common eventual tail are derived
from CrossSeparation. The one-block case uses no minimum of cross pairs,
no epsilon hypothesis, and no physical separation assumption.

STATIC CANDIDATE ONLY: no Lean/Lake/checker invocation has been performed.
The imported actual field/row candidates also require final real verification.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open scoped BigOperators
open Filter

namespace FourBody.SequenceExternalLiteralSupplement

/-- The same actual field bound controls the actual positive block-mass mean. -/
theorem physical_external_mean_norm_bound {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (q : Configuration) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j : Label, blockOf d i ≠ blockOf d j →
      δ ≤ dist (q i) (q j)) (a : BlockIndex d) :
    ‖NewtonFieldLimits.physicalExternalMean m d q a‖ ≤ totalMass m / δ ^ 2 := by
  exact ExternalNormBounds.actual_block_mean_norm_bound hm d
    (NewtonFieldLimits.physicalExternalField m d q) a (totalMass m / δ ^ 2)
    (ExternalNormBounds.actual_external_norm_bound hm d q hδ hsep)

/-- Literal Euclidean deviation bound; it holds for every actual block mean. -/
theorem physical_external_deviation_norm_bound {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (q : Configuration) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j : Label, blockOf d i ≠ blockOf d j →
      δ ≤ dist (q i) (q j)) (i : Label) (a : BlockIndex d) :
    ‖NewtonFieldLimits.physicalExternalField m d q i -
      NewtonFieldLimits.physicalExternalMean m d q a‖ ≤
      2 * totalMass m / δ ^ 2 := by
  calc
    ‖NewtonFieldLimits.physicalExternalField m d q i -
        NewtonFieldLimits.physicalExternalMean m d q a‖ ≤
        ‖NewtonFieldLimits.physicalExternalField m d q i‖ +
          ‖NewtonFieldLimits.physicalExternalMean m d q a‖ := norm_sub_le _ _
    _ ≤ totalMass m / δ ^ 2 + totalMass m / δ ^ 2 :=
      add_le_add (ExternalNormBounds.actual_external_norm_bound hm d q hδ hsep i)
        (physical_external_mean_norm_bound hm d q hδ hsep a)
    _ = 2 * totalMass m / δ ^ 2 := by ring

/-- ONE derived δ and ONE eventual tail control fields, means and deviations. -/
theorem exists_actual_eventual_external_deviation_bound {m : Masses}
    (hm : PositiveMasses m) {s : ℕ → ℝ} {q : ℕ → Configuration}
    {φ : ℕ → ℕ} {y : Label → ℝ}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ν in atTop,
      (∀ i : Label, ‖NewtonFieldLimits.physicalExternalField m
        (VerticalPartition.verticalPartitionDatum y) (q (φ ν)) i‖ ≤
          totalMass m / δ ^ 2) ∧
      (∀ a : BlockIndex (VerticalPartition.verticalPartitionDatum y),
        ‖NewtonFieldLimits.physicalExternalMean m
          (VerticalPartition.verticalPartitionDatum y) (q (φ ν)) a‖ ≤
            totalMass m / δ ^ 2) ∧
      ∀ (i : Label) (a : BlockIndex (VerticalPartition.verticalPartitionDatum y)),
        ‖NewtonFieldLimits.physicalExternalField m
          (VerticalPartition.verticalPartitionDatum y) (q (φ ν)) i -
          NewtonFieldLimits.physicalExternalMean m
            (VerticalPartition.verticalPartitionDatum y) (q (φ ν)) a‖ ≤
              2 * totalMass m / δ ^ 2 := by
  obtain ⟨δ, hδ, hsep⟩ := CrossSeparation.exists_eventual_cross_separation hlim
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hsep] with ν hν
  refine ⟨?_, ?_, ?_⟩
  · exact ExternalNormBounds.actual_external_norm_bound hm _ _ hδ hν
  · exact physical_external_mean_norm_bound hm _ _ hδ hν
  · intro i a
    exact physical_external_deviation_norm_bound hm _ _ hδ hν i a

/-- The arbitrary input sequence supplies its own initial limit and bounds. -/
theorem exists_original_subsequence_external_deviation_bound {m : Masses}
    (hm : PositiveMasses m) {s : ℕ → ℝ} {q : ℕ → Configuration}
    (hs : Tendsto s atTop atTop) (hq : ∀ ν, IsSolution m (s ν) (q ν)) :
    ∃ φ : ℕ → ℕ, ∃ y : Label → ℝ, ∃ δ : ℝ,
      SequenceStart.InitialVerticalLimit m s q φ y ∧ 0 < δ ∧
      ∀ᶠ ν in atTop,
        (∀ i : Label, ‖NewtonFieldLimits.physicalExternalField m
          (VerticalPartition.verticalPartitionDatum y) (q (φ ν)) i‖ ≤
            totalMass m / δ ^ 2) ∧
        (∀ a : BlockIndex (VerticalPartition.verticalPartitionDatum y),
          ‖NewtonFieldLimits.physicalExternalMean m
            (VerticalPartition.verticalPartitionDatum y) (q (φ ν)) a‖ ≤
              totalMass m / δ ^ 2) ∧
        ∀ (i : Label) (a : BlockIndex (VerticalPartition.verticalPartitionDatum y)),
          ‖NewtonFieldLimits.physicalExternalField m
            (VerticalPartition.verticalPartitionDatum y) (q (φ ν)) i -
            NewtonFieldLimits.physicalExternalMean m
              (VerticalPartition.verticalPartitionDatum y) (q (φ ν)) a‖ ≤
                2 * totalMass m / δ ^ 2 := by
  obtain ⟨φ, y, hlim⟩ := SequenceStart.exists_initial_vertical_limit hm hs hq
  obtain ⟨δ, hδ, hbounds⟩ := exists_actual_eventual_external_deviation_bound hm hlim
  exact ⟨φ, y, δ, hlim, hδ, hbounds⟩

/-- A genuine one-block datum has one actual block index for all labels. -/
theorem blockOf_eq_of_one_block (d : OrderedClusterDatum)
    (hblocks : d.blocks.length = 1) (i j : Label) : blockOf d i = blockOf d j := by
  exact (Fin.cast_injective hblocks)
    (Subsingleton.elim (Fin.cast hblocks (blockOf d i))
      (Fin.cast hblocks (blockOf d j)))

/-- Every summand is absent in a one-block actual exterior field. -/
theorem physical_external_field_eq_zero_of_one_block (m : Masses)
    (d : OrderedClusterDatum) (q : Configuration) (hblocks : d.blocks.length = 1)
    (i : Label) : NewtonFieldLimits.physicalExternalField m d q i = 0 := by
  classical
  unfold NewtonFieldLimits.physicalExternalField
  apply Finset.sum_eq_zero
  intro j _hj
  have hj : blockOf d j = blockOf d i := blockOf_eq_of_one_block d hblocks j i
  simp [hj]

/-- The actual weighted external mean is also exactly zero for one block. -/
theorem physical_external_mean_eq_zero_of_one_block (m : Masses)
    (d : OrderedClusterDatum) (q : Configuration) (hblocks : d.blocks.length = 1)
    (a : BlockIndex d) : NewtonFieldLimits.physicalExternalMean m d q a = 0 := by
  have hfield : NewtonFieldLimits.physicalExternalField m d q = 0 := by
    funext i
    exact physical_external_field_eq_zero_of_one_block m d q hblocks i
  rw [NewtonFieldLimits.physicalExternalMean, hfield]
  simp [datumBlockMean]

/-- The literal exterior deviation has zero norm in the one-block case. -/
theorem physical_external_deviation_norm_eq_zero_of_one_block (m : Masses)
    (d : OrderedClusterDatum) (q : Configuration) (hblocks : d.blocks.length = 1)
    (i : Label) (a : BlockIndex d) :
    ‖NewtonFieldLimits.physicalExternalField m d q i -
      NewtonFieldLimits.physicalExternalMean m d q a‖ = 0 := by
  rw [physical_external_field_eq_zero_of_one_block m d q hblocks i,
    physical_external_mean_eq_zero_of_one_block m d q hblocks a, sub_self, norm_zero]

/-- Reassemble the actual H/Y mass-mean rows as a true Point identity. -/
theorem physical_external_mean_eq_anisotropy_of_coordinates {m : Masses}
    (hm : PositiveMasses m) {d : OrderedClusterDatum} {s : ℝ} (hs : 0 < s)
    {h : BlowupCoordinates m d} {q : Configuration} (hq : IsSolution m s q)
    (hh : CoordinatesOfConfiguration m d (epsilon s) q h) (a : BlockIndex d) :
    NewtonFieldLimits.physicalExternalMean m d q a =
      anisotropy s (datumBlockMean m d q a) := by
  have he : epsilon s ≠ 0 := ne_of_gt (SequenceStart.epsilon_pos hs)
  have hx : datumBlockMean m d q a 0 / epsilon s =
      (epsilon s) ^ 2 * NewtonFieldLimits.physicalExternalMean m d q a 0 := by
    calc
      datumBlockMean m d q a 0 / epsilon s = outerH h a := by
        simpa only [horizontalCenterCoordinate] using (hh.2.1 a).symm
      _ = _ := PhysicalSequenceRows.horizontal_mean_row hm hs hq hh a
  have hmx : datumBlockMean m d q a 0 =
      (epsilon s) ^ 3 * NewtonFieldLimits.physicalExternalMean m d q a 0 := by
    calc
      datumBlockMean m d q a 0 =
          ((epsilon s) ^ 2 * NewtonFieldLimits.physicalExternalMean m d q a 0) *
            epsilon s := (div_eq_iff he).mp hx
      _ = _ := by ring
  have hscale : s * (epsilon s) ^ 3 = 1 := by
    rw [SequenceStart.epsilon_cube hs]
    exact mul_inv_cancel₀ (ne_of_gt hs)
  ext k
  fin_cases k
  · change NewtonFieldLimits.physicalExternalMean m d q a 0 = s * datumBlockMean m d q a 0
    calc
      NewtonFieldLimits.physicalExternalMean m d q a 0 =
          (s * (epsilon s) ^ 3) * NewtonFieldLimits.physicalExternalMean m d q a 0 := by
            rw [hscale, one_mul]
      _ = s * datumBlockMean m d q a 0 := by rw [mul_assoc, ← hmx]
  · change NewtonFieldLimits.physicalExternalMean m d q a 1 = datumBlockMean m d q a 1
    exact (PhysicalSequenceRows.vertical_mean_row hm hs hq hh a).symm.trans
      (by simpa only [verticalCenterCoordinate] using hh.2.2.1 a)

/-- The original solution itself supplies the actual inverse mean coordinates. -/
theorem physical_external_mean_eq_anisotropy {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) {s : ℝ} (hs : 0 < s) {q : Configuration}
    (hq : IsSolution m s q) (a : BlockIndex d) :
    NewtonFieldLimits.physicalExternalMean m d q a =
      anisotropy s (datumBlockMean m d q a) := by
  let qW : W m := ⟨q, by
    change centerLM m q = 0
    exact solution_center_zero m hs hq⟩
  let h : BlowupCoordinates m d := meanInverse hm d (epsilon s) qW
  have he : epsilon s ≠ 0 := ne_of_gt (SequenceStart.epsilon_pos hs)
  have hh : CoordinatesOfConfiguration m d (epsilon s) q h := by
    apply (represents_iff_coordinatesOfConfiguration hm he h q).mp
    apply (represents_iff_eq_physicalCoordinates _ _ _).mpr
    exact (congrArg Subtype.val (coordinateQ_meanInverse hm d he qW)).symm
  exact physical_external_mean_eq_anisotropy_of_coordinates hm hs hq hh a

/-- The two actual internal rows are one literal Point equation. -/
theorem physical_scaled_internal_equation_of_coordinates {m : Masses}
    (hm : PositiveMasses m) {d : OrderedClusterDatum} {s : ℝ} (hs : 0 < s)
    {h : BlowupCoordinates m d} {q : Configuration} (hq : IsSolution m s q)
    (hh : CoordinatesOfConfiguration m d (epsilon s) q h) (i : Label) :
    NewtonFieldLimits.physicalInternalField m d
        (InternalCoordinates.internalVectors m d (epsilon s) q) i +
      (epsilon s) ^ 2 • (NewtonFieldLimits.physicalExternalField m d q i -
        NewtonFieldLimits.physicalExternalMean m d q (blockOf d i)) =
      !₂[InternalCoordinates.internalVectors m d (epsilon s) q i 0,
        (epsilon s) ^ 3 * InternalCoordinates.internalVectors m d (epsilon s) q i 1] := by
  ext k
  fin_cases k
  · simpa [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] using
      PhysicalSequenceRows.internal_horizontal_row hm hs hq hh i
  · simpa [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] using
      PhysicalSequenceRows.internal_vertical_row hm hs hq hh i

/-- The original solution supplies its own coordinates for the scaled equation. -/
theorem physical_scaled_internal_equation {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) {s : ℝ} (hs : 0 < s) {q : Configuration}
    (hq : IsSolution m s q) (i : Label) :
    NewtonFieldLimits.physicalInternalField m d
        (InternalCoordinates.internalVectors m d (epsilon s) q) i +
      (epsilon s) ^ 2 • (NewtonFieldLimits.physicalExternalField m d q i -
        NewtonFieldLimits.physicalExternalMean m d q (blockOf d i)) =
      !₂[InternalCoordinates.internalVectors m d (epsilon s) q i 0,
        (epsilon s) ^ 3 * InternalCoordinates.internalVectors m d (epsilon s) q i 1] := by
  let qW : W m := ⟨q, by
    change centerLM m q = 0
    exact solution_center_zero m hs hq⟩
  let h : BlowupCoordinates m d := meanInverse hm d (epsilon s) qW
  have he : epsilon s ≠ 0 := ne_of_gt (SequenceStart.epsilon_pos hs)
  have hh : CoordinatesOfConfiguration m d (epsilon s) q h := by
    apply (represents_iff_coordinatesOfConfiguration hm he h q).mp
    apply (represents_iff_eq_physicalCoordinates _ _ _).mpr
    exact (congrArg Subtype.val (coordinateQ_meanInverse hm d he qW)).symm
  exact physical_scaled_internal_equation_of_coordinates hm hs hq hh i

/-- The actual horizontal mean row has the exact inverse-square orientation. -/
theorem physical_horizontal_mean_inverse_row {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {s : ℝ} (hs : 0 < s)
    {h : BlowupCoordinates m d} {q : Configuration} (hq : IsSolution m s q)
    (hh : CoordinatesOfConfiguration m d (epsilon s) q h) (a : BlockIndex d) :
    NewtonFieldLimits.physicalExternalMean m d q a 0 =
      (epsilon s)⁻¹ ^ 2 * outerH h a := by
  have he : epsilon s ≠ 0 := ne_of_gt (SequenceStart.epsilon_pos hs)
  rw [PhysicalSequenceRows.horizontal_mean_row hm hs hq hh a]
  field_simp [he]

/-- Literal physical center formula, with no prescribed coordinate witness. -/
theorem physical_horizontal_mean_inverse_identity {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) {s : ℝ} (hs : 0 < s) {q : Configuration}
    (hq : IsSolution m s q) (a : BlockIndex d) :
    NewtonFieldLimits.physicalExternalMean m d q a 0 =
      (epsilon s)⁻¹ ^ 2 * horizontalCenterCoordinate m d (epsilon s) q a := by
  let qW : W m := ⟨q, by
    change centerLM m q = 0
    exact solution_center_zero m hs hq⟩
  let h : BlowupCoordinates m d := meanInverse hm d (epsilon s) qW
  have he : epsilon s ≠ 0 := ne_of_gt (SequenceStart.epsilon_pos hs)
  have hh : CoordinatesOfConfiguration m d (epsilon s) q h := by
    apply (represents_iff_coordinatesOfConfiguration hm he h q).mp
    apply (represents_iff_eq_physicalCoordinates _ _ _).mpr
    exact (congrArg Subtype.val (coordinateQ_meanInverse hm d he qW)).symm
  calc
    NewtonFieldLimits.physicalExternalMean m d q a 0 =
        (epsilon s)⁻¹ ^ 2 * outerH h a :=
      physical_horizontal_mean_inverse_row hm hs hq hh a
    _ = _ := by rw [hh.2.1 a]

end FourBody.SequenceExternalLiteralSupplement

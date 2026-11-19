import FourBody.HorizontalCubicBound
import FourBody.Diameter

set_option autoImplicit false

/-!
STATIC source-faithful supplement for frozen Pro v2 S3-U39, lines 492--496,
and its exact H = epsilon^2 Emean_x consequence S3-U40, lines 498--503.
The original source SHA256 is
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

The coefficient 3 is obtained from the actual pair-difference horizontal
diameter, not by adding two coordinate absolute bounds. Positive masses,
the literal physical solution equations, actual Newton forces, actual block
mass means, and a cross gap derived from the same selected original solution
sequence are retained. No sharp estimate is assumed in a theorem input.

This module has not been compiled or axiom-audited. No Lean/Lake process was
run while preparing it; all claims here remain pending machine verification.
-/

noncomputable section
open scoped BigOperators
open Filter
namespace FourBody.ScalarSupplement

/-- Both orientations of the actual maximum-minus-minimum range control
the absolute pair difference, without invoking a center or triangle bound. -/
theorem coordinate_abs_difference_le_diameter (t : Label → ℝ) (i j : Label) :
    |t i - t j| ≤ coordinateDiameter t := by
  apply abs_le.mpr
  constructor
  · have h := coordinate_difference_le_diameter t i j
    linarith
  · exact coordinate_difference_le_diameter t j i

/-- The physical pair difference has coefficient B = 3 M^(1/3), not 2B. -/
theorem horizontal_pair_diameter_bound_sharp {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : IsSolution m s q)
    (i j : Label) :
    |q i 0 - q j 0| ≤ SequenceStart.verticalBound m * epsilon s := by
  have h := (coordinate_abs_difference_le_diameter (fun k => q k 0) i j).trans
    (diameter_x hm hs hq)
  rw [SequenceStart.horizontal_root_factor hm hs] at h
  exact h

def horizontalExteriorConstantSharp (m : Masses) (δ : ℝ) : ℝ :=
  3 * (totalMass m) ^ ((4 : ℝ) / 3) / δ ^ 3

theorem horizontalExteriorConstantSharp_pos {m : Masses} (hm : PositiveMasses m)
    {δ : ℝ} (hδ : 0 < δ) : 0 < horizontalExteriorConstantSharp m δ := by
  exact div_pos
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos (totalMass_pos hm) _))
    (pow_pos hδ 3)

/-- Exact real-power simplification of the literal source coefficient. -/
theorem horizontalExteriorConstantSharp_eq {m : Masses} (hm : PositiveMasses m)
    (δ : ℝ) :
    (totalMass m / δ ^ 3) * SequenceStart.verticalBound m =
      horizontalExteriorConstantSharp m δ := by
  have hpow : (totalMass m) ^ ((4 : ℝ) / 3) =
      totalMass m * (totalMass m) ^ ((1 : ℝ) / 3) := by
    rw [show (4 : ℝ) / 3 = 1 + (1 : ℝ) / 3 by norm_num,
      Real.rpow_add (totalMass_pos hm), Real.rpow_one]
  unfold horizontalExteriorConstantSharp SequenceStart.verticalBound
  rw [hpow]
  ring

theorem physical_pair_horizontal_bound_sharp {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : IsSolution m s q)
    {δ : ℝ} (hδ : 0 < δ) (i j : Label) (hsep : δ ≤ dist (q i) (q j)) :
    |Reuse.physicalNewtonForce (m j) (q j) (q i) 0| ≤
      (m j / δ ^ 3) * (SequenceStart.verticalBound m * epsilon s) := by
  have hdist : 0 < dist (q i) (q j) := hδ.trans_le hsep
  have hcoefficient : 0 ≤ m j / dist (q i) (q j) ^ 3 :=
    div_nonneg (hm j).le (pow_pos hdist 3).le
  have hcoeff_le : m j / dist (q i) (q j) ^ 3 ≤ m j / δ ^ 3 :=
    div_le_div_of_nonneg_left (hm j).le (pow_pos hδ 3)
      (pow_le_pow_left₀ hδ.le hsep 3)
  have hdiff := horizontal_pair_diameter_bound_sharp hm hs hq i j
  rw [Reuse.physicalNewtonForce, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul, abs_mul, abs_of_nonneg hcoefficient]
  exact mul_le_mul hcoeff_le hdiff (abs_nonneg _)
    (div_nonneg (hm j).le (pow_pos hδ 3).le)

/-- The original external field, with the exact coefficient displayed. -/
theorem external_horizontal_bound_sharp {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) {s : ℝ} (hs : 0 < s)
    {q : Configuration} (hq : IsSolution m s q) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j : Label, blockOf d i ≠ blockOf d j → δ ≤ dist (q i) (q j))
    (i : Label) :
    |NewtonFieldLimits.physicalExternalField m d q i 0| ≤
      (3 * (totalMass m) ^ ((4 : ℝ) / 3) / δ ^ 3) * epsilon s := by
  classical
  have hcoord : NewtonFieldLimits.physicalExternalField m d q i 0 =
      ∑ j : Label, if blockOf d j ≠ blockOf d i then
        Reuse.physicalNewtonForce (m j) (q j) (q i) 0 else 0 := by
    simp only [NewtonFieldLimits.physicalExternalField, WithLp.ofLp_sum,
      Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _hj
    split_ifs <;> rfl
  rw [hcoord]
  calc
    |∑ j : Label, if blockOf d j ≠ blockOf d i then
        Reuse.physicalNewtonForce (m j) (q j) (q i) 0 else 0| ≤
      ∑ j : Label, |if blockOf d j ≠ blockOf d i then
        Reuse.physicalNewtonForce (m j) (q j) (q i) 0 else 0| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le
        (Finset.univ : Finset Label)
        (fun j => if blockOf d j ≠ blockOf d i then
          Reuse.physicalNewtonForce (m j) (q j) (q i) 0 else 0)
    _ ≤ ∑ j : Label,
        (m j / δ ^ 3) * (SequenceStart.verticalBound m * epsilon s) := by
      apply Finset.sum_le_sum
      intro j _hj
      by_cases hblock : blockOf d j ≠ blockOf d i
      · simp only [if_pos hblock]
        exact physical_pair_horizontal_bound_sharp hm hs hq hδ i j
          (hsep i j (Ne.symm hblock))
      · simp only [hblock, if_false, abs_zero]
        exact mul_nonneg (div_nonneg (hm j).le (pow_pos hδ 3).le)
          (mul_nonneg (SequenceStart.verticalBound_pos hm).le
            (SequenceStart.epsilon_pos hs).le)
    _ = ((totalMass m / δ ^ 3) * SequenceStart.verticalBound m) * epsilon s := by
      rw [← Finset.sum_mul, ← Finset.sum_div]
      unfold totalMass
      ring
    _ = (3 * (totalMass m) ^ ((4 : ℝ) / 3) / δ ^ 3) * epsilon s := by
      exact congrArg (fun A : ℝ => A * epsilon s)
        (horizontalExteriorConstantSharp_eq hm δ)

/-- Actual positive block mass averages preserve the same coefficient 3. -/
theorem external_mean_horizontal_bound_sharp {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) {s : ℝ} (hs : 0 < s)
    {q : Configuration} (hq : IsSolution m s q) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j : Label, blockOf d i ≠ blockOf d j → δ ≤ dist (q i) (q j))
    (a : BlockIndex d) :
    |NewtonFieldLimits.physicalExternalMean m d q a 0| ≤
      (3 * (totalMass m) ^ ((4 : ℝ) / 3) / δ ^ 3) * epsilon s := by
  exact HorizontalCubicBound.block_mean_abs_bound hm d
    (NewtonFieldLimits.physicalExternalField m d q) a 0 _
    (fun i => external_horizontal_bound_sharp hm d hs hq hδ hsep i)

/-- The literal physical mean equation transfers the same coefficient to H. -/
theorem horizontal_centers_cubic_bound_sharp {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {s : ℝ} (hs : 0 < s)
    {h : BlowupCoordinates m d} {q : Configuration} (hq : IsSolution m s q)
    (hh : CoordinatesOfConfiguration m d (epsilon s) q h)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j : Label, blockOf d i ≠ blockOf d j → δ ≤ dist (q i) (q j))
    (a : BlockIndex d) :
    |outerH h a| ≤
      (3 * (totalMass m) ^ ((4 : ℝ) / 3) / δ ^ 3) * (epsilon s) ^ 3 := by
  rw [PhysicalSequenceRows.horizontal_mean_row hm hs hq hh a,
    abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc
    (epsilon s) ^ 2 * |NewtonFieldLimits.physicalExternalMean m d q a 0| ≤
      (epsilon s) ^ 2 *
        ((3 * (totalMass m) ^ ((4 : ℝ) / 3) / δ ^ 3) * epsilon s) :=
      mul_le_mul_of_nonneg_left
        (external_mean_horizontal_bound_sharp hm d hs hq hδ hsep a) (sq_nonneg _)
    _ = (3 * (totalMass m) ^ ((4 : ℝ) / 3) / δ ^ 3) * (epsilon s) ^ 3 := by ring

/-- One actual sequence-derived gap gives one common eventual tail for all
original external fields and all actual block means, with exact coefficient 3. -/
theorem exists_eventual_external_horizontal_bound_sharp {m : Masses}
    (hm : PositiveMasses m) {s : ℕ → ℝ} {q : ℕ → Configuration}
    {φ : ℕ → ℕ} {y : Label → ℝ} (hq : ∀ ν, IsSolution m (s ν) (q ν))
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ν in atTop,
      (∀ i : Label, |NewtonFieldLimits.physicalExternalField m
        (VerticalPartition.verticalPartitionDatum y) (q (φ ν)) i 0| ≤
          (3 * (totalMass m) ^ ((4 : ℝ) / 3) / δ ^ 3) * epsilon (s (φ ν))) ∧
      (∀ a : BlockIndex (VerticalPartition.verticalPartitionDatum y),
        |NewtonFieldLimits.physicalExternalMean m (VerticalPartition.verticalPartitionDatum y)
          (q (φ ν)) a 0| ≤
            (3 * (totalMass m) ^ ((4 : ℝ) / 3) / δ ^ 3) * epsilon (s (φ ν))) := by
  obtain ⟨δ, hδ, hsep⟩ := CrossSeparation.exists_eventual_cross_separation hlim
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hsep] with ν hν
  have hs : 0 < s (φ ν) := lt_trans (by norm_num) (hlim.2.1 ν)
  exact ⟨fun i => external_horizontal_bound_sharp hm _ hs (hq (φ ν)) hδ hν i,
    fun a => external_mean_horizontal_bound_sharp hm _ hs (hq (φ ν)) hδ hν a⟩

/-- Natural bridge to the existing frozen Proposition 3.2 target. It
derives its sharp witness from the actual selected sequence, so any already
constructed internal-limit subsequence can use exactly the same φ and h. -/
theorem horizontal_centers_cubic_statement_sharp {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    (hq : ∀ ν, IsSolution m (s ν) (q ν))
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (h : ℕ → BlowupCoordinates m (VerticalPartition.verticalPartitionDatum y))
    (hh : ∀ ν, CoordinatesOfConfiguration m (VerticalPartition.verticalPartitionDatum y)
      (epsilon (s (φ ν))) (q (φ ν)) (h ν)) :
    FourBody.HorizontalCentersCubicBound m (VerticalPartition.verticalPartitionDatum y)
      (fun ν => epsilon (s (φ ν))) h := by
  obtain ⟨δ, hδ, hsep⟩ := CrossSeparation.exists_eventual_cross_separation hlim
  refine ⟨horizontalExteriorConstantSharp m δ,
    horizontalExteriorConstantSharp_pos hm hδ, ?_⟩
  filter_upwards [hsep] with ν hν
  intro a
  have hs : 0 < s (φ ν) := lt_trans (by norm_num) (hlim.2.1 ν)
  exact horizontal_centers_cubic_bound_sharp hm hs (hq (φ ν)) (hh ν) hδ hν a

/-- A source-facing endpoint whose only inputs are the arbitrary original
solution sequence and its diverging real anisotropy parameters. The selected
subsequence, physical coordinates, cross gap and sharp bounds are outputs. -/
theorem exists_original_sequence_sharp_cubic {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} (hs : Tendsto s atTop atTop)
    (hq : ∀ ν, IsSolution m (s ν) (q ν)) :
    ∃ φ : ℕ → ℕ, ∃ y : Label → ℝ,
      SequenceStart.InitialVerticalLimit m s q φ y ∧
      ∃ δ : ℝ, 0 < δ ∧
      ∃ h : ℕ → BlowupCoordinates m (VerticalPartition.verticalPartitionDatum y),
        (∀ ν, CoordinatesOfConfiguration m (VerticalPartition.verticalPartitionDatum y)
          (epsilon (s (φ ν))) (q (φ ν)) (h ν)) ∧
        ∀ᶠ ν in atTop,
          (∀ i : Label, |NewtonFieldLimits.physicalExternalField m
            (VerticalPartition.verticalPartitionDatum y) (q (φ ν)) i 0| ≤
              (3 * (totalMass m) ^ ((4 : ℝ) / 3) / δ ^ 3) * epsilon (s (φ ν))) ∧
          (∀ a : BlockIndex (VerticalPartition.verticalPartitionDatum y),
            |NewtonFieldLimits.physicalExternalMean m (VerticalPartition.verticalPartitionDatum y)
              (q (φ ν)) a 0| ≤
                (3 * (totalMass m) ^ ((4 : ℝ) / 3) / δ ^ 3) * epsilon (s (φ ν)) ∧
            |outerH (h ν) a| ≤
              (3 * (totalMass m) ^ ((4 : ℝ) / 3) / δ ^ 3) *
                (epsilon (s (φ ν))) ^ 3) := by
  obtain ⟨φ, y, hlim⟩ := SequenceStart.exists_initial_vertical_limit hm hs hq
  obtain ⟨δ, hδ, hsep⟩ := CrossSeparation.exists_eventual_cross_separation hlim
  obtain ⟨h, hh⟩ := VerticalPartition.exists_selected_mean_coordinates hm hq hlim.2.1
    (VerticalPartition.verticalPartitionDatum y)
  refine ⟨φ, y, hlim, δ, hδ, h, hh, ?_⟩
  filter_upwards [hsep] with ν hν
  have hsν : 0 < s (φ ν) := lt_trans (by norm_num) (hlim.2.1 ν)
  refine ⟨fun i => external_horizontal_bound_sharp hm _ hsν (hq (φ ν)) hδ hν i, ?_⟩
  intro a
  exact ⟨external_mean_horizontal_bound_sharp hm _ hsν (hq (φ ν)) hδ hν a,
    horizontal_centers_cubic_bound_sharp hm hsν (hq (φ ν)) (hh ν) hδ hν a⟩

end FourBody.ScalarSupplement

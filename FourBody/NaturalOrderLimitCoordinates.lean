import FourBody.HorizontalCubicBound
import FourBody.ScalarLimitEquations

/-!
# Actual limit coordinates before the final ascending-u reordering

Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
This is an honest intermediate representation: all coordinate, equation,
distance and cubic-bound conclusions below are obtained on the SAME φ
from original arbitrary solution sequences. The datum still uses the
provisional natural LABEL order within a height fiber. The limit is
therefore not asserted to satisfy IsSeed, whose increasing-u condition
requires an actual reordered datum and transport proof.
No main conclusion is supplied as an assumption; all bodies uncompiled.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace FourBody.NaturalOrderLimitCoordinates

def limitCoordinates {m : Masses} {s : ℕ → ℝ} {q : ℕ → Configuration}
    {φ : ℕ → ℕ} {y : Label → ℝ} {P₀ : Configuration}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀) :
    BlowupCoordinates m (VerticalPartition.verticalPartitionDatum y) := by
  refine ⟨((0, VerticalPartition.verticalHeight y), ((fun i => P₀ i 0), 0)), ?_⟩
  apply (mem_coordinateSpace_iff m (VerticalPartition.verticalPartitionDatum y) _).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · exact VerticalPartition.vertical_group_center_zero m hlim.2.2.2.2.2.2.2.2
  · intro a
    have hcenter := congrArg (fun p : Point => p 0) (hdata.2.2.1 a)
    simpa only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      PiLp.zero_apply, smul_eq_mul] using hcenter
  · intro a
    simp

theorem limitCoordinates_outerH {m : Masses} {s : ℕ → ℝ} {q : ℕ → Configuration}
    {φ : ℕ → ℕ} {y : Label → ℝ} {P₀ : Configuration}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀)
    (a : BlockIndex (VerticalPartition.verticalPartitionDatum y)) :
    outerH (limitCoordinates hlim hdata) a = 0 := rfl

theorem limitCoordinates_outerY {m : Masses} {s : ℕ → ℝ} {q : ℕ → Configuration}
    {φ : ℕ → ℕ} {y : Label → ℝ} {P₀ : Configuration}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀)
    (a : BlockIndex (VerticalPartition.verticalPartitionDatum y)) :
    outerY (limitCoordinates hlim hdata) a = VerticalPartition.verticalHeight y a := rfl

theorem limitCoordinates_innerU {m : Masses} {s : ℕ → ℝ} {q : ℕ → Configuration}
    {φ : ℕ → ℕ} {y : Label → ℝ} {P₀ : Configuration}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀) (i : Label) :
    innerU (limitCoordinates hlim hdata) i = P₀ i 0 := rfl

theorem limitCoordinates_innerV {m : Masses} {s : ℕ → ℝ} {q : ℕ → Configuration}
    {φ : ℕ → ℕ} {y : Label → ℝ} {P₀ : Configuration}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀) (i : Label) :
    innerV (limitCoordinates hlim hdata) i = 0 := rfl

theorem point_eq_horizontal_tuple {p : Point} (hp : p 1 = 0) :
    p = (!₂[p 0, 0] : Point) := by
  ext k
  fin_cases k
  · rfl
  · simpa using hp

theorem actual_internal_coordinate_tendsto {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    {P₀ : Configuration}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀)
    (heq : InternalEquationLimits.InternalEquationAtLimit m y P₀)
    {a : BlockIndex (VerticalPartition.verticalPartitionDatum y)} {i : Label}
    (hi : i ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) a) :
    Tendsto (fun ν => internalVectorCoordinate m (VerticalPartition.verticalPartitionDatum y)
      (epsilon (s (φ ν))) (q (φ ν)) a i) atTop
      (nhds (!₂[innerU (limitCoordinates hlim hdata) i, 0] : Point)) := by
  have hP := (tendsto_pi_nhds.mp hdata.1 i).congr'
    (Eventually.of_forall (fun ν => InternalCoordinates.internalVectors_apply_of_mem
      m (VerticalPartition.verticalPartitionDatum y) _ _ hi))
  have htuple : (!₂[innerU (limitCoordinates hlim hdata) i, 0] : Point) = P₀ i := by
    rw [limitCoordinates_innerU]
    exact (point_eq_horizontal_tuple
      (InternalHorizontalLimit.internal_limit_vertical_zero hm hdata heq i)).symm
  rw [htuple]
  exact hP

/-- Actual normalized internal pair distance also has a positive limit;
the scalar distance is obtained only after vertical vanishing is proved. -/
theorem normalized_internal_distance_tendsto {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    {P₀ : Configuration}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀)
    (heq : InternalEquationLimits.InternalEquationAtLimit m y P₀)
    {a : BlockIndex (VerticalPartition.verticalPartitionDatum y)} {i j : Label}
    (hi : i ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) a)
    (hj : j ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) a) (hij : i ≠ j) :
    0 < |P₀ i 0 - P₀ j 0| ∧
      Tendsto (fun ν => dist (q (φ ν) i) (q (φ ν) j) / epsilon (s (φ ν)))
        atTop (nhds |P₀ i 0 - P₀ j 0|) := by
  have hv := InternalHorizontalLimit.internal_limit_vertical_zero hm hdata heq
  have hd : 0 < dist (P₀ i) (P₀ j) :=
    ((ScaleConstants.constants_positive m hm).2.1).trans_le (hdata.2.2.2 a i j hi hj hij)
  have hdlim := (tendsto_pi_nhds.mp hdata.1 i).dist (tendsto_pi_nhds.mp hdata.1 j)
  rw [ScalarLimitEquations.point_dist_eq_abs_horizontal (hv i) (hv j)] at hd hdlim
  refine ⟨hd, hdlim.congr' ?_⟩
  exact Eventually.of_forall (fun ν => InternalCoordinates.internalVectors_dist_of_mem m
    (VerticalPartition.verticalPartitionDatum y) (hlim.2.2.2.1 ν) _ hi hj)

/-- Direct binding to the frozen SequenceDistanceRegimes specification,
with the common c₀(m), C(m) and the SAME selected physical sequence. -/
theorem actual_distance_regimes {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    {P₀ : Configuration} (hq : ∀ ν, IsSolution m (s ν) (q ν))
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀) :
    SequenceDistanceRegimes m (VerticalPartition.verticalPartitionDatum y)
      (limitCoordinates hlim hdata) (fun ν => epsilon (s (φ ν))) (fun ν => q (φ ν)) := by
  refine ⟨?_, ?_⟩
  · exact ⟨ScaleConstants.c₀ m, ScaleConstants.C m,
      (ScaleConstants.constants_positive m hm).2.1,
      (ScaleConstants.constants_positive m hm).2.2.2,
      InternalScale.eventually_all_internal_scaled hm hq hlim⟩
  · intro a b hab i j hi hj
    simpa only [limitCoordinates_outerY] using
      SequencePointLimits.cross_distance_tendsto hlim hab hi hj

/-- The whole un-reordered limit result uses only the original arbitrary
solution sequence. It retains all real-coordinate claims but intentionally
does not state IsSeed in the provisional natural-label order. -/
theorem exists_actual_natural_order_limits {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration}
    (hs : Tendsto s atTop atTop) (hq : ∀ ν, IsSolution m (s ν) (q ν)) :
    ∃ φ : ℕ → ℕ, ∃ y : Label → ℝ, ∃ P₀ : Configuration,
      ∃ z : BlowupCoordinates m (VerticalPartition.verticalPartitionDatum y),
      ∃ h : ℕ → BlowupCoordinates m (VerticalPartition.verticalPartitionDatum y),
        SequenceStart.InitialVerticalLimit m s q φ y ∧
        InternalSubsequence.InternalLimitData m s q φ y P₀ ∧
        InternalEquationLimits.InternalEquationAtLimit m y P₀ ∧
        (∀ i : Label, P₀ i 1 = 0) ∧
        (∀ ν, CoordinatesOfConfiguration m (VerticalPartition.verticalPartitionDatum y)
          (epsilon (s (φ ν))) (q (φ ν)) (h ν)) ∧
        (∀ a : BlockIndex (VerticalPartition.verticalPartitionDatum y),
          Tendsto (fun ν => outerH (h ν) a) atTop (nhds 0) ∧
          Tendsto (fun ν => outerY (h ν) a) atTop (nhds (outerY z a))) ∧
        (∀ (a : BlockIndex (VerticalPartition.verticalPartitionDatum y)) (i : Label),
          i ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) a →
          Tendsto (fun ν => internalVectorCoordinate m (VerticalPartition.verticalPartitionDatum y)
            (epsilon (s (φ ν))) (q (φ ν)) a i) atTop (nhds (!₂[innerU z i, 0] : Point))) ∧
        FourBody.HorizontalCentersCubicBound m (VerticalPartition.verticalPartitionDatum y)
          (fun ν => epsilon (s (φ ν))) h ∧
        SequenceDistanceRegimes m (VerticalPartition.verticalPartitionDatum y) z
          (fun ν => epsilon (s (φ ν))) (fun ν => q (φ ν)) ∧
        StrictMono (outerY z) ∧
        OneDimensionalSolution (datumBlockMass m (VerticalPartition.verticalPartitionDatum y)) (outerY z) ∧
        (∀ a : BlockIndex (VerticalPartition.verticalPartitionDatum y),
          OneDimensionalSolution
            (fun j => m (internalLabel (VerticalPartition.verticalPartitionDatum y) a j))
            (fun j => innerU z (internalLabel (VerticalPartition.verticalPartitionDatum y) a j))) := by
  obtain ⟨φ, y, P₀, hlim, hdata, heq, _houter⟩ :=
    InternalEquationLimits.exists_internal_equation_limit hm hs hq
  obtain ⟨h, hh⟩ := VerticalPartition.exists_selected_mean_coordinates hm hq hlim.2.1
    (VerticalPartition.verticalPartitionDatum y)
  let z := limitCoordinates hlim hdata
  have hcubic := HorizontalCubicBound.horizontal_centers_cubic_bound hm hq hlim h hh
  refine ⟨φ, y, P₀, z, h, hlim, hdata, heq,
    InternalHorizontalLimit.internal_limit_vertical_zero hm hdata heq, hh, ?_, ?_,
    (HorizontalCubicBound.horizontalCentersCubicBound_iff_statement m s φ _ h).mp hcubic,
    actual_distance_regimes hm hq hlim hdata,
    VerticalPartition.verticalHeight_strictMono y,
    ScalarLimitEquations.outer_height_is_oneDimensionalSolution hm hq hlim,
    ScalarLimitEquations.internal_limit_is_oneDimensionalSolution hm hdata heq⟩
  · intro a
    refine ⟨HorizontalCubicBound.horizontal_centers_tendsto_zero hlim.2.2.2.2.1 hcubic a, ?_⟩
    have hY := VerticalPartition.vertical_block_mean_tendsto hm hlim.2.2.2.2.2.1 a
    exact hY.congr' (Eventually.of_forall (fun ν => ((hh ν).2.2.1 a).symm))
  · intro a i hi
    exact actual_internal_coordinate_tendsto hm hlim hdata heq hi

end FourBody.NaturalOrderLimitCoordinates

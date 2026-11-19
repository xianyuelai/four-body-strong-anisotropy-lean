import FourBody.ReorderedLimitCoordinates

/-!
# Complete Proposition 3.2 proof candidate, awaiting actual Lean elaboration

Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
The last theorem has the EXACT frozen SeedLimitStatement type and takes
no additional analytic, compactness, seed, branch or main-theorem
hypotheses. Its body derives the initial simultaneous subsequence,
internal compactness, equations, vertical pairing, actual horizontal
sorting, coordinate mean identities, cubic H bound and both distance
regimes. The same φ is used throughout.

IMPORTANT STATUS: every sequence module here is still an UNCOMPILED
candidate. TwoScaleEstimates and BlowupPhysicalBridge dependencies also
await their actual compiler window. Writing this body does not confirm
Proposition 3.2, a clean build, axiom audit or any main theorem.
FiniteHorizontalSort exact local copy SHA256:
F621ED3F3ED28F7D1E539272C4995ACFB464DE59ABC2320F79ED9A729313B9A7.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace FourBody.SeedLimitCandidate

open ReorderedLimitCoordinates

theorem final_vertical_center_eq_old (m : Masses) (y : Label → ℝ) (P₀ : Configuration)
    (q : Configuration) (a : BlockIndex (finalDatum y P₀)) :
    verticalCenterCoordinate m (finalDatum y P₀) q a =
      verticalCenterCoordinate m (VerticalPartition.verticalPartitionDatum y) q (oldIndex y P₀ a) := by
  unfold verticalCenterCoordinate
  rw [final_block_mean_eq]

theorem final_horizontal_center_eq_old (m : Masses) (y : Label → ℝ) (P₀ : Configuration)
    (ε : ℝ) (q : Configuration) (a : BlockIndex (finalDatum y P₀)) :
    horizontalCenterCoordinate m (finalDatum y P₀) ε q a =
      horizontalCenterCoordinate m (VerticalPartition.verticalPartitionDatum y) ε q
        (oldIndex y P₀ a) := by
  unfold horizontalCenterCoordinate
  rw [final_block_mean_eq]

theorem final_internal_vector_eq_old (m : Masses) (y : Label → ℝ) (P₀ : Configuration)
    (ε : ℝ) (q : Configuration) (a : BlockIndex (finalDatum y P₀)) (i : Label) :
    internalVectorCoordinate m (finalDatum y P₀) ε q a i =
      internalVectorCoordinate m (VerticalPartition.verticalPartitionDatum y) ε q
        (oldIndex y P₀ a) i := by
  unfold internalVectorCoordinate
  rw [final_block_mean_eq]

/-- The mean-inverse coordinates for the new and old data have exactly
the same horizontal centers at corresponding actual outer positions. -/
theorem actual_horizontal_coordinates_eq {m : Masses} {y : Label → ℝ}
    {P₀ : Configuration} {ε : ℝ} {q : Configuration}
    {hnew : BlowupCoordinates m (finalDatum y P₀)}
    {hold : BlowupCoordinates m (VerticalPartition.verticalPartitionDatum y)}
    (hhnew : CoordinatesOfConfiguration m (finalDatum y P₀) ε q hnew)
    (hhold : CoordinatesOfConfiguration m (VerticalPartition.verticalPartitionDatum y) ε q hold)
    (a : BlockIndex (finalDatum y P₀)) :
    outerH hnew a = outerH hold (oldIndex y P₀ a) := by
  exact (hhnew.2.1 a).trans ((final_horizontal_center_eq_old m y P₀ ε q a).trans
    (hhold.2.1 (oldIndex y P₀ a)).symm)

/-- Cubic bounds transport by actual mean identities; a new estimate is
not assumed for the final datum. -/
theorem final_cubic_bound {m : Masses} {s : ℕ → ℝ} {q : ℕ → Configuration}
    {φ : ℕ → ℕ} {y : Label → ℝ} {P₀ : Configuration}
    {hnew : ℕ → BlowupCoordinates m (finalDatum y P₀)}
    {hold : ℕ → BlowupCoordinates m (VerticalPartition.verticalPartitionDatum y)}
    (hhnew : ∀ ν, CoordinatesOfConfiguration m (finalDatum y P₀)
      (epsilon (s (φ ν))) (q (φ ν)) (hnew ν))
    (hhold : ∀ ν, CoordinatesOfConfiguration m (VerticalPartition.verticalPartitionDatum y)
      (epsilon (s (φ ν))) (q (φ ν)) (hold ν))
    (hcubic : HorizontalCubicBound.HorizontalCentersCubicBound m s φ
      (VerticalPartition.verticalPartitionDatum y) hold) :
    FourBody.HorizontalCentersCubicBound m (finalDatum y P₀)
      (fun ν => epsilon (s (φ ν))) hnew := by
  obtain ⟨K, hK, hbound⟩ := hcubic
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound] with ν hν
  intro a
  rw [actual_horizontal_coordinates_eq (hhnew ν) (hhold ν) a]
  exact hν (oldIndex y P₀ a)

theorem final_outer_vertical_tendsto {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    {P₀ : Configuration}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀)
    {h : ℕ → BlowupCoordinates m (finalDatum y P₀)}
    (hh : ∀ ν, CoordinatesOfConfiguration m (finalDatum y P₀)
      (epsilon (s (φ ν))) (q (φ ν)) (h ν)) (a : BlockIndex (finalDatum y P₀)) :
    Tendsto (fun ν => outerY (h ν) a) atTop
      (nhds (outerY (finalCoordinates hlim hdata) a)) := by
  have hY := VerticalPartition.vertical_block_mean_tendsto hm hlim.2.2.2.2.2.1
    (oldIndex y P₀ a)
  rw [finalCoordinates_outerY]
  exact hY.congr' (Eventually.of_forall (fun ν =>
    (final_vertical_center_eq_old m y P₀ (q (φ ν)) a).symm.trans
      ((hh ν).2.2.1 a).symm))

theorem final_internal_coordinate_tendsto {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    {P₀ : Configuration}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀)
    (heq : InternalEquationLimits.InternalEquationAtLimit m y P₀)
    {a : BlockIndex (finalDatum y P₀)} {i : Label} (hi : i ∈ datumBlock (finalDatum y P₀) a) :
    Tendsto (fun ν => internalVectorCoordinate m (finalDatum y P₀)
      (epsilon (s (φ ν))) (q (φ ν)) a i) atTop
      (nhds (!₂[innerU (finalCoordinates hlim hdata) i, 0] : Point)) := by
  have hiold := (final_block_mem_iff y P₀ a i).mp hi
  have hP := NaturalOrderLimitCoordinates.actual_internal_coordinate_tendsto hm hlim hdata heq hiold
  rw [finalCoordinates_innerU]
  simpa only [NaturalOrderLimitCoordinates.limitCoordinates_innerU] using
    hP.congr' (Eventually.of_forall (fun ν =>
      (final_internal_vector_eq_old m y P₀ (epsilon (s (φ ν))) (q (φ ν)) a i).symm))

/-- The two actual distance regimes are invariant under the proved
within-block label reorder. All indices and witnesses remain the SAME. -/
theorem final_distance_regimes {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    {P₀ : Configuration} (hq : ∀ ν, IsSolution m (s ν) (q ν))
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀) :
    SequenceDistanceRegimes m (finalDatum y P₀) (finalCoordinates hlim hdata)
      (fun ν => epsilon (s (φ ν))) (fun ν => q (φ ν)) := by
  refine ⟨?_, ?_⟩
  · refine ⟨ScaleConstants.c₀ m, ScaleConstants.C m,
      (ScaleConstants.constants_positive m hm).2.1,
      (ScaleConstants.constants_positive m hm).2.2.2, ?_⟩
    filter_upwards [InternalScale.eventually_all_internal_scaled hm hq hlim] with ν hν
    intro a i j hi hj hij
    exact hν (oldIndex y P₀ a) i j ((final_block_mem_iff y P₀ a i).mp hi)
      ((final_block_mem_iff y P₀ a j).mp hj) hij
  · intro a b hab i j hi hj
    have habold : oldIndex y P₀ a ≠ oldIndex y P₀ b :=
      fun h => hab ((oldIndex y P₀).injective h)
    rw [finalCoordinates_outerY, finalCoordinates_outerY]
    exact SequencePointLimits.cross_distance_tendsto hlim habold
      ((final_block_mem_iff y P₀ a i).mp hi) ((final_block_mem_iff y P₀ b j).mp hj)

/-- EXACT Proposition 3.2 specification. Every intermediate conclusion is
derived from the original quantifiers. This is a proof CANDIDATE until all
dependencies, this declaration and its full type/axioms are checked. -/
theorem seedLimitStatement_candidate : SeedLimitStatement := by
  intro m hm s q hs hq
  obtain ⟨φ, y, P₀, hlim, hdata, heq, _houter⟩ :=
    InternalEquationLimits.exists_internal_equation_limit hm hs hq
  obtain ⟨hold, hhold⟩ := VerticalPartition.exists_selected_mean_coordinates hm hq hlim.2.1
    (VerticalPartition.verticalPartitionDatum y)
  obtain ⟨h, hh⟩ := VerticalPartition.exists_selected_mean_coordinates hm hq hlim.2.1
    (finalDatum y P₀)
  have hcubicOld := HorizontalCubicBound.horizontal_centers_cubic_bound hm hq hlim hold hhold
  have hcubic := final_cubic_bound hh hhold hcubicOld
  have hcubicLocal := (HorizontalCubicBound.horizontalCentersCubicBound_iff_statement
    m s φ (finalDatum y P₀) h).mpr hcubic
  refine ⟨φ, hlim.1, finalDatum y P₀, finalCoordinates hlim hdata, h,
    finalCoordinates_isSeed hm hq hlim hdata heq, hlim.2.1, hlim.2.2.2.2.1, hh,
    ?_, ?_, hcubic, final_distance_regimes hm hq hlim hdata⟩
  · intro a
    exact ⟨HorizontalCubicBound.horizontal_centers_tendsto_zero hlim.2.2.2.2.1 hcubicLocal a,
      final_outer_vertical_tendsto hm hlim hdata hh a⟩
  · intro a i hi
    exact final_internal_coordinate_tendsto hm hlim hdata heq hi

end FourBody.SeedLimitCandidate

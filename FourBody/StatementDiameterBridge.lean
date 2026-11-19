import FourBody.StatementDefinitions
import FourBody.PointGap

/-!
Bridge the source-facing actual Finset max-minus-min to the sorting
permutation used by the verified largest-gap estimate. Ties are permitted,
and the functions contain the same original four labeled coordinates.
No estimate or solution classification is assumed here.
-/

noncomputable section

namespace FourBody

theorem coordinateValues_max_eq_sorted (q : Configuration) (k : Axis) :
    (coordinateValues q k).max' (coordinateValues_nonempty q k) =
      q (Tuple.sort (fun i => q i k) 3) k := by
  apply ((coordinateValues q k).max'_eq_iff (coordinateValues_nonempty q k) _).mpr
  constructor
  · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · intro x hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
    exact (coordinate_extrema (fun i => q i k)).2 i

theorem coordinateValues_min_eq_sorted (q : Configuration) (k : Axis) :
    (coordinateValues q k).min' (coordinateValues_nonempty q k) =
      q (Tuple.sort (fun i => q i k) 0) k := by
  apply ((coordinateValues q k).min'_eq_iff (coordinateValues_nonempty q k) _).mpr
  constructor
  · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · intro x hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
    exact (coordinate_extrema (fun i => q i k)).1 i

/-- Exact equality of the two genuine max-minus-min representations. -/
theorem actualCoordinateDiameter_eq_sorted (q : Configuration) (k : Axis) :
    actualCoordinateDiameter q k = coordinateDiameter (fun i => q i k) := by
  rw [actualCoordinateDiameter, coordinateValues_max_eq_sorted,
    coordinateValues_min_eq_sorted]
  rfl

end FourBody


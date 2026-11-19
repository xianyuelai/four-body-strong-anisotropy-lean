import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
The finite ordering step in v2 `lem:diameter`, TeX lines 184--209.
The original manuscript has SHA256
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

This file constructs the sorting permutation rather than assuming it.
Its diameter is bridged to the actual maximum minus minimum. Repeated
coordinate values are permitted. Labels are retained throughout.
This finite lemma does not by itself prove the force or diameter estimate.
-/

noncomputable section

namespace FourBody

/-- The actual maximum minus minimum of the four coordinates, represented
by the endpoint values of the library's sorting permutation. -/
def coordinateDiameter (t : Fin 4 → ℝ) : ℝ :=
  t (Tuple.sort t 3) - t (Tuple.sort t 0)

theorem coordinate_extrema (t : Fin 4 → ℝ) :
    (∀ i, t (Tuple.sort t 0) ≤ t i) ∧
      (∀ i, t i ≤ t (Tuple.sort t 3)) := by
  have hmono := Tuple.monotone_sort t
  constructor
  · intro i
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      hmono (Fin.zero_le ((Tuple.sort t).symm i))
  · intro i
    have h := hmono (Fin.le_last ((Tuple.sort t).symm i))
    rw [show Fin.last 3 = (3 : Fin 4) by decide] at h
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h

theorem coordinateDiameter_nonneg (t : Fin 4 → ℝ) :
    0 ≤ coordinateDiameter t := by
  rcases coordinate_extrema t with ⟨hmin, _⟩
  exact sub_nonneg.mpr (hmin (Tuple.sort t 3))

/-- Every oriented coordinate difference is bounded by the actual range. -/
theorem coordinate_difference_le_diameter (t : Fin 4 → ℝ) (i j : Fin 4) :
    t j - t i ≤ coordinateDiameter t := by
  rcases coordinate_extrema t with ⟨hmin, hmax⟩
  exact sub_le_sub (hmax j) (hmin i)

/-- The upper bound is attained by a labeled pair. -/
theorem coordinateDiameter_attained (t : Fin 4 → ℝ) :
    ∃ i j : Fin 4, t j - t i = coordinateDiameter t := by
  exact ⟨Tuple.sort t 0, Tuple.sort t 3, rfl⟩

/-- Bridge to any genuine minimum and maximum selected by the application. -/
theorem coordinateDiameter_eq_of_extrema (t : Fin 4 → ℝ)
    (iMin iMax : Fin 4) (hmin : ∀ i, t iMin ≤ t i)
    (hmax : ∀ i, t i ≤ t iMax) :
    coordinateDiameter t = t iMax - t iMin := by
  rcases coordinate_extrema t with ⟨hlo, hhi⟩
  have h0 : t (Tuple.sort t 0) = t iMin :=
    le_antisymm (hlo iMin) (hmin (Tuple.sort t 0))
  have h3 : t (Tuple.sort t 3) = t iMax :=
    le_antisymm (hmax (Tuple.sort t 3)) (hhi iMax)
  exact congrArg₂ (fun a b : ℝ => a - b) h3 h0

/-- The three consecutive differences in a four-tuple. -/
def adjacentCoordinateGap (u : Fin 4 → ℝ) (k : Fin 3) : ℝ :=
  u k.succ - u k.castSucc

/-- One of the three consecutive differences controls the endpoint range.
The positivity follows from the positive range, without requiring that
each individual coordinate gap is strictly positive. -/
theorem exists_large_adjacent_coordinate_gap (u : Fin 4 → ℝ)
    (hD : 0 < u 3 - u 0) :
    ∃ k : Fin 3, 0 < adjacentCoordinateGap u k ∧
      u 3 - u 0 ≤ 3 * adjacentCoordinateGap u k := by
  by_cases h01 : u 1 - u 0 ≤ u 2 - u 1
  · by_cases h12 : u 2 - u 1 ≤ u 3 - u 2
    · refine ⟨2, ?_, ?_⟩
      · change 0 < u 3 - u 2
        linarith
      · change u 3 - u 0 ≤ 3 * (u 3 - u 2)
        linarith
    · refine ⟨1, ?_, ?_⟩
      · change 0 < u 2 - u 1
        linarith
      · change u 3 - u 0 ≤ 3 * (u 2 - u 1)
        linarith
  · by_cases h02 : u 1 - u 0 ≤ u 3 - u 2
    · refine ⟨2, ?_, ?_⟩
      · change 0 < u 3 - u 2
        linarith
      · change u 3 - u 0 ≤ 3 * (u 3 - u 2)
        linarith
    · refine ⟨0, ?_, ?_⟩
      · change 0 < u 1 - u 0
        linarith
      · change u 3 - u 0 ≤ 3 * (u 1 - u 0)
        linarith

/-- A nonempty lower block and its nonempty complement, obtained by an
actual largest-gap cut of the original labeled coordinates. -/
theorem coordinate_largest_gap_partition (t : Fin 4 → ℝ)
    (hD : 0 < coordinateDiameter t) :
    ∃ (A B : Finset (Fin 4)) (g : ℝ),
      A.Nonempty ∧ B.Nonempty ∧ B = Finset.univ \ A ∧
      Disjoint A B ∧ A ∪ B = Finset.univ ∧
      0 < g ∧ coordinateDiameter t ≤ 3 * g ∧
      ∀ i ∈ A, ∀ j ∈ B, g ≤ t j - t i := by
  classical
  let π : Equiv.Perm (Fin 4) := Tuple.sort t
  let u : Fin 4 → ℝ := t ∘ π
  have hmono : Monotone u := Tuple.monotone_sort t
  have hD' : 0 < u 3 - u 0 := hD
  rcases exists_large_adjacent_coordinate_gap u hD' with ⟨k, hg, hbound⟩
  let A : Finset (Fin 4) :=
    Finset.univ.filter (fun i => π.symm i ≤ k.castSucc)
  let B : Finset (Fin 4) := Finset.univ \ A
  have hA : A.Nonempty := by
    refine ⟨π k.castSucc, ?_⟩
    simp only [A, Finset.mem_filter, Finset.mem_univ,
      Equiv.symm_apply_apply, le_refl, and_self]
  have hB : B.Nonempty := by
    refine ⟨π k.succ, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa only [A, Finset.mem_filter, Finset.mem_univ,
      Equiv.symm_apply_apply, true_and] using
      (not_le_of_gt (Fin.castSucc_lt_succ (i := k)))
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiB
    exact (Finset.mem_sdiff.mp hiB).2 hiA
  have hunion : A ∪ B = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ A)
  refine ⟨A, B, adjacentCoordinateGap u k, hA, hB, rfl,
    hdisj, hunion, hg, hbound, ?_⟩
  intro i hiA j hjB
  have hi : π.symm i ≤ k.castSucc := (Finset.mem_filter.mp hiA).2
  have hjNot : ¬π.symm j ≤ k.castSucc := by
    intro hj
    exact (Finset.mem_sdiff.mp hjB).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
  have hj : k.succ ≤ π.symm j :=
    Fin.castSucc_lt_iff_succ_le.mp (lt_of_not_ge hjNot)
  have hlo : t i ≤ u k.castSucc := by
    simpa only [u, Function.comp_apply, Equiv.apply_symm_apply] using hmono hi
  have hhi : u k.succ ≤ t j := by
    simpa only [u, Function.comp_apply, Equiv.apply_symm_apply] using hmono hj
  change u k.succ - u k.castSucc ≤ t j - t i
  linarith

/-- The same result stated directly with genuine extremizing labels,
so no meaning of the manuscript's `max_i t_i - min_i t_i` is lost. -/
theorem coordinate_largest_gap_partition_of_extrema (t : Fin 4 → ℝ)
    (iMin iMax : Fin 4) (hmin : ∀ i, t iMin ≤ t i)
    (hmax : ∀ i, t i ≤ t iMax) (hD : 0 < t iMax - t iMin) :
    ∃ (A B : Finset (Fin 4)) (g : ℝ),
      A.Nonempty ∧ B.Nonempty ∧ B = Finset.univ \ A ∧
      Disjoint A B ∧ A ∪ B = Finset.univ ∧
      0 < g ∧ t iMax - t iMin ≤ 3 * g ∧
      ∀ i ∈ A, ∀ j ∈ B, g ≤ t j - t i := by
  have hdiam := coordinateDiameter_eq_of_extrema t iMin iMax hmin hmax
  rw [← hdiam] at hD ⊢
  exact coordinate_largest_gap_partition t hD

end FourBody

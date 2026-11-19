import FourBody.PointGap
import Mathlib.Data.Finset.Max

/-!
Finite subset ordering for v2 `prop:scales`, especially TeX lines 278--282.
The original manuscript has SHA256
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

For a nonempty subset J of the original four labels, the extremizing
labels below are obtained by the proved finite min/max existence API.
The partition is constructed, not assumed. Coordinates outside J are
filled with its attained minimum, and the global four-label cut is then
restricted to J. The factor 3 is a valid uniform consequence for subsets
of four labels. This file does not prove the sharper factor |J| - 1 or
the force estimates of Proposition 2.2.
-/

noncomputable section

namespace FourBody

/-- An attained minimum coordinate in a nonempty labeled cluster. -/
def clusterMinLabel (J : Finset (Fin 4)) (t : Fin 4 → ℝ)
    (hJ : J.Nonempty) : Fin 4 :=
  Classical.choose (Finset.exists_min_image J t hJ)

theorem clusterMinLabel_spec (J : Finset (Fin 4)) (t : Fin 4 → ℝ)
    (hJ : J.Nonempty) :
    clusterMinLabel J t hJ ∈ J ∧
      ∀ i ∈ J, t (clusterMinLabel J t hJ) ≤ t i :=
  Classical.choose_spec (Finset.exists_min_image J t hJ)

/-- An attained maximum coordinate in a nonempty labeled cluster. -/
def clusterMaxLabel (J : Finset (Fin 4)) (t : Fin 4 → ℝ)
    (hJ : J.Nonempty) : Fin 4 :=
  Classical.choose (Finset.exists_max_image J t hJ)

theorem clusterMaxLabel_spec (J : Finset (Fin 4)) (t : Fin 4 → ℝ)
    (hJ : J.Nonempty) :
    clusterMaxLabel J t hJ ∈ J ∧
      ∀ i ∈ J, t i ≤ t (clusterMaxLabel J t hJ) :=
  Classical.choose_spec (Finset.exists_max_image J t hJ)

/-- The actual maximum minus minimum on J. A nonemptiness proof is
required, so this definition imposes no convention for an empty cluster. -/
def clusterCoordinateDiameter (J : Finset (Fin 4)) (t : Fin 4 → ℝ)
    (hJ : J.Nonempty) : ℝ :=
  t (clusterMaxLabel J t hJ) - t (clusterMinLabel J t hJ)

theorem clusterCoordinateDiameter_nonneg (J : Finset (Fin 4))
    (t : Fin 4 → ℝ) (hJ : J.Nonempty) :
    0 ≤ clusterCoordinateDiameter J t hJ := by
  rcases clusterMinLabel_spec J t hJ with ⟨_, hmin⟩
  rcases clusterMaxLabel_spec J t hJ with ⟨hmaxJ, _⟩
  exact sub_nonneg.mpr (hmin _ hmaxJ)

theorem cluster_coordinate_difference_le_diameter (J : Finset (Fin 4))
    (t : Fin 4 → ℝ) (hJ : J.Nonempty) (i j : Fin 4)
    (hi : i ∈ J) (hj : j ∈ J) :
    t j - t i ≤ clusterCoordinateDiameter J t hJ := by
  rcases clusterMinLabel_spec J t hJ with ⟨_, hmin⟩
  rcases clusterMaxLabel_spec J t hJ with ⟨_, hmax⟩
  exact sub_le_sub (hmax j hj) (hmin i hi)

theorem clusterCoordinateDiameter_attained (J : Finset (Fin 4))
    (t : Fin 4 → ℝ) (hJ : J.Nonempty) :
    ∃ i ∈ J, ∃ j ∈ J, t j - t i = clusterCoordinateDiameter J t hJ := by
  exact ⟨clusterMinLabel J t hJ, (clusterMinLabel_spec J t hJ).1,
    clusterMaxLabel J t hJ, (clusterMaxLabel_spec J t hJ).1, rfl⟩

theorem clusterCoordinateDiameter_eq_of_extrema (J : Finset (Fin 4))
    (t : Fin 4 → ℝ) (hJ : J.Nonempty) (iMin iMax : Fin 4)
    (hiMin : iMin ∈ J) (hiMax : iMax ∈ J)
    (hmin : ∀ i ∈ J, t iMin ≤ t i)
    (hmax : ∀ i ∈ J, t i ≤ t iMax) :
    clusterCoordinateDiameter J t hJ = t iMax - t iMin := by
  rcases clusterMinLabel_spec J t hJ with ⟨hminJ, hlo⟩
  rcases clusterMaxLabel_spec J t hJ with ⟨hmaxJ, hhi⟩
  have h0 : t (clusterMinLabel J t hJ) = t iMin :=
    le_antisymm (hlo iMin hiMin) (hmin _ hminJ)
  have h3 : t (clusterMaxLabel J t hJ) = t iMax :=
    le_antisymm (hmax _ hmaxJ) (hhi iMax hiMax)
  exact congrArg₂ (fun a b : ℝ => a - b) h3 h0

/-- An actual cut inside J, starting with attained extrema supplied by
the application. Both extremizing labels are proved to survive the cut. -/
theorem cluster_largest_gap_partition_of_extrema (J : Finset (Fin 4))
    (t : Fin 4 → ℝ) (iMin iMax : Fin 4)
    (hiMin : iMin ∈ J) (hiMax : iMax ∈ J)
    (hmin : ∀ i ∈ J, t iMin ≤ t i)
    (hmax : ∀ i ∈ J, t i ≤ t iMax) (hD : 0 < t iMax - t iMin) :
    ∃ (A B : Finset (Fin 4)) (g : ℝ),
      A ⊆ J ∧ B ⊆ J ∧ A.Nonempty ∧ B.Nonempty ∧ B = J \ A ∧
      Disjoint A B ∧ A ∪ B = J ∧
      0 < g ∧ t iMax - t iMin ≤ 3 * g ∧
      ∀ i ∈ A, ∀ j ∈ B, g ≤ t j - t i := by
  classical
  let u : Fin 4 → ℝ := fun i => if i ∈ J then t i else t iMin
  have hminU : ∀ i, u iMin ≤ u i := by
    intro i
    by_cases hi : i ∈ J
    · simpa only [u, if_pos hiMin, if_pos hi] using hmin i hi
    · simp only [u, if_pos hiMin, if_neg hi, le_refl]
  have hmaxU : ∀ i, u i ≤ u iMax := by
    intro i
    by_cases hi : i ∈ J
    · simpa only [u, if_pos hiMax, if_pos hi] using hmax i hi
    · simpa only [u, if_pos hiMax, if_neg hi] using hmin iMax hiMax
  have hD' : 0 < u iMax - u iMin := by
    simpa only [u, if_pos hiMax, if_pos hiMin] using hD
  rcases coordinate_largest_gap_partition_of_extrema u iMin iMax hminU hmaxU hD'
    with ⟨U, V, g, hU, hV, hVdef, hUV, hcover, hg, hDg, hsep⟩
  have hMinU : iMin ∈ U := by
    by_contra hnot
    have hMinV : iMin ∈ V := by
      rw [hVdef]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩
    rcases hU with ⟨i, hi⟩
    have hgap := hsep i hi iMin hMinV
    have hmi := hminU i
    linarith
  have hMaxV : iMax ∈ V := by
    by_contra hnot
    have hMaxU : iMax ∈ U := by
      have hmem : iMax ∈ U ∪ V := by
        rw [hcover]
        exact Finset.mem_univ _
      exact (Finset.mem_union.mp hmem).resolve_right hnot
    rcases hV with ⟨j, hj⟩
    have hgap := hsep iMax hMaxU j hj
    have hmj := hmaxU j
    linarith
  let A : Finset (Fin 4) := J ∩ U
  let B : Finset (Fin 4) := J \ A
  have hAJ : A ⊆ J := Finset.inter_subset_left
  have hBJ : B ⊆ J := by
    intro i hi
    exact (Finset.mem_sdiff.mp hi).1
  have hA : A.Nonempty :=
    ⟨iMin, Finset.mem_inter.mpr ⟨hiMin, hMinU⟩⟩
  have hB : B.Nonempty := by
    refine ⟨iMax, Finset.mem_sdiff.mpr ⟨hiMax, ?_⟩⟩
    intro hMaxA
    exact (Finset.disjoint_left.mp hUV) (Finset.mem_inter.mp hMaxA).2 hMaxV
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiB
    exact (Finset.mem_sdiff.mp hiB).2 hiA
  have hunion : A ∪ B = J := Finset.union_sdiff_of_subset hAJ
  refine ⟨A, B, g, hAJ, hBJ, hA, hB, rfl, hAB, hunion, hg, ?_, ?_⟩
  · simpa only [u, if_pos hiMax, if_pos hiMin] using hDg
  · intro i hiA j hjB
    have hiJ : i ∈ J := (Finset.mem_inter.mp hiA).1
    have hiU : i ∈ U := (Finset.mem_inter.mp hiA).2
    have hjJ : j ∈ J := (Finset.mem_sdiff.mp hjB).1
    have hjNotA : j ∉ A := (Finset.mem_sdiff.mp hjB).2
    have hjV : j ∈ V := by
      rw [hVdef]
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hjU
      exact hjNotA (Finset.mem_inter.mpr ⟨hjJ, hjU⟩)
    simpa only [u, if_pos hiJ, if_pos hjJ] using hsep i hiU j hjV

/-- The same constructed cut using the actual cluster diameter. The
extremizing witnesses and all their properties are obtained internally. -/
theorem cluster_largest_gap_partition (J : Finset (Fin 4))
    (t : Fin 4 → ℝ) (hJ : J.Nonempty)
    (hD : 0 < clusterCoordinateDiameter J t hJ) :
    ∃ (A B : Finset (Fin 4)) (g : ℝ),
      A ⊆ J ∧ B ⊆ J ∧ A.Nonempty ∧ B.Nonempty ∧ B = J \ A ∧
      Disjoint A B ∧ A ∪ B = J ∧
      0 < g ∧ clusterCoordinateDiameter J t hJ ≤ 3 * g ∧
      ∀ i ∈ A, ∀ j ∈ B, g ≤ t j - t i := by
  rcases clusterMinLabel_spec J t hJ with ⟨hminJ, hmin⟩
  rcases clusterMaxLabel_spec J t hJ with ⟨hmaxJ, hmax⟩
  exact cluster_largest_gap_partition_of_extrema J t
    (clusterMinLabel J t hJ) (clusterMaxLabel J t hJ)
    hminJ hmaxJ hmin hmax hD

end FourBody

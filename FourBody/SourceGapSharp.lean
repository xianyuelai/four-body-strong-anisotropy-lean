import FourBody.ClusterGap
import FourBody.Geometry
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
Independent STATIC candidate; no Lean/Lake/checker acceptance is claimed.
Original v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

S2-U01, source lines 194–199: a genuinely largest positive consecutive gap.
S2-U15, source lines 278–282: a largest gap for the actual cluster J,
with the sharp denominator |J|-1 and a constructed nonempty labeled cut.

The cluster proof enumerates J itself; it never fills missing labels with
extra copies of a coordinate. Thus its gap count is exactly |J|-1 for
clusters with 2, 3 or 4 labels. The largest-gap comparisons are conclusions,
not assumptions. Coordinate ties are permitted. Every witness is a genuine
original label in J, and the lower/upper witnesses are consecutive in the
same sorted enumeration used to select the largest gap.
-/

set_option autoImplicit false
set_option warningAsError true
noncomputable section
open scoped BigOperators

namespace FourBody.SourceFaithfulGap

/-- Consecutive difference in a tuple of n+1 actual coordinates. -/
def adjacentGap {n : ℕ} (u : Fin (n + 1) → ℝ) (k : Fin n) : ℝ :=
  u k.succ - u k.castSucc

/-- Exact telescoping; there are precisely n consecutive gaps. -/
theorem sum_adjacentGap {n : ℕ} (u : Fin (n + 1) → ℝ) :
    (∑ k : Fin n, adjacentGap u k) = u (Fin.last n) - u 0 := by
  have hzero := Fin.sum_univ_succ u
  have hlast := Fin.sum_univ_castSucc u
  unfold adjacentGap
  rw [Finset.sum_sub_distrib]
  linarith

/-- Largest means comparison with every other adjacent gap. The positive
endpoint range forces this maximum to be positive even when there are ties. -/
theorem exists_largest_adjacent_gap (n : ℕ) (hn : 0 < n)
    (u : Fin (n + 1) → ℝ) (hD : 0 < u (Fin.last n) - u 0) :
    ∃ k : Fin n,
      0 < adjacentGap u k ∧
      (∀ l : Fin n, adjacentGap u l ≤ adjacentGap u k) ∧
      u (Fin.last n) - u 0 ≤ (n : ℝ) * adjacentGap u k ∧
      (u (Fin.last n) - u 0) / (n : ℝ) ≤ adjacentGap u k := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨k, _hk, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n)) (adjacentGap u) hne
  have hcompare : ∀ l : Fin n, adjacentGap u l ≤ adjacentGap u k :=
    fun l => hmax l (Finset.mem_univ l)
  have hsum : (∑ l : Fin n, adjacentGap u l) ≤
      ∑ _l : Fin n, adjacentGap u k :=
    Finset.sum_le_sum (fun l _ => hcompare l)
  have hbound : u (Fin.last n) - u 0 ≤ (n : ℝ) * adjacentGap u k := by
    simpa only [sum_adjacentGap, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using hsum
  have hg : 0 < adjacentGap u k := by
    by_contra hnot
    have hnng : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hproduct := mul_nonpos_of_nonneg_of_nonpos hnng (le_of_not_gt hnot)
    linarith
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hdiv : (u (Fin.last n) - u 0) / (n : ℝ) ≤ adjacentGap u k :=
    (div_le_iff₀ hnR).mpr (by simpa only [mul_comm] using hbound)
  exact ⟨k, hg, hcompare, hbound, hdiv⟩

/-- The missing typed largest-gap comparison for the manuscript's full
four-tuple: all three adjacent gaps are compared with the selected one. -/
theorem exists_largest_adjacent_coordinate_gap_four
    (u : Fin 4 → ℝ) (hD : 0 < u 3 - u 0) :
    ∃ k : Fin 3,
      0 < adjacentCoordinateGap u k ∧
      (∀ l : Fin 3, adjacentCoordinateGap u l ≤ adjacentCoordinateGap u k) ∧
      u 3 - u 0 ≤ 3 * adjacentCoordinateGap u k ∧
      (u 3 - u 0) / 3 ≤ adjacentCoordinateGap u k := by
  simpa only [adjacentGap, adjacentCoordinateGap, Nat.cast_ofNat,
    show Fin.last 3 = (3 : Fin 4) by decide] using
    exists_largest_adjacent_gap 3 (by norm_num) u hD

/-- A sorted enumeration of J and a cut at its actual largest adjacent
gap. The entire sharp source statement is retained in the type, including
consecutive labeled witnesses belonging to the two constructed groups.
No target gap, ordering certificate, or force bound is a premise. -/
theorem cluster_largest_adjacent_gap_partition_sharp
    (J : Finset Label) (t : Label → ℝ) (hJ : J.Nonempty)
    (hcard : 2 ≤ J.card) (hD : 0 < clusterCoordinateDiameter J t hJ) :
    ∃ (n : ℕ) (σ : Fin (n + 1) ≃ {i : Label // i ∈ J})
      (k : Fin n) (A B : Finset Label),
      J.card = n + 1 ∧
      Monotone (fun l : Fin (n + 1) => t (σ l).val) ∧
      A ⊆ J ∧ B ⊆ J ∧ A.Nonempty ∧ B.Nonempty ∧
      B = J \ A ∧ Disjoint A B ∧ A ∪ B = J ∧
      (σ k.castSucc).val ∈ A ∧ (σ k.succ).val ∈ B ∧
      0 < adjacentGap (fun l => t (σ l).val) k ∧
      (∀ l : Fin n,
        adjacentGap (fun a => t (σ a).val) l ≤
          adjacentGap (fun a => t (σ a).val) k) ∧
      clusterCoordinateDiameter J t hJ / ((J.card - 1 : ℕ) : ℝ) ≤
        adjacentGap (fun a => t (σ a).val) k ∧
      clusterCoordinateDiameter J t hJ ≤
        ((J.card - 1 : ℕ) : ℝ) * adjacentGap (fun a => t (σ a).val) k ∧
      (∀ i ∈ A, ∀ j ∈ B,
        adjacentGap (fun a => t (σ a).val) k ≤ t j - t i) := by
  classical
  let n : ℕ := J.card - 1
  have hn : 0 < n := by dsimp [n]; omega
  have hcardEq : J.card = n + 1 := by dsimp [n]; omega
  let e : Fin (n + 1) ≃ {i : Label // i ∈ J} :=
    (J.orderIsoOfFin hcardEq).toEquiv
  let v : Fin (n + 1) → ℝ := fun l => t (e l).val
  let π : Equiv.Perm (Fin (n + 1)) := Tuple.sort v
  let σ : Fin (n + 1) ≃ {i : Label // i ∈ J} := π.trans e
  let u : Fin (n + 1) → ℝ := fun l => t (σ l).val
  have hmono : Monotone u := by
    intro a b hab
    exact Tuple.monotone_sort v hab
  have hmin : ∀ i ∈ J, t (σ 0).val ≤ t i := by
    intro i hi
    have h := hmono (Fin.zero_le (σ.symm ⟨i, hi⟩))
    simpa only [u, Equiv.apply_symm_apply] using h
  have hmax : ∀ i ∈ J, t i ≤ t (σ (Fin.last n)).val := by
    intro i hi
    have h := hmono (Fin.le_last (σ.symm ⟨i, hi⟩))
    simpa only [u, Equiv.apply_symm_apply] using h
  have hdiam : clusterCoordinateDiameter J t hJ = u (Fin.last n) - u 0 :=
    clusterCoordinateDiameter_eq_of_extrema J t hJ
      (σ 0).val (σ (Fin.last n)).val (σ 0).property
      (σ (Fin.last n)).property hmin hmax
  have hD' : 0 < u (Fin.last n) - u 0 := by simpa only [hdiam] using hD
  obtain ⟨k, hg, hlargest, hbound, havg⟩ :=
    exists_largest_adjacent_gap n hn u hD'
  let A : Finset Label :=
    J.filter (fun i => ∃ hi : i ∈ J, σ.symm ⟨i, hi⟩ ≤ k.castSucc)
  let B : Finset Label := J \ A
  have hAJ : A ⊆ J := Finset.filter_subset _ _
  have hBJ : B ⊆ J := by
    intro i hi
    exact (Finset.mem_sdiff.mp hi).1
  have hleft : (σ k.castSucc).val ∈ A := by
    apply Finset.mem_filter.mpr
    refine ⟨(σ k.castSucc).property, (σ k.castSucc).property, ?_⟩
    have hsub : (⟨(σ k.castSucc).val, (σ k.castSucc).property⟩ :
        {i : Label // i ∈ J}) = σ k.castSucc := rfl
    rw [hsub, Equiv.symm_apply_apply]
  have hright : (σ k.succ).val ∈ B := by
    apply Finset.mem_sdiff.mpr
    refine ⟨(σ k.succ).property, ?_⟩
    intro hmem
    obtain ⟨hi, hiLe⟩ := (Finset.mem_filter.mp hmem).2
    have hsub : (⟨(σ k.succ).val, hi⟩ : {i : Label // i ∈ J}) =
        σ k.succ := by apply Subtype.ext; rfl
    rw [hsub, Equiv.symm_apply_apply] at hiLe
    exact (not_le_of_gt (Fin.castSucc_lt_succ (i := k))) hiLe
  have hA : A.Nonempty := ⟨(σ k.castSucc).val, hleft⟩
  have hB : B.Nonempty := ⟨(σ k.succ).val, hright⟩
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiB
    exact (Finset.mem_sdiff.mp hiB).2 hiA
  have hunion : A ∪ B = J := Finset.union_sdiff_of_subset hAJ
  refine ⟨n, σ, k, A, B, hcardEq, hmono, hAJ, hBJ, hA, hB, rfl,
    hdisj, hunion, hleft, hright, hg, hlargest, ?_, ?_, ?_⟩
  · simpa only [hdiam] using havg
  · simpa only [hdiam] using hbound
  · intro i hiA j hjB
    obtain ⟨hiJ, hiLe⟩ := (Finset.mem_filter.mp hiA).2
    have hjJ : j ∈ J := (Finset.mem_sdiff.mp hjB).1
    have hjNot : ¬σ.symm ⟨j, hjJ⟩ ≤ k.castSucc := by
      intro hjLe
      exact (Finset.mem_sdiff.mp hjB).2
        (Finset.mem_filter.mpr ⟨hjJ, hjJ, hjLe⟩)
    have hjLe : k.succ ≤ σ.symm ⟨j, hjJ⟩ :=
      Fin.castSucc_lt_iff_succ_le.mp (lt_of_not_ge hjNot)
    have hlo : t i ≤ u k.castSucc := by
      simpa only [u, Equiv.apply_symm_apply] using hmono hiLe
    have hhi : u k.succ ≤ t j := by
      simpa only [u, Equiv.apply_symm_apply] using hmono hjLe
    change u k.succ - u k.castSucc ≤ t j - t i
    linarith

end FourBody.SourceFaithfulGap

import FourBody.CoordinateEquivalence
import FourBody.SequenceStart
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Sort

/-!
# Grouping the initial vertical limit into actual ordered blocks

Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
This is the equality-class partition of the four initial vertical limits
at the start of Proposition 3.2 (proof lines 423--428).

Distinct attained real heights are sorted increasingly; each block is the
actual fiber among the four fixed labels. The fiber's present internal
order is the fixed increasing LABEL order. It is only a provisional order.
It is NOT asserted to be the prescribed order of the eventual scaled
internal horizontal seed. That later reordering remains a separate task.

The construction proves all OrderedClusterDatum invariants from the finite
fibers. No datum, seed, compactness certificate or branch is assumed.
Compilation status is recorded outside this file.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace FourBody.VerticalPartition

/-- Distinct attained heights; four labels are included even if tied. -/
def verticalValues (y : Label → ℝ) : Finset ℝ :=
  (Finset.univ : Finset Label).image y

def orderedVerticalValues (y : Label → ℝ) : List ℝ :=
  (verticalValues y).sort (· ≤ ·)

/-- Provisional natural label order inside one equality class. -/
def verticalFiberList (y : Label → ℝ) (t : ℝ) : List Label := by
  classical
  exact (List.finRange 4).filter (fun i => decide (y i = t))

def verticalBlocks (y : Label → ℝ) : List (List Label) :=
  (orderedVerticalValues y).map (verticalFiberList y)

theorem mem_orderedVerticalValues (y : Label → ℝ) (t : ℝ) :
    t ∈ orderedVerticalValues y ↔ ∃ i : Label, y i = t := by
  classical
  simp [orderedVerticalValues, verticalValues]

theorem mem_verticalFiberList (y : Label → ℝ) (t : ℝ) (i : Label) :
    i ∈ verticalFiberList y t ↔ y i = t := by
  classical
  simp [verticalFiberList]

theorem verticalFiberList_nodup (y : Label → ℝ) (t : ℝ) :
    (verticalFiberList y t).Nodup := by
  classical
  exact (List.nodup_finRange 4).filter _

theorem orderedVerticalValues_nodup (y : Label → ℝ) :
    (orderedVerticalValues y).Nodup := by
  exact Finset.sort_nodup _ _

theorem verticalFiberList_nonempty (y : Label → ℝ) {t : ℝ}
    (ht : t ∈ orderedVerticalValues y) : verticalFiberList y t ≠ [] := by
  obtain ⟨i, hi⟩ := (mem_orderedVerticalValues y t).mp ht
  have hmem := (mem_verticalFiberList y t i).mpr hi
  intro he
  simp only [he, List.not_mem_nil] at hmem

theorem verticalFibers_disjoint (y : Label → ℝ) {t u : ℝ} (htu : t ≠ u) :
    List.Disjoint (verticalFiberList y t) (verticalFiberList y u) := by
  apply List.disjoint_left.mpr
  intro i hit hiu
  exact htu (((mem_verticalFiberList y t i).mp hit).symm.trans
    ((mem_verticalFiberList y u i).mp hiu))

theorem verticalBlocks_nonempty (y : Label → ℝ) :
    ∀ b ∈ verticalBlocks y, b ≠ [] := by
  intro b hb
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
  exact verticalFiberList_nonempty y ht

theorem verticalBlocks_pairwise_disjoint (y : Label → ℝ) :
    (verticalBlocks y).Pairwise List.Disjoint := by
  apply List.pairwise_map.mpr
  exact (orderedVerticalValues_nodup y).imp (fun htu => verticalFibers_disjoint y htu)

theorem verticalBlocks_flatten_nodup (y : Label → ℝ) :
    (verticalBlocks y).flatten.Nodup := by
  apply List.nodup_flatten.mpr
  refine ⟨?_, verticalBlocks_pairwise_disjoint y⟩
  intro b hb
  obtain ⟨t, _ht, rfl⟩ := List.mem_map.mp hb
  exact verticalFiberList_nodup y t

theorem every_label_mem_verticalBlocks (y : Label → ℝ) (i : Label) :
    i ∈ (verticalBlocks y).flatten := by
  apply List.mem_flatten.mpr
  refine ⟨verticalFiberList y (y i), ?_, ?_⟩
  · apply List.mem_map.mpr
    exact ⟨y i, (mem_orderedVerticalValues y (y i)).mpr ⟨i, rfl⟩, rfl⟩
  · exact (mem_verticalFiberList y (y i) i).mpr rfl

theorem verticalBlocks_labels_once (y : Label → ℝ) :
    (verticalBlocks y).flatten.Perm (List.finRange 4) := by
  apply (List.perm_ext_iff_of_nodup (verticalBlocks_flatten_nodup y)
    (List.nodup_finRange 4)).mpr
  intro i
  exact ⟨fun _ => List.mem_finRange i, fun _ => every_label_mem_verticalBlocks y i⟩

/-- The concrete initial ordered partition. Its internal label order is
provisional; the later seed-order extraction is not encoded as an axiom. -/
def verticalPartitionDatum (y : Label → ℝ) : OrderedClusterDatum where
  blocks := verticalBlocks y
  nonempty_blocks := verticalBlocks_nonempty y
  labels_once := verticalBlocks_labels_once y

def verticalHeightIndex (y : Label → ℝ)
    (a : BlockIndex (verticalPartitionDatum y)) : Fin (orderedVerticalValues y).length :=
  ⟨a.val, by simpa only [verticalPartitionDatum, verticalBlocks, List.length_map] using a.isLt⟩

def verticalHeight (y : Label → ℝ)
    (a : BlockIndex (verticalPartitionDatum y)) : ℝ :=
  (orderedVerticalValues y).get (verticalHeightIndex y a)

theorem datumBlock_eq_fiber (y : Label → ℝ)
    (a : BlockIndex (verticalPartitionDatum y)) :
    datumBlock (verticalPartitionDatum y) a = verticalFiberList y (verticalHeight y a) := by
  change ((orderedVerticalValues y).map (verticalFiberList y)).get a =
    verticalFiberList y ((orderedVerticalValues y).get (verticalHeightIndex y a))
  have ha : a.val < (orderedVerticalValues y).length := (verticalHeightIndex y a).isLt
  change ((orderedVerticalValues y).map (verticalFiberList y))[a.val] =
    verticalFiberList y ((orderedVerticalValues y)[a.val])
  exact List.getElem_map _

theorem mem_datumBlock_iff_height (y : Label → ℝ)
    (a : BlockIndex (verticalPartitionDatum y)) (i : Label) :
    i ∈ datumBlock (verticalPartitionDatum y) a ↔ y i = verticalHeight y a := by
  rw [datumBlock_eq_fiber]
  exact mem_verticalFiberList y (verticalHeight y a) i

/-- The OUTER block order is the genuine strictly increasing height order. -/
theorem verticalHeight_strictMono (y : Label → ℝ) : StrictMono (verticalHeight y) := by
  intro a b hab
  exact (Finset.sortedLT_sort (verticalValues y)).pairwise.rel_get_of_lt
    (show verticalHeightIndex y a < verticalHeightIndex y b from hab)

theorem height_blockOf (y : Label → ℝ) (i : Label) :
    verticalHeight y (blockOf (verticalPartitionDatum y) i) = y i := by
  exact ((mem_datumBlock_iff_height y _ i).mp
    (label_mem_blockOf (verticalPartitionDatum y) i)).symm

/-- Actual indexed equality classes, including all tied limit heights. -/
theorem blockOf_eq_iff_vertical_eq (y : Label → ℝ) (i j : Label) :
    blockOf (verticalPartitionDatum y) i = blockOf (verticalPartitionDatum y) j ↔
      y i = y j := by
  constructor
  · intro h
    simpa only [height_blockOf] using congrArg (verticalHeight y) h
  · intro h
    apply (verticalHeight_strictMono y).injective
    simpa only [height_blockOf] using h

/-- No abstract grouping certificate is assumed: these are the literal
block memberships and equality classes of the actual vertical limit. -/
def VerticalLimitGrouping (y : Label → ℝ) (d : OrderedClusterDatum)
    (Y : BlockIndex d → ℝ) : Prop :=
  StrictMono Y ∧
  (∀ (a : BlockIndex d) (i : Label), i ∈ datumBlock d a ↔ y i = Y a) ∧
  (∀ i j : Label, blockOf d i = blockOf d j ↔ y i = y j)

theorem verticalPartition_groups_limit (y : Label → ℝ) :
    VerticalLimitGrouping y (verticalPartitionDatum y) (verticalHeight y) :=
  ⟨verticalHeight_strictMono y, mem_datumBlock_iff_height y,
    blockOf_eq_iff_vertical_eq y⟩

/-- A single simultaneous physical subsequence together with its actual
initial equality-class datum, without any final seed-order assertion. -/
theorem exists_initial_grouped_limit {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration}
    (hs : Tendsto s atTop atTop) (hq : ∀ ν, IsSolution m (s ν) (q ν)) :
    ∃ φ : ℕ → ℕ, ∃ y : Label → ℝ, ∃ d : OrderedClusterDatum,
      ∃ Y : BlockIndex d → ℝ,
        SequenceStart.InitialVerticalLimit m s q φ y ∧ VerticalLimitGrouping y d Y := by
  obtain ⟨φ, y, hlim⟩ := SequenceStart.exists_initial_vertical_limit hm hs hq
  exact ⟨φ, y, verticalPartitionDatum y, verticalHeight y, hlim,
    verticalPartition_groups_limit y⟩


/-- The literal weighted vertical mean of each INITIAL block tends to the
corresponding actual limit height; no scaling or seed equation is used. -/
theorem vertical_block_mean_tendsto {m : Masses} (hm : PositiveMasses m)
    {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    (hy : Tendsto (fun ν => SequenceStart.verticalCoordinates (q (φ ν)))
      atTop (nhds y)) (a : BlockIndex (verticalPartitionDatum y)) :
    Tendsto (fun ν => verticalCenterCoordinate m (verticalPartitionDatum y) (q (φ ν)) a)
      atTop (nhds (verticalHeight y a)) := by
  classical
  have hsum : Tendsto
      (fun ν => ∑ i ∈ datumBlockLabels (verticalPartitionDatum y) a, m i * q (φ ν) i 1)
      atTop (nhds (∑ i ∈ datumBlockLabels (verticalPartitionDatum y) a, m i * y i)) := by
    apply tendsto_finsetSum
    intro i _hi
    exact tendsto_const_nhds.mul (tendsto_pi_nhds.mp hy i)
  have heq : (∑ i ∈ datumBlockLabels (verticalPartitionDatum y) a, m i * y i) =
      datumBlockMass m (verticalPartitionDatum y) a * verticalHeight y a := by
    calc
      _ = ∑ i ∈ datumBlockLabels (verticalPartitionDatum y) a,
          m i * verticalHeight y a := by
        apply Finset.sum_congr rfl
        intro i hi
        have himem : i ∈ datumBlock (verticalPartitionDatum y) a := by
          simpa only [datumBlockLabels, List.mem_toFinset] using hi
        rw [(mem_datumBlock_iff_height y a i).mp himem]
      _ = _ := by rw [datumBlockMass, Finset.sum_mul]
  have hlim := (tendsto_const_nhds
    (x := (datumBlockMass m (verticalPartitionDatum y) a)⁻¹)).mul hsum
  simpa only [verticalCenterCoordinate, datumBlockMean_apply, heq, ← mul_assoc,
    inv_mul_cancel₀ (datumBlockMass_ne_zero hm (verticalPartitionDatum y) a),
    one_mul] using hlim

/-- Initial outer heights have the original exact mass-weighted center.
This is a centering conclusion only, not their one-dimensional force law. -/
theorem vertical_group_center_zero (m : Masses) {y : Label → ℝ}
    (hy : (∑ i, m i * y i) = 0) :
    (∑ a : BlockIndex (verticalPartitionDatum y),
      datumBlockMass m (verticalPartitionDatum y) a * verticalHeight y a) = 0 := by
  classical
  calc
    _ = ∑ a : BlockIndex (verticalPartitionDatum y),
        ∑ i ∈ datumBlockLabels (verticalPartitionDatum y) a, m i * y i := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [datumBlockMass, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have himem : i ∈ datumBlock (verticalPartitionDatum y) a := by
        simpa only [datumBlockLabels, List.mem_toFinset] using hi
      rw [(mem_datumBlock_iff_height y a i).mp himem]
    _ = ∑ i, m i * y i := sum_datumBlocks (verticalPartitionDatum y) _
    _ = 0 := hy

/-- Every selected original configuration has its actual mass-mean blow-up
coordinates for ANY concrete datum. The existing proved Qε inverse is used;
the scaled coordinates are not asserted to be bounded or convergent here. -/
theorem exists_selected_mean_coordinates {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ}
    (hq : ∀ ν, IsSolution m (s ν) (q ν)) (hgt : ∀ ν, 1 < s (φ ν))
    (d : OrderedClusterDatum) :
    ∃ h : ℕ → BlowupCoordinates m d,
      ∀ ν, CoordinatesOfConfiguration m d (epsilon (s (φ ν))) (q (φ ν)) (h ν) := by
  let r : ℕ → W m := fun ν => ⟨q (φ ν), by
    change centerLM m (q (φ ν)) = 0
    exact solution_center_zero m (lt_trans (by norm_num) (hgt ν)) (hq (φ ν))⟩
  let h : ℕ → BlowupCoordinates m d :=
    fun ν => meanInverse hm d (epsilon (s (φ ν))) (r ν)
  refine ⟨h, ?_⟩
  intro ν
  have he : epsilon (s (φ ν)) ≠ 0 :=
    ne_of_gt (SequenceStart.epsilon_pos (lt_trans (by norm_num) (hgt ν)))
  apply (represents_iff_coordinatesOfConfiguration hm he (h ν) (q (φ ν))).mp
  apply (represents_iff_eq_physicalCoordinates _ _ _).mpr
  exact (congrArg Subtype.val (coordinateQ_meanInverse hm d he (r ν))).symm

/-- Same actual grouping and SAME actual mean coordinates, still without
claiming compactness of internal P, H = O(ε³), or the final seed order. -/
theorem exists_initial_grouped_mean_limit {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration}
    (hs : Tendsto s atTop atTop) (hq : ∀ ν, IsSolution m (s ν) (q ν)) :
    ∃ φ : ℕ → ℕ, ∃ y : Label → ℝ, ∃ d : OrderedClusterDatum,
      ∃ Y : BlockIndex d → ℝ, ∃ h : ℕ → BlowupCoordinates m d,
        SequenceStart.InitialVerticalLimit m s q φ y ∧
        VerticalLimitGrouping y d Y ∧
        (∀ ν, CoordinatesOfConfiguration m d (epsilon (s (φ ν))) (q (φ ν)) (h ν)) ∧
        (∀ a : BlockIndex d, Tendsto (fun ν => outerY (h ν) a) atTop (nhds (Y a))) ∧
        (∑ a : BlockIndex d, datumBlockMass m d a * Y a) = 0 := by
  obtain ⟨φ, y, hlim⟩ := SequenceStart.exists_initial_vertical_limit hm hs hq
  obtain ⟨h, hh⟩ := exists_selected_mean_coordinates hm hq hlim.2.1 (verticalPartitionDatum y)
  refine ⟨φ, y, verticalPartitionDatum y, verticalHeight y, h, hlim,
    verticalPartition_groups_limit y, hh, ?_, ?_⟩
  · intro a
    have hY := vertical_block_mean_tendsto hm hlim.2.2.2.2.2.1 a
    apply hY.congr'
    exact Filter.Eventually.of_forall (fun ν => ((hh ν).2.2.1 a).symm)
  · exact vertical_group_center_zero m hlim.2.2.2.2.2.2.2.2

end FourBody.VerticalPartition


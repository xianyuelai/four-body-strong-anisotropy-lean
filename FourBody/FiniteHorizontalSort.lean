import FourBody.CoordinateEquivalence
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Pairwise
import Mathlib.Logic.Equiv.Basic

/-!
# Actual finite reordering by the horizontal limit

Frozen manuscript Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

The equality classes and their outer order are retained. Each actual
nonempty block is sorted using the actual horizontal coordinate u.
Strict order follows from injectivity ON THAT BLOCK, which the preceding
vertical-energy argument derives. The construction itself does not assume
a seed, a branch, or the paper's main conclusion.

STATIC CANDIDATE ONLY: no Lean/Lake elaboration has been performed.
-/

noncomputable section
open scoped BigOperators

namespace FourBody.FiniteHorizontalSort

/-- Sort the actual labels, rather than sorting abstract coordinate values
and losing the label-to-mass correspondence. -/
def sortBlock (u : Label → ℝ) (b : List Label) : List Label := by
  classical
  exact b.mergeSort (fun i j => decide (u i ≤ u j))

theorem sortBlock_perm (u : Label → ℝ) (b : List Label) :
    (sortBlock u b).Perm b := by
  classical
  exact List.mergeSort_perm b (fun i j => decide (u i ≤ u j))

@[simp]
theorem sortBlock_length (u : Label → ℝ) (b : List Label) :
    (sortBlock u b).length = b.length :=
  (sortBlock_perm u b).length_eq

@[simp]
theorem mem_sortBlock (u : Label → ℝ) (b : List Label) (i : Label) :
    i ∈ sortBlock u b ↔ i ∈ b :=
  (sortBlock_perm u b).mem_iff

theorem sortBlock_nodup (u : Label → ℝ) {b : List Label} (hb : b.Nodup) :
    (sortBlock u b).Nodup :=
  (sortBlock_perm u b).nodup_iff.mpr hb

theorem sortBlock_nonempty (u : Label → ℝ) {b : List Label} (hb : b ≠ []) :
    sortBlock u b ≠ [] := by
  intro he
  apply hb
  have hp := (sortBlock_perm u b).symm
  rw [he] at hp
  exact hp.eq_nil

theorem sortBlock_pairwise_le (u : Label → ℝ) (b : List Label) :
    (sortBlock u b).Pairwise (fun i j => u i ≤ u j) := by
  classical
  dsimp [sortBlock]
  simpa using List.pairwise_mergeSort
    (le := fun i j : Label => decide (u i ≤ u j))
    (fun a b c hab hbc => by
      have hab' : u a ≤ u b := by simpa using hab
      have hbc' : u b ≤ u c := by simpa using hbc
      simpa using hab'.trans hbc')
    (fun a b => by simpa using le_total (u a) (u b)) b

/-- Every hypothesis refers to actual label membership. Injectivity is
only needed inside this block; different blocks may have equal u values. -/
theorem sortBlock_pairwise_lt (u : Label → ℝ) {b : List Label}
    (hb : b.Nodup)
    (hinj : ∀ {i j : Label}, i ∈ b → j ∈ b → u i = u j → i = j) :
    (sortBlock u b).Pairwise (fun i j => u i < u j) := by
  apply ((sortBlock_pairwise_le u b).and (sortBlock_nodup u hb)).imp_of_mem
  intro i j hi hj h
  apply lt_of_le_of_ne h.1
  intro he
  exact h.2 (hinj ((mem_sortBlock u b i).mp hi)
    ((mem_sortBlock u b j).mp hj) he)

theorem sortBlock_get_strictMono (u : Label → ℝ) {b : List Label}
    (hb : b.Nodup)
    (hinj : ∀ {i j : Label}, i ∈ b → j ∈ b → u i = u j → i = j) :
    StrictMono (fun j : Fin (sortBlock u b).length => u ((sortBlock u b).get j)) := by
  intro j k hjk
  exact (sortBlock_pairwise_lt u hb hinj).rel_get_of_lt hjk

/-- Sorting each component preserves the concatenated label multiset. -/
theorem flatten_map_sortBlock_perm (u : Label → ℝ) (bs : List (List Label)) :
    (bs.map (sortBlock u)).flatten.Perm bs.flatten := by
  induction bs with
  | nil => exact List.Perm.refl []
  | cons b bs ih =>
      simpa only [List.map_cons, List.flatten_cons] using
        (sortBlock_perm u b).append ih

/-- The same outer sequence of actual sets, with the new internal order. -/
def reorderedDatum (d : OrderedClusterDatum) (u : Label → ℝ) :
    OrderedClusterDatum where
  blocks := d.blocks.map (sortBlock u)
  nonempty_blocks := by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    exact sortBlock_nonempty u (d.nonempty_blocks c hc)
  labels_once := (flatten_map_sortBlock_perm u d.blocks).trans d.labels_once

@[simp]
theorem reordered_blocks_length (d : OrderedClusterDatum) (u : Label → ℝ) :
    (reorderedDatum d u).blocks.length = d.blocks.length := by
  simp only [reorderedDatum, List.length_map]

/-- Same numeric position, cast through the proved outer-list length. -/
def reorderedBlockIndex (d : OrderedClusterDatum) (u : Label → ℝ) :
    BlockIndex d ≃ BlockIndex (reorderedDatum d u) :=
  finCongr (reordered_blocks_length d u).symm

@[simp]
theorem reorderedBlockIndex_val (d : OrderedClusterDatum) (u : Label → ℝ)
    (a : BlockIndex d) : (reorderedBlockIndex d u a).val = a.val := rfl

theorem reorderedBlockIndex_strictMono (d : OrderedClusterDatum) (u : Label → ℝ) :
    StrictMono (reorderedBlockIndex d u) := by
  intro a b hab
  exact hab

theorem reordered_block_eq_sortBlock (d : OrderedClusterDatum) (u : Label → ℝ)
    (a : BlockIndex d) :
    datumBlock (reorderedDatum d u) (reorderedBlockIndex d u a) =
      sortBlock u (datumBlock d a) := by
  change (d.blocks.map (sortBlock u))[a.val]'(by
    simpa only [List.length_map] using a.isLt) =
      sortBlock u (d.blocks[a.val]'a.isLt)
  exact List.getElem_map (sortBlock u)

theorem reordered_block_perm (d : OrderedClusterDatum) (u : Label → ℝ)
    (a : BlockIndex d) :
    (datumBlock (reorderedDatum d u) (reorderedBlockIndex d u a)).Perm
      (datumBlock d a) := by
  rw [reordered_block_eq_sortBlock]
  exact sortBlock_perm u (datumBlock d a)

@[simp]
theorem mem_reordered_block (d : OrderedClusterDatum) (u : Label → ℝ)
    (a : BlockIndex d) (i : Label) :
    i ∈ datumBlock (reorderedDatum d u) (reorderedBlockIndex d u a) ↔
      i ∈ datumBlock d a :=
  (reordered_block_perm d u a).mem_iff

@[simp]
theorem reordered_block_labels (d : OrderedClusterDatum) (u : Label → ℝ)
    (a : BlockIndex d) :
    datumBlockLabels (reorderedDatum d u) (reorderedBlockIndex d u a) =
      datumBlockLabels d a := by
  classical
  ext i
  simp only [datumBlockLabels, List.mem_toFinset, mem_reordered_block]

@[simp]
theorem reordered_block_mass (m : Masses) (d : OrderedClusterDatum) (u : Label → ℝ)
    (a : BlockIndex d) :
    datumBlockMass m (reorderedDatum d u) (reorderedBlockIndex d u a) =
      datumBlockMass m d a := by
  simp only [datumBlockMass, reordered_block_labels]

@[simp]
theorem reordered_block_mean (m : Masses) (d : OrderedClusterDatum) (u : Label → ℝ)
    (q : Configuration) (a : BlockIndex d) :
    datumBlockMean m (reorderedDatum d u) q (reorderedBlockIndex d u a) =
      datumBlockMean m d q a := by
  simp only [datumBlockMean, reordered_block_mass, reordered_block_labels]

/-- The position of every actual label changes only by the outer length cast. -/
theorem reordered_blockOf (d : OrderedClusterDatum) (u : Label → ℝ) (i : Label) :
    blockOf (reorderedDatum d u) i = reorderedBlockIndex d u (blockOf d i) := by
  apply blockOf_eq_of_mem
  exact (mem_reordered_block d u (blockOf d i) i).mpr (label_mem_blockOf d i)

theorem reordered_internal_length (d : OrderedClusterDatum) (u : Label → ℝ)
    (a : BlockIndex d) :
    (datumBlock (reorderedDatum d u) (reorderedBlockIndex d u a)).length =
      (datumBlock d a).length :=
  (reordered_block_perm d u a).length_eq

/-- The actual reordered getter has the prescribed strictly increasing u.
The input injectivity is literal label-membership injectivity. -/
theorem reordered_internal_strictMono (d : OrderedClusterDatum) (u : Label → ℝ)
    (a : BlockIndex d)
    (hinj : ∀ {i j : Label}, i ∈ datumBlock d a → j ∈ datumBlock d a →
      u i = u j → i = j) :
    StrictMono
      (fun j : InternalIndex (reorderedDatum d u) (reorderedBlockIndex d u a) =>
        u (internalLabel (reorderedDatum d u) (reorderedBlockIndex d u a) j)) := by
  intro j k hjk
  have hpair :
      (datumBlock (reorderedDatum d u) (reorderedBlockIndex d u a)).Pairwise
        (fun i j => u i < u j) := by
    rw [reordered_block_eq_sortBlock]
    exact sortBlock_pairwise_lt u (d.block_nodup (datumBlock_mem d a)) hinj
  exact hpair.rel_get_of_lt hjk

/-- A transparent finite package for a later seed-assembly step. -/
def ReorderedByHorizontal (d d' : OrderedClusterDatum) (u : Label → ℝ)
    (e : BlockIndex d ≃ BlockIndex d') : Prop :=
  (∀ a, (e a).val = a.val) ∧
  (∀ a, (datumBlock d' (e a)).Perm (datumBlock d a)) ∧
  (∀ a, StrictMono
    (fun j : InternalIndex d' (e a) => u (internalLabel d' (e a) j)))

/-- Construct the order; never assume an already ordered seed as a premise. -/
theorem exists_reordered_by_horizontal (d : OrderedClusterDatum) (u : Label → ℝ)
    (hinj : ∀ a : BlockIndex d, ∀ {i j : Label},
      i ∈ datumBlock d a → j ∈ datumBlock d a → u i = u j → i = j) :
    ∃ d' : OrderedClusterDatum, ∃ e : BlockIndex d ≃ BlockIndex d',
      ReorderedByHorizontal d d' u e := by
  exact ⟨reorderedDatum d u, reorderedBlockIndex d u,
    reorderedBlockIndex_val d u, reordered_block_perm d u,
    fun a => reordered_internal_strictMono d u a (hinj a)⟩


/-- Index transport from the reordered datum to the original datum. -/
def oldIndex (d : OrderedClusterDatum) (u : Label → ℝ) :
    BlockIndex (reorderedDatum d u) ≃ BlockIndex d :=
  (reorderedBlockIndex d u).symm

/-- Index transport in the direction used to construct the reordered datum. -/
def newIndex (d : OrderedClusterDatum) (u : Label → ℝ) :
    BlockIndex d ≃ BlockIndex (reorderedDatum d u) :=
  (oldIndex d u).symm

@[simp]
theorem oldIndex_val (d : OrderedClusterDatum) (u : Label → ℝ)
    (a : BlockIndex (reorderedDatum d u)) : (oldIndex d u a).val = a.val := rfl

@[simp]
theorem newIndex_val (d : OrderedClusterDatum) (u : Label → ℝ)
    (a : BlockIndex d) : (newIndex d u a).val = a.val := rfl

theorem oldIndex_strictMono (d : OrderedClusterDatum) (u : Label → ℝ) :
    StrictMono (oldIndex d u) := by
  intro a b hab
  exact hab

theorem newIndex_strictMono (d : OrderedClusterDatum) (u : Label → ℝ) :
    StrictMono (newIndex d u) := by
  intro a b hab
  exact hab

theorem datumBlock_perm (d : OrderedClusterDatum) (u : Label → ℝ)
    (a : BlockIndex (reorderedDatum d u)) :
    (datumBlock (reorderedDatum d u) a).Perm (datumBlock d (oldIndex d u a)) := by
  simpa only [oldIndex, Equiv.apply_symm_apply] using
    reordered_block_perm d u (oldIndex d u a)

theorem datumBlock_mem_iff (d : OrderedClusterDatum) (u : Label → ℝ)
    (a : BlockIndex (reorderedDatum d u)) (i : Label) :
    i ∈ datumBlock (reorderedDatum d u) a ↔ i ∈ datumBlock d (oldIndex d u a) :=
  (datumBlock_perm d u a).mem_iff

theorem mem_datumBlock_iff (d : OrderedClusterDatum) (u : Label → ℝ)
    (a : BlockIndex (reorderedDatum d u)) (i : Label) :
    i ∈ datumBlock (reorderedDatum d u) a ↔ i ∈ datumBlock d (oldIndex d u a) :=
  datumBlock_mem_iff d u a i

theorem datumBlockLabels_eq (d : OrderedClusterDatum) (u : Label → ℝ)
    (a : BlockIndex (reorderedDatum d u)) :
    datumBlockLabels (reorderedDatum d u) a = datumBlockLabels d (oldIndex d u a) := by
  simpa only [oldIndex, Equiv.apply_symm_apply] using
    reordered_block_labels d u (oldIndex d u a)

theorem datumBlockMass_eq (m : Masses) (d : OrderedClusterDatum) (u : Label → ℝ)
    (a : BlockIndex (reorderedDatum d u)) :
    datumBlockMass m (reorderedDatum d u) a = datumBlockMass m d (oldIndex d u a) := by
  simp only [datumBlockMass, datumBlockLabels_eq]

theorem datumBlockMean_eq (m : Masses) (d : OrderedClusterDatum) (u : Label → ℝ)
    (q : Configuration) (a : BlockIndex (reorderedDatum d u)) :
    datumBlockMean m (reorderedDatum d u) q a = datumBlockMean m d q (oldIndex d u a) := by
  simp only [datumBlockMean, datumBlockMass_eq, datumBlockLabels_eq]

theorem blockOf_new_to_old (d : OrderedClusterDatum) (u : Label → ℝ) (i : Label) :
    oldIndex d u (blockOf (reorderedDatum d u) i) = blockOf d i := by
  rw [reordered_blockOf]
  exact (reorderedBlockIndex d u).symm_apply_apply (blockOf d i)

/-- Final adapter: increasing actual horizontal coordinates in each new block.
The premise is still the derived injectivity in each original actual block. -/
theorem strictMono_internalLabel (d : OrderedClusterDatum) (u : Label → ℝ)
    (hinj : ∀ a : BlockIndex d, ∀ {i j : Label},
      i ∈ datumBlock d a → j ∈ datumBlock d a → u i = u j → i = j)
    (a : BlockIndex (reorderedDatum d u)) :
    StrictMono (fun j : InternalIndex (reorderedDatum d u) a =>
      u (internalLabel (reorderedDatum d u) a j)) := by
  have h := reordered_internal_strictMono d u (oldIndex d u a) (hinj (oldIndex d u a))
  have he : reorderedBlockIndex d u (oldIndex d u a) = a :=
    (reorderedBlockIndex d u).apply_symm_apply a
  rw [he] at h
  exact h

end FourBody.FiniteHorizontalSort

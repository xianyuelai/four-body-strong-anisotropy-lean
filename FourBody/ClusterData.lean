import FourBody.Labels
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# The actual ordered cluster data in the v2 manuscript

The manuscript's label set `{1,2,3,4}` is represented by `Fin 4` with the
fixed relabelling `i ↦ i.val + 1`. A block is a list: its list order is the
prescribed strict internal label order. The outer list order is the order
of the blocks. Every label occurs exactly once, and every block is nonempty.

This module proves the combinatorial part of the manuscript, independently
of the analytic existence, uniqueness, recovery, and exhaustion obligations.
No assertion about solutions of the four-body equation occurs here.
-/

namespace FourBody


/-- Actual ordered nonempty blocks, with an internal order in each block. -/
@[ext]
structure OrderedClusterDatum where
  blocks : List (List Label)
  nonempty_blocks : ∀ b ∈ blocks, b ≠ []
  labels_once : blocks.flatten.Perm (List.finRange 4)
  deriving DecidableEq

abbrev LabelOrder := {l : List Label // l.Perm (List.finRange 4)}

namespace LabelOrder

theorem length_eq (l : LabelOrder) : l.val.length = 4 := by
  simpa using l.property.length_eq

theorem nodup (l : LabelOrder) : l.val.Nodup :=
  l.property.nodup_iff.mpr (List.nodup_finRange 4)

theorem mem (l : LabelOrder) (i : Label) : i ∈ l.val :=
  l.property.mem_iff.mpr (List.mem_finRange i)

/-- Read the ordered labels at their four positions. -/
def permutation (l : LabelOrder) : Equiv.Perm Label :=
  (finCongr l.length_eq.symm).trans
    (List.Nodup.getEquivOfForallMemList l.val l.nodup l.mem)

/-- Write a permutation as its ordered list of values. -/
def ofPermutation (p : Equiv.Perm Label) : LabelOrder :=
  ⟨List.ofFn p, by
    rw [List.ofFn_eq_map]
    exact p.map_finRange_perm⟩

@[simp]
theorem permutation_apply (l : LabelOrder) (i : Label) :
    l.permutation i = l.val.get (Fin.cast l.length_eq.symm i) :=
  rfl

@[simp]
theorem ofFn_permutation (l : LabelOrder) :
    List.ofFn l.permutation = l.val := by
  change List.ofFn (fun i : Fin 4 => l.val.get (Fin.cast l.length_eq.symm i)) = l.val
  rw [← List.ofFn_congr l.length_eq]
  exact List.ofFn_get l.val

/-- An explicit inverse pair: reading and writing the full label order. -/
def equivPermutation : LabelOrder ≃ Equiv.Perm Label where
  toFun := permutation
  invFun := ofPermutation
  left_inv l := by
    apply Subtype.ext
    exact l.ofFn_permutation
  right_inv p := by
    apply Equiv.ext
    intro i
    change (List.ofFn p).get (Fin.cast (ofPermutation p).length_eq.symm i) = p i
    rw [List.get_eq_getElem, List.getElem_ofFn]
    congr 1

end LabelOrder

namespace OrderedClusterDatum

theorem flatten_length (d : OrderedClusterDatum) : d.blocks.flatten.length = 4 := by
  simpa using d.labels_once.length_eq

theorem flatten_nodup (d : OrderedClusterDatum) : d.blocks.flatten.Nodup :=
  d.labels_once.nodup_iff.mpr (List.nodup_finRange 4)

theorem every_label_mem (d : OrderedClusterDatum) (i : Label) : i ∈ d.blocks.flatten :=
  d.labels_once.mem_iff.mpr (List.mem_finRange i)

/-- Each actual block lists its labels without repetition. -/
theorem block_nodup (d : OrderedClusterDatum) {b : List Label} (hb : b ∈ d.blocks) :
    b.Nodup :=
  (List.nodup_flatten.mp d.flatten_nodup).1 b hb

/-- Blocks in different positions have disjoint label sets. -/
theorem pairwise_disjoint_blocks (d : OrderedClusterDatum) :
    d.blocks.Pairwise List.Disjoint :=
  (List.nodup_flatten.mp d.flatten_nodup).2

/-- Positions and labels in a block correspond concretely by the list getter. -/
def blockLabelsEquiv (d : OrderedClusterDatum) (b : List Label) (hb : b ∈ d.blocks) :
    Fin b.length ≃ {i : Label // i ∈ b} :=
  List.Nodup.getEquiv b (d.block_nodup hb)

/-- The prescribed strict order is the order of positions in the actual block. -/
def internalLt (d : OrderedClusterDatum) (b : List Label) (hb : b ∈ d.blocks)
    (i j : {i : Label // i ∈ b}) : Prop :=
  (d.blockLabelsEquiv b hb).symm i < (d.blockLabelsEquiv b hb).symm j

theorem internalLt_irrefl (d : OrderedClusterDatum) (b : List Label) (hb : b ∈ d.blocks)
    (i : {i : Label // i ∈ b}) : ¬d.internalLt b hb i i :=
  lt_irrefl _

theorem internalLt_trans (d : OrderedClusterDatum) (b : List Label) (hb : b ∈ d.blocks)
    (i j k : {i : Label // i ∈ b}) :
    d.internalLt b hb i j → d.internalLt b hb j k → d.internalLt b hb i k :=
  lt_trans

theorem internalLt_trichotomy (d : OrderedClusterDatum) (b : List Label) (hb : b ∈ d.blocks)
    (i j : {i : Label // i ∈ b}) :
    d.internalLt b hb i j ∨ i = j ∨ d.internalLt b hb j i := by
  rcases lt_trichotomy ((d.blockLabelsEquiv b hb).symm i)
    ((d.blockLabelsEquiv b hb).symm j) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ((d.blockLabelsEquiv b hb).symm.injective h))
  · exact Or.inr (Or.inr h)

/-- Concatenate blocks without forgetting either order. -/
def labelOrder (d : OrderedClusterDatum) : LabelOrder :=
  ⟨d.blocks.flatten, d.labels_once⟩

/-- The positive block lengths, summing to four. -/
def composition (d : OrderedClusterDatum) : Composition 4 where
  blocks := d.blocks.map List.length
  blocks_pos := by
    intro n hn
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hn
    exact List.length_pos_iff.mpr (d.nonempty_blocks b hb)
  blocks_sum := by
    rw [← List.length_flatten]
    exact d.flatten_length

def blockCount (d : OrderedClusterDatum) : ℕ := d.blocks.length

@[simp]
theorem composition_length (d : OrderedClusterDatum) :
    d.composition.length = d.blockCount := by
  simp [composition, Composition.length, blockCount]

theorem blockCount_pos (d : OrderedClusterDatum) : 0 < d.blockCount := by
  rw [← d.composition_length]
  exact d.composition.length_pos_of_pos (by decide)

theorem blockCount_le_four (d : OrderedClusterDatum) : d.blockCount ≤ 4 := by
  rw [← d.composition_length]
  exact d.composition.length_le

/-- Split an ordered label list at the positive composition lengths. -/
def ofOrderComposition (l : LabelOrder) (c : Composition 4) : OrderedClusterDatum where
  blocks := l.val.splitWrtComposition (c.cast l.length_eq.symm)
  nonempty_blocks := by
    intro b hb
    exact List.ne_nil_of_length_pos (List.length_pos_of_mem_splitWrtComposition hb)
  labels_once := by
    rw [List.flatten_splitWrtComposition]
    exact l.property

@[simp]
theorem labelOrder_ofOrderComposition (l : LabelOrder) (c : Composition 4) :
    (ofOrderComposition l c).labelOrder = l := by
  apply Subtype.ext
  exact List.flatten_splitWrtComposition l.val (c.cast l.length_eq.symm)

@[simp]
theorem composition_ofOrderComposition (l : LabelOrder) (c : Composition 4) :
    (ofOrderComposition l c).composition = c := by
  apply Composition.ext
  exact List.map_length_splitWrtComposition l.val (c.cast l.length_eq.symm)

@[simp]
theorem ofOrderComposition_labelOrder_composition (d : OrderedClusterDatum) :
    ofOrderComposition d.labelOrder d.composition = d := by
  apply OrderedClusterDatum.ext
  apply List.splitWrtComposition_flatten
  rfl

/-- The genuine block data and concatenation/composition constructions are inverse. -/
def equivOrderComposition : OrderedClusterDatum ≃ LabelOrder × Composition 4 where
  toFun d := (d.labelOrder, d.composition)
  invFun p := ofOrderComposition p.1 p.2
  left_inv := ofOrderComposition_labelOrder_composition
  right_inv p := by
    apply Prod.ext
    · exact labelOrder_ofOrderComposition p.1 p.2
    · exact composition_ofOrderComposition p.1 p.2

/-- The permutation is read from the concatenated blocks; no solution bijection is assumed. -/
def equivPermutationComposition :
    OrderedClusterDatum ≃ Equiv.Perm Label × Composition 4 :=
  equivOrderComposition.trans
    (Equiv.prodCongr LabelOrder.equivPermutation (Equiv.refl _))

end OrderedClusterDatum

/-- A concrete Boolean indicator for each of the three possible interior cuts. -/
def finsetCutsEquiv : Finset (Fin 3) ≃ (Fin 3 → Bool) where
  toFun s i := decide (i ∈ s)
  invFun b := Finset.univ.filter (fun i => b i = true)
  left_inv s := by
    ext i
    simp
  right_inv b := by
    funext i
    simp

/-- The interior boundaries are exactly the cuts between adjacent labels. -/
def compositionCutsEquiv : Composition 4 ≃ (Fin 3 → Bool) :=
  ((compositionEquiv 4).trans (compositionAsSetEquiv 4)).trans finsetCutsEquiv

/-- The manuscript's explicit 4! × 2^3 encoding, with a proved inverse. -/
def datumEncoding : OrderedClusterDatum ≃ Equiv.Perm Label × (Fin 3 → Bool) :=
  OrderedClusterDatum.equivPermutationComposition.trans
    (Equiv.prodCongr (Equiv.refl _) compositionCutsEquiv)

@[simp]
theorem decode_encode (d : OrderedClusterDatum) : datumEncoding.symm (datumEncoding d) = d :=
  datumEncoding.symm_apply_apply d

@[simp]
theorem encode_decode (p : Equiv.Perm Label × (Fin 3 → Bool)) :
    datumEncoding (datumEncoding.symm p) = p :=
  datumEncoding.apply_symm_apply p

/-- Finiteness is obtained from the proved encoding, rather than postulated. -/
instance : Fintype OrderedClusterDatum :=
  Fintype.ofEquiv (Equiv.Perm Label × (Fin 3 → Bool)) datumEncoding.symm

theorem card_orderedClusterDatum : Fintype.card OrderedClusterDatum = 192 := by
  rw [Fintype.card_congr datumEncoding, Fintype.card_prod, Fintype.card_perm]
  norm_num [Label, Fintype.card_fun, Nat.factorial]

/-- Move a predicate on a product's second factor into that factor's subtype. -/
def productSubtypeSndEquiv (P : Composition 4 → Prop) :
    {p : Equiv.Perm Label × Composition 4 // P p.2} ≃
      Equiv.Perm Label × {c : Composition 4 // P c} where
  toFun p := (p.val.1, ⟨p.val.2, p.property⟩)
  invFun p := ⟨(p.1, p.2.val), p.2.property⟩
  left_inv p := by cases p; rfl
  right_inv p := by rcases p with ⟨p, c, hc⟩; rfl

/-- Restrict the actual datum equivalence to any collection of block counts. -/
def datumBlockPredicateEquiv (P : ℕ → Prop) :
    {d : OrderedClusterDatum // P d.blockCount} ≃
      Equiv.Perm Label × {c : Composition 4 // P c.length} :=
  ((OrderedClusterDatum.equivPermutationComposition).subtypeEquiv
    (by intro d; simp [OrderedClusterDatum.equivPermutationComposition,
      OrderedClusterDatum.equivOrderComposition])).trans
    (productSubtypeSndEquiv (fun c => P c.length))

theorem card_oneBlockComposition :
    Fintype.card {c : Composition 4 // c.length = 1} = 1 := by decide

theorem card_fourBlockComposition :
    Fintype.card {c : Composition 4 // c.length = 4} = 1 := by decide

theorem card_twoBlockComposition :
    Fintype.card {c : Composition 4 // c.length = 2} = 3 := by decide

theorem card_threeBlockComposition :
    Fintype.card {c : Composition 4 // c.length = 3} = 3 := by decide

theorem card_middleBlockComposition :
    Fintype.card {c : Composition 4 // 1 < c.length ∧ c.length < 4} = 6 := by decide

theorem card_oneBlockData :
    Fintype.card {d : OrderedClusterDatum // d.blockCount = 1} = 24 := by
  rw [Fintype.card_congr (datumBlockPredicateEquiv (· = 1)), Fintype.card_prod,
    Fintype.card_perm, card_oneBlockComposition]
  norm_num [Label, Nat.factorial]

theorem card_fourBlockData :
    Fintype.card {d : OrderedClusterDatum // d.blockCount = 4} = 24 := by
  rw [Fintype.card_congr (datumBlockPredicateEquiv (· = 4)), Fintype.card_prod,
    Fintype.card_perm, card_fourBlockComposition]
  norm_num [Label, Nat.factorial]

theorem card_twoBlockData :
    Fintype.card {d : OrderedClusterDatum // d.blockCount = 2} = 72 := by
  rw [Fintype.card_congr (datumBlockPredicateEquiv (· = 2)), Fintype.card_prod,
    Fintype.card_perm, card_twoBlockComposition]
  norm_num [Label, Nat.factorial]

theorem card_threeBlockData :
    Fintype.card {d : OrderedClusterDatum // d.blockCount = 3} = 72 := by
  rw [Fintype.card_congr (datumBlockPredicateEquiv (· = 3)), Fintype.card_prod,
    Fintype.card_perm, card_threeBlockComposition]
  norm_num [Label, Nat.factorial]

/-- The manuscript's refined count for all permitted numbers of blocks. -/
theorem card_data_with_k_blocks (k : ℕ) (hk₁ : 1 ≤ k) (hk₄ : k ≤ 4) :
    Fintype.card {d : OrderedClusterDatum // d.blockCount = k} =
      24 * Nat.choose 3 (k - 1) := by
  interval_cases k <;>
    norm_num [card_oneBlockData, card_twoBlockData, card_threeBlockData, card_fourBlockData]

theorem card_middleBlockData :
    Fintype.card {d : OrderedClusterDatum // 1 < d.blockCount ∧ d.blockCount < 4} = 144 := by
  rw [Fintype.card_congr (datumBlockPredicateEquiv (fun k => 1 < k ∧ k < 4)),
    Fintype.card_prod, Fintype.card_perm, card_middleBlockComposition]
  norm_num [Label, Nat.factorial]

end FourBody

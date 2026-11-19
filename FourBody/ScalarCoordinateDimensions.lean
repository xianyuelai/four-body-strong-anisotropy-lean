import FourBody.ScalarCenteredDimensions
import FourBody.CoordinateProduct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

/-!
Literal S4-B02, frozen Pro v2 lines 522--525:
  2 (k - 1) + 2 sum_a (|B_a| - 1) = 6.
The split is proved on the actual CoordinateProduct factors and transported
by the actual continuous linear equivalence to BlowupCoordinates. The sum of
block cardinalities is obtained from the actual ordered partition, not taken
as an input. No already-known dimension-six theorem for W is used.

STATIC ONLY: no Lean/Lake invocation, compilation, strict lint, or axiom audit
has been performed for this module.
-/

noncomputable section
open scoped BigOperators
namespace FourBody.ScalarCoordinateDimensions

/-- The actual finite disjoint-cover partition counts each of the four
original labels exactly once. -/
theorem sum_block_card_eq_four (d : OrderedClusterDatum) :
    (∑ a : BlockIndex d, (datumBlockLabels d a).card) = 4 := by
  simpa using (sum_datumBlocks d (fun _ : Label => (1 : ℕ)))

/-- Actual list positions have the same cardinality as the label sets. -/
theorem sum_block_length_eq_four (d : OrderedClusterDatum) :
    (∑ a : BlockIndex d, (datumBlock d a).length) = 4 := by
  simpa only [ScalarDimensions.datumBlockLabels_card_eq_length] using
    sum_block_card_eq_four d

/-- Every actual block is nonempty, so natural subtraction can be summed
without truncation of any individual block term. -/
theorem sum_reduced_block_card (d : OrderedClusterDatum) :
    (∑ a : BlockIndex d, ((datumBlockLabels d a).card - 1)) =
      4 - d.blocks.length := by
  calc
    (∑ a : BlockIndex d, ((datumBlockLabels d a).card - 1)) =
        (∑ a : BlockIndex d, (datumBlockLabels d a).card) -
          (∑ _a : BlockIndex d, (1 : ℕ)) :=
      Finset.sum_tsub_distrib Finset.univ
        (fun a _ha => Nat.succ_le_of_lt
          (Finset.card_pos.mpr (datumBlockLabels_nonempty d a)))
    _ = 4 - d.blocks.length := by
      rw [sum_block_card_eq_four]
      simp

theorem sum_reduced_block_length (d : OrderedClusterDatum) :
    (∑ a : BlockIndex d, ((datumBlock d a).length - 1)) =
      4 - d.blocks.length := by
  simpa only [ScalarDimensions.datumBlockLabels_card_eq_length] using
    sum_reduced_block_card d

/-- The literal arithmetic identity, including k = 1 and singleton blocks. -/
theorem explicit_dimension_split_eq_six (d : OrderedClusterDatum) :
    2 * (d.blocks.length - 1) +
      2 * (∑ a : BlockIndex d, ((datumBlockLabels d a).card - 1)) = 6 := by
  rw [sum_reduced_block_card]
  have hkpos : 0 < d.blocks.length := d.blockCount_pos
  have hkle : d.blocks.length ≤ 4 := d.blockCount_le_four
  omega

theorem explicit_dimension_split_length_eq_six (d : OrderedClusterDatum) :
    2 * (d.blocks.length - 1) +
      2 * (∑ a : BlockIndex d, ((datumBlock d a).length - 1)) = 6 := by
  simpa only [ScalarDimensions.datumBlockLabels_card_eq_length] using
    explicit_dimension_split_eq_six d

/-- The two actual outer scalar center spaces contribute 2(k - 1). -/
theorem outer_pair_finrank {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) :
    Module.finrank ℝ
      (CoordinateProduct.OuterSpace m d × CoordinateProduct.OuterSpace m d) =
        2 * (d.blocks.length - 1) := by
  simp only [Module.finrank_prod, ScalarDimensions.outerSpace_finrank hm d, two_mul]

/-- Each pair of actual internal scalar center spaces contributes
2(|B_a| - 1); a singleton contributes exactly zero. -/
theorem inner_pair_finrank {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (a : BlockIndex d) :
    Module.finrank ℝ
      (CoordinateProduct.InnerSpace m d a × CoordinateProduct.InnerSpace m d a) =
        2 * ((datumBlockLabels d a).card - 1) := by
  simp only [Module.finrank_prod, ScalarDimensions.innerSpace_finrank_card hm d a, two_mul]

/-- The actual dependent product sums over the actual ordered block indices. -/
theorem internal_product_finrank {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) :
    Module.finrank ℝ
      (∀ a : BlockIndex d,
        CoordinateProduct.InnerSpace m d a × CoordinateProduct.InnerSpace m d a) =
      2 * (∑ a : BlockIndex d, ((datumBlockLabels d a).card - 1)) := by
  rw [Module.finrank_pi_fintype]
  simp_rw [inner_pair_finrank hm d]
  rw [Finset.mul_sum]

/-- The actual product has the literal outer-plus-inner dimension split,
before evaluating the arithmetic expression to six. -/
theorem productSpace_finrank_split {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) :
    Module.finrank ℝ (CoordinateProduct.ProductSpace m d) =
      2 * (d.blocks.length - 1) +
        2 * (∑ a : BlockIndex d, ((datumBlockLabels d a).card - 1)) := by
  change Module.finrank ℝ
    ((CoordinateProduct.OuterSpace m d × CoordinateProduct.OuterSpace m d) ×
      (∀ a : BlockIndex d,
        CoordinateProduct.InnerSpace m d a × CoordinateProduct.InnerSpace m d a)) = _
  rw [Module.finrank_prod, outer_pair_finrank hm d, internal_product_finrank hm d]

/-- Transport by the actual coordinate-product CLE, preserving the explicit
factor dimension expression rather than substituting a W-dimension theorem. -/
theorem blowupCoordinates_finrank_split {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) :
    Module.finrank ℝ (BlowupCoordinates m d) =
      2 * (d.blocks.length - 1) +
        2 * (∑ a : BlockIndex d, ((datumBlockLabels d a).card - 1)) :=
  (CoordinateProduct.equivalence m d).toLinearEquiv.finrank_eq.trans
    (productSpace_finrank_split hm d)

/-- The source-facing endpoint retains both equalities of the literal
S4-B02 statement for every genuine ordered partition of the four labels. -/
theorem blowupCoordinates_finrank_explicit_split {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) :
    Module.finrank ℝ (BlowupCoordinates m d) =
        2 * (d.blocks.length - 1) +
          2 * (∑ a : BlockIndex d, ((datumBlockLabels d a).card - 1)) ∧
      2 * (d.blocks.length - 1) +
          2 * (∑ a : BlockIndex d, ((datumBlockLabels d a).card - 1)) = 6 :=
  ⟨blowupCoordinates_finrank_split hm d, explicit_dimension_split_eq_six d⟩

theorem blowupCoordinates_finrank_six {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) : Module.finrank ℝ (BlowupCoordinates m d) = 6 :=
  (blowupCoordinates_finrank_split hm d).trans (explicit_dimension_split_eq_six d)

end FourBody.ScalarCoordinateDimensions

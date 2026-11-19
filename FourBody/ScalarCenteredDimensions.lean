import FourBody.ScalarGeometry
import FourBody.CoordinateProduct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Finset.Card

set_option autoImplicit false

/-!
The literal mass-centered scalar spaces have dimension n - 1. The center
map is proved surjective from positive masses when n > 0, using an explicit
constant-vector preimage. Fin 0 is treated separately: the center map is
zero and every centered vector is zero. The outer and internal dimensions
use the actual block masses and actual block labels of CoordinateProduct.

STATIC CANDIDATE ONLY: this file has not been compiled or axiom-audited.
No Lean or Lake process was run while preparing these proofs.
-/

noncomputable section
open scoped BigOperators
namespace FourBody.ScalarDimensions

open ScalarGeometry

theorem scalarConfiguration_finrank (n : ℕ) :
    Module.finrank ℝ (ScalarConfiguration n) = n := by
  change Module.finrank ℝ (Fin n → ℝ) = n
  exact (Module.finrank_pi ℝ (ι := Fin n)).trans (Fintype.card_fin n)

/-- Constant vectors give actual preimages; no surjectivity is assumed. -/
theorem scalarCenterLM_surjective {n : ℕ} (hn : 0 < n) (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) : Function.Surjective (scalarCenterLM μ) := by
  intro r
  refine ⟨fun _ => r / (∑ i, μ i), ?_⟩
  change (∑ i, μ i * (r / (∑ j, μ j))) = r
  rw [← Finset.sum_mul]
  exact mul_div_cancel₀ r (ne_of_gt (ScalarGeometry.totalMass_pos hn μ hμ))

theorem scalarCenterLM_range_eq_top {n : ℕ} (hn : 0 < n) (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) : LinearMap.range (scalarCenterLM μ) = ⊤ :=
  LinearMap.range_eq_top.mpr (scalarCenterLM_surjective hn μ hμ)

/-- The empty-domain center functional is explicitly the zero map. -/
theorem scalarCenterLM_empty_eq_zero (μ : Fin 0 → ℝ) : scalarCenterLM μ = 0 := by
  ext z
  simp [scalarCenterLM]

theorem scalarCenterLM_empty_not_surjective (μ : Fin 0 → ℝ) :
    ¬ Function.Surjective (scalarCenterLM μ) := by
  intro h
  obtain ⟨z, hz⟩ := h 1
  rw [scalarCenterLM_empty_eq_zero] at hz
  exact zero_ne_one hz

theorem scalarCenterLM_surjective_iff {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) : Function.Surjective (scalarCenterLM μ) ↔ 0 < n := by
  constructor
  · intro h
    apply Nat.pos_of_ne_zero
    intro hn
    subst n
    exact scalarCenterLM_empty_not_surjective μ h
  · intro hn
    exact scalarCenterLM_surjective hn μ hμ

theorem scalarW_empty_eq_top (μ : Fin 0 → ℝ) : ScalarW μ = ⊤ := by
  rw [ScalarW, scalarCenterLM_empty_eq_zero, LinearMap.ker_zero]

theorem scalarW_empty_eq_zero (μ : Fin 0 → ℝ) (z : ScalarW μ) : z = 0 := by
  apply Subtype.ext
  funext i
  exact Fin.elim0 i

theorem scalarW_empty_finrank (μ : Fin 0 → ℝ) :
    Module.finrank ℝ (ScalarW μ) = 0 := by
  rw [scalarW_empty_eq_top, finrank_top]
  exact scalarConfiguration_finrank 0

/-- Rank-nullity, with the rank-one range proved from the original masses. -/
theorem scalarW_finrank_of_pos {n : ℕ} (hn : 0 < n) (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) : Module.finrank ℝ (ScalarW μ) = n - 1 := by
  have hdim := LinearMap.finrank_range_add_finrank_ker (scalarCenterLM μ)
  rw [scalarCenterLM_range_eq_top hn μ hμ, finrank_top,
    Module.finrank_self, scalarConfiguration_finrank] at hdim
  change Module.finrank ℝ (LinearMap.ker (scalarCenterLM μ)) = n - 1
  simpa only [Nat.add_sub_cancel_left] using
    congrArg (fun k : ℕ => k - 1) hdim

/-- The same formula covers both Fin 0 and Fin 1 with natural subtraction. -/
theorem scalarW_finrank {n : ℕ} (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i) :
    Module.finrank ℝ (ScalarW μ) = n - 1 := by
  by_cases hn : n = 0
  · subst n
    exact scalarW_empty_finrank μ
  · exact scalarW_finrank_of_pos (Nat.pos_of_ne_zero hn) μ hμ

theorem scalarW_singleton_finrank (μ : Fin 1 → ℝ) (hμ : ∀ i, 0 < μ i) :
    Module.finrank ℝ (ScalarW μ) = 0 :=
  scalarW_finrank μ hμ

/-- Here k is the number of actual ordered block positions. -/
theorem outerSpace_finrank {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) :
    Module.finrank ℝ (CoordinateProduct.OuterSpace m d) = d.blocks.length - 1 := by
  exact scalarW_finrank (datumBlockMass m d) (fun a => datumBlockMass_pos hm d a)

/-- Internal indices enumerate the actual list of labels in the block. -/
theorem innerSpace_finrank_length {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (a : BlockIndex d) :
    Module.finrank ℝ (CoordinateProduct.InnerSpace m d a) =
      (datumBlock d a).length - 1 := by
  exact scalarW_finrank (CoordinateProduct.internalMass m d a)
    (CoordinateProduct.internalMass_pos hm d a)

theorem datumBlockLabels_card_eq_length (d : OrderedClusterDatum) (a : BlockIndex d) :
    (datumBlockLabels d a).card = (datumBlock d a).length := by
  exact List.toFinset_card_of_nodup (d.block_nodup (datumBlock_mem d a))

/-- Thus the dimension is |B| - 1 for the genuine block label set. -/
theorem innerSpace_finrank_card {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (a : BlockIndex d) :
    Module.finrank ℝ (CoordinateProduct.InnerSpace m d a) =
      (datumBlockLabels d a).card - 1 := by
  rw [datumBlockLabels_card_eq_length]
  exact innerSpace_finrank_length hm d a

/-- The actual outer center functional has nonempty domain and full range. -/
theorem outerCenterLM_surjective {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) : Function.Surjective (scalarCenterLM (datumBlockMass m d)) := by
  have hn : 0 < d.blocks.length :=
    lt_of_le_of_lt (Nat.zero_le (blockOf d (0 : Label)).val) (blockOf d (0 : Label)).isLt
  exact scalarCenterLM_surjective hn (datumBlockMass m d)
    (fun a => datumBlockMass_pos hm d a)

/-- Every actual internal block is nonempty and uses the original masses. -/
theorem innerCenterLM_surjective {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (a : BlockIndex d) :
    Function.Surjective (scalarCenterLM (CoordinateProduct.internalMass m d a)) := by
  have hn : 0 < (datumBlock d a).length :=
    List.length_pos_iff.mpr (datumBlock_nonempty d a)
  exact scalarCenterLM_surjective hn (CoordinateProduct.internalMass m d a)
    (CoordinateProduct.internalMass_pos hm d a)

end FourBody.ScalarDimensions

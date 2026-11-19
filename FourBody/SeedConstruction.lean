import FourBody.CoordinateEquivalence
import FourBody.ScalarPotentialOriginalRoute

/-!
Actual seed existence and uniqueness for the literal ordered block datum.
Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
This is a static candidate awaiting the serial compilation window.
The unique roots are obtained from the proved centered minimization route;
neither seed existence nor a branch or classification certificate is assumed.
-/

noncomputable section
open scoped BigOperators
namespace FourBody

def internalLabelsEquivalence (d : OrderedClusterDatum) (a : BlockIndex d) :
    InternalIndex d a ≃ {i : Label // i ∈ datumBlock d a} :=
  d.blockLabelsEquiv (datumBlock d a) (List.get_mem d.blocks a)

theorem internalLabelsEquivalence_apply (d : OrderedClusterDatum)
    (a : BlockIndex d) (i : InternalIndex d a) :
    (internalLabelsEquivalence d a i).val = internalLabel d a i := rfl

theorem internalLabel_mem (d : OrderedClusterDatum) (a : BlockIndex d)
    (i : InternalIndex d a) : internalLabel d a i ∈ datumBlock d a :=
  (internalLabelsEquivalence d a i).property

theorem internalLabel_injective (d : OrderedClusterDatum) (a : BlockIndex d) :
    Function.Injective (internalLabel d a) := by
  intro i j hij
  apply (internalLabelsEquivalence d a).injective
  exact Subtype.ext hij

theorem internalLabel_surjective (d : OrderedClusterDatum) (a : BlockIndex d)
    {i : Label} (hi : i ∈ datumBlock d a) :
    ∃ j : InternalIndex d a, internalLabel d a j = i := by
  refine ⟨(internalLabelsEquivalence d a).symm ⟨i, hi⟩, ?_⟩
  exact congrArg Subtype.val ((internalLabelsEquivalence d a).apply_symm_apply ⟨i, hi⟩)

/-- Exact reindexing between the positions in the list and its label set. -/
theorem sum_internalLabels {A : Type*} [AddCommMonoid A]
    (d : OrderedClusterDatum) (a : BlockIndex d) (f : Label → A) :
    (∑ i : InternalIndex d a, f (internalLabel d a i)) =
      ∑ i ∈ datumBlockLabels d a, f i := by
  classical
  apply Finset.sum_bij (fun i _ => internalLabel d a i)
  · intro i _
    simpa only [datumBlockLabels, List.mem_toFinset] using internalLabel_mem d a i
  · intro i _ j _ hij
    exact internalLabel_injective d a hij
  · intro i hi
    have himem : i ∈ datumBlock d a := by simpa only [datumBlockLabels, List.mem_toFinset] using hi
    obtain ⟨j, hj⟩ := internalLabel_surjective d a himem
    exact ⟨j, Finset.mem_univ j, hj⟩
  · intro i _
    rfl

/-- Patching the actual internal solutions along the actual disjoint blocks.
The membership proof is used only to read the proved list equivalence. -/
def assembleInternal (d : OrderedClusterDatum)
    (u : ∀ a : BlockIndex d, InternalIndex d a → ℝ) (i : Label) : ℝ :=
  ∑ a : BlockIndex d, if hi : i ∈ datumBlock d a then
    u a ((internalLabelsEquivalence d a).symm ⟨i, hi⟩) else 0

theorem assembleInternal_apply (d : OrderedClusterDatum)
    (u : ∀ a : BlockIndex d, InternalIndex d a → ℝ)
    (a : BlockIndex d) (i : InternalIndex d a) :
    assembleInternal d u (internalLabel d a i) = u a i := by
  classical
  rw [assembleInternal, Finset.sum_eq_single a]
  · have hi := internalLabel_mem d a i
    rw [dif_pos hi]
    have hs : (⟨internalLabel d a i, hi⟩ : {j : Label // j ∈ datumBlock d a}) =
        internalLabelsEquivalence d a i := rfl
    rw [hs, Equiv.symm_apply_apply]
  · intro b _ hba
    have hn : internalLabel d a i ∉ datumBlock d b := by
      intro hb
      exact hba (datumBlock_index_unique d hb (internalLabel_mem d a i))
    exact dif_neg hn
  · intro ha
    exact False.elim (ha (Finset.mem_univ a))

theorem assembleInternal_weighted_center (m : Masses) (d : OrderedClusterDatum)
    (u : ∀ a : BlockIndex d, InternalIndex d a → ℝ)
    (hu : ∀ a, (∑ i : InternalIndex d a, m (internalLabel d a i) * u a i) = 0)
    (a : BlockIndex d) :
    (∑ i ∈ datumBlockLabels d a, m i * assembleInternal d u i) = 0 := by
  rw [← sum_internalLabels]
  simp_rw [assembleInternal_apply]
  exact hu a

/-- The root is a point of the real centered space produced by minimization. -/
def orderedScalarRoot {n : ℕ} (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i) :
    ScalarGeometry.ScalarW μ :=
  Classical.choose (ExistsUnique.exists
    (ScalarMinimizer.scalar_chamber_solution_existsUnique_hessian_route μ hμ))

theorem orderedScalarRoot_spec {n : ℕ} (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i) :
    StrictMono (orderedScalarRoot μ hμ).val ∧
      OneDimensionalSolution μ (orderedScalarRoot μ hμ).val := by
  have h := Classical.choose_spec (ExistsUnique.exists
    (ScalarMinimizer.scalar_chamber_solution_existsUnique_hessian_route μ hμ))
  refine ⟨h.1, ?_, ?_, ?_⟩
  · intro i j hij
    exact fun heq => hij (h.2.1 heq)
  · exact (orderedScalarRoot μ hμ).property
  · exact h.2.2

theorem orderedScalarRoot_unique {n : ℕ} (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i)
    (z : Fin n → ℝ) (hzorder : StrictMono z) (hz : OneDimensionalSolution μ z) :
    z = (orderedScalarRoot μ hμ).val := by
  let w : ScalarGeometry.ScalarW μ := ⟨z, hz.2.1⟩
  have hw : w ∈ ScalarGeometry.chamber μ ∧ ScalarGeometry.IsScalarSolution μ w.val :=
    ⟨hzorder, hzorder.injective, hz.2.2⟩
  have hroot := Classical.choose_spec (ExistsUnique.exists
    (ScalarMinimizer.scalar_chamber_solution_existsUnique_hessian_route μ hμ))
  have heq := ExistsUnique.unique
    (ScalarMinimizer.scalar_chamber_solution_existsUnique_hessian_route μ hμ) hw hroot
  exact congrArg Subtype.val heq

/-- The single-mass case is the actual zero point of the centered space. -/
theorem orderedScalarRoot_singleton_zero (μ : Fin 1 → ℝ) (hμ : ∀ i, 0 < μ i) :
    orderedScalarRoot μ hμ = 0 :=
  ScalarGeometry.singleton_center_eq_zero μ hμ _

/-- The auxiliary empty finite list is handled without a mass divisor. -/
theorem orderedScalarRoot_empty_zero (μ : Fin 0 → ℝ) (hμ : ∀ i, 0 < μ i) :
    orderedScalarRoot μ hμ = 0 := by
  apply Subtype.ext
  funext i
  exact Fin.elim0 i

def seedCoordinates {m : Masses} (hm : PositiveMasses m) (d : OrderedClusterDatum) :
    BlowupCoordinates m d := by
  let Y := orderedScalarRoot (datumBlockMass m d) (fun a => datumBlockMass_pos hm d a)
  let U : ∀ a : BlockIndex d, InternalIndex d a → ℝ := fun a =>
    (orderedScalarRoot (fun i => m (internalLabel d a i))
      (fun i => hm (internalLabel d a i))).val
  refine ⟨((0, Y.val), (assembleInternal d U, 0)), ?_⟩
  apply (mem_coordinateSpace_iff m d _).mpr
  refine ⟨?_, Y.property, ?_, ?_⟩
  · simp
  · intro a
    apply assembleInternal_weighted_center
    intro b
    exact (orderedScalarRoot (fun i => m (internalLabel d b i))
      (fun i => hm (internalLabel d b i))).property
  · intro a
    simp

theorem seedCoordinates_outerH {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (a : BlockIndex d) :
    outerH (seedCoordinates hm d) a = 0 := rfl

theorem seedCoordinates_outerY {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) :
    outerY (seedCoordinates hm d) =
      (orderedScalarRoot (datumBlockMass m d) (fun a => datumBlockMass_pos hm d a)).val := rfl

theorem seedCoordinates_innerU {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (a : BlockIndex d) (i : InternalIndex d a) :
    innerU (seedCoordinates hm d) (internalLabel d a i) =
      (orderedScalarRoot (fun j => m (internalLabel d a j))
        (fun j => hm (internalLabel d a j))).val i :=
  assembleInternal_apply d _ a i

theorem seedCoordinates_innerV {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (i : Label) :
    innerV (seedCoordinates hm d) i = 0 := rfl

theorem seedCoordinates_isSeed {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) : IsSeed m d (seedCoordinates hm d) := by
  have hY := orderedScalarRoot_spec (datumBlockMass m d) (fun a => datumBlockMass_pos hm d a)
  refine ⟨seedCoordinates_outerH hm d, seedCoordinates_innerV hm d, ?_, ?_, ?_⟩
  · rw [seedCoordinates_outerY]
    exact hY.1
  · rw [seedCoordinates_outerY]
    exact hY.2
  · intro a
    have hU := orderedScalarRoot_spec (fun i => m (internalLabel d a i))
      (fun i => hm (internalLabel d a i))
    have heq : (fun i : InternalIndex d a =>
        innerU (seedCoordinates hm d) (internalLabel d a i)) =
        (orderedScalarRoot (fun i => m (internalLabel d a i))
          (fun i => hm (internalLabel d a i))).val := by
      funext i
      exact seedCoordinates_innerU hm d a i
    rw [heq]
    exact hU

/-- Every actual ordered datum has exactly one actual constrained seed. -/
theorem seed_existsUnique {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) : ∃! h : BlowupCoordinates m d, IsSeed m d h := by
  refine ⟨seedCoordinates hm d, seedCoordinates_isSeed hm d, ?_⟩
  intro h hh
  have hY : outerY h = outerY (seedCoordinates hm d) := by
    rw [seedCoordinates_outerY]
    exact orderedScalarRoot_unique _ _ _ hh.2.2.1 hh.2.2.2.1
  have hU : innerU h = innerU (seedCoordinates hm d) := by
    funext i
    let a := blockOf d i
    obtain ⟨j, hj⟩ := internalLabel_surjective d a (label_mem_blockOf d i)
    have hua := hh.2.2.2.2 a
    have heq := orderedScalarRoot_unique (fun j => m (internalLabel d a j))
      (fun j => hm (internalLabel d a j))
      (fun j => innerU h (internalLabel d a j)) hua.1 hua.2
    rw [← hj]
    exact (congr_fun heq j).trans (seedCoordinates_innerU hm d a j).symm
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · funext a
      exact (hh.1 a).trans (seedCoordinates_outerH hm d a).symm
    · exact hY
  · apply Prod.ext
    · exact hU
    · funext i
      exact (hh.2.1 i).trans (seedCoordinates_innerV hm d i).symm

end FourBody

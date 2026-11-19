import FourBody.ClusterData
import FourBody.Geometry
import FourBody.BlowupPhysicalBridge
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

/-!
Literal source bridges, prepared independently of the classification proof.
Frozen v2 TeX: 97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

S5-B01/B04: the existing actual permutation/composition encoding is decoded:
a true cut is an interior cumulative block-length boundary, and the actual
number of ordered nonempty blocks equals the number of true cuts plus one.
S5-U23: the centered affine-line direction is normalized, retaining every
actual labeled coordinate and a nonzero parameter for a collision-free tuple.
S4-U03: physical distances in a common block scale by |ε| for every real ε.

STATIC CANDIDATE ONLY. This file has not been elaborated or audited.
No conclusion about branch existence, exhaustiveness, or counts is assumed.
-/

noncomputable section
open scoped BigOperators
namespace FourBody.SourceLiteralBridges

/-- The boundary between positions j and j+1, in zero-based coordinates. -/
def cutBoundaryEmbedding : Fin 3 ↪ Fin 5 where
  toFun j := ⟨1 + (j : ℕ), by omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    change 1 + (i : ℕ) = 1 + (j : ℕ) at h
    omega

/-- The actual interior cuts selected by the existing composition equivalence. -/
def interiorCuts (c : Composition 4) : Finset (Fin 3) :=
  compositionAsSetEquiv 4 (compositionEquiv 4 c)

theorem interiorCuts_mem_iff (c : Composition 4) (j : Fin 3) :
    j ∈ interiorCuts c ↔ cutBoundaryEmbedding j ∈ c.boundaries := by
  change j ∈ {i : Fin 3 |
    (⟨1 + (i : ℕ), by omega⟩ : Fin 5) ∈ c.boundaries}.toFinset ↔ _
  simp only [Set.mem_toFinset]
  rfl

theorem cut_true_iff_boundary (c : Composition 4) (j : Fin 3) :
    compositionCutsEquiv c j = true ↔
      cutBoundaryEmbedding j ∈ c.boundaries := by
  change decide (j ∈ interiorCuts c) = true ↔ _
  simp only [decide_eq_true_eq]
  exact interiorCuts_mem_iff c j

/-- Boundary semantics obtained from the actual proved inverse of the encoding. -/
theorem boundary_mem_iff_endpoints_or_cut (c : Composition 4) (x : Fin 5) :
    x ∈ c.boundaries ↔ x = 0 ∨ x = Fin.last 4 ∨
      ∃ j ∈ interiorCuts c, (x : ℕ) = (j : ℕ) + 1 := by
  have hboundaries : ((compositionAsSetEquiv 4).symm (interiorCuts c)).boundaries =
      c.boundaries :=
    congrArg (fun t : CompositionAsSet 4 => t.boundaries)
      ((compositionAsSetEquiv 4).symm_apply_apply c.toCompositionAsSet)
  rw [← hboundaries]
  simp only [compositionAsSetEquiv, Equiv.coe_fn_symm_mk, Set.mem_toFinset, Set.mem_ofPred_eq, exists_prop]

theorem boundaries_eq_insert_endpoints_map_cuts (c : Composition 4) :
    c.boundaries = insert 0 (insert (Fin.last 4)
      ((interiorCuts c).map cutBoundaryEmbedding)) := by
  ext x
  rw [boundary_mem_iff_endpoints_or_cut]
  simp only [Finset.mem_insert, Finset.mem_map]
  constructor
  · rintro (hzero | hlast | ⟨j, hj, hval⟩)
    · exact Or.inl hzero
    · exact Or.inr (Or.inl hlast)
    · refine Or.inr (Or.inr ⟨j, hj, ?_⟩)
      apply Fin.ext
      change 1 + (j : ℕ) = (x : ℕ)
      omega
  · rintro (hzero | hlast | ⟨j, hj, hpoint⟩)
    · exact Or.inl hzero
    · exact Or.inr (Or.inl hlast)
    · refine Or.inr (Or.inr ⟨j, hj, ?_⟩)
      have hval := congrArg Fin.val hpoint
      change 1 + (j : ℕ) = (x : ℕ) at hval
      omega

theorem zero_not_mem_mapped_cuts (c : Composition 4) :
    (0 : Fin 5) ∉ (interiorCuts c).map cutBoundaryEmbedding := by
  rintro h
  obtain ⟨j, _, hj⟩ := Finset.mem_map.mp h
  have h := congrArg Fin.val hj
  change 1 + (j : ℕ) = 0 at h
  omega

theorem last_not_mem_mapped_cuts (c : Composition 4) :
    Fin.last 4 ∉ (interiorCuts c).map cutBoundaryEmbedding := by
  rintro h
  obtain ⟨j, _, hj⟩ := Finset.mem_map.mp h
  have h := congrArg Fin.val hj
  change 1 + (j : ℕ) = 4 at h
  have hjlt := j.isLt
  omega

theorem boundary_card_eq_cut_card_add_two (c : Composition 4) :
    c.boundaries.card = (interiorCuts c).card + 2 := by
  rw [boundaries_eq_insert_endpoints_map_cuts]
  have hz : (0 : Fin 5) ∉ insert (Fin.last 4)
      ((interiorCuts c).map cutBoundaryEmbedding) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨by decide, zero_not_mem_mapped_cuts c⟩
  rw [Finset.card_insert_of_notMem hz,
    Finset.card_insert_of_notMem (last_not_mem_mapped_cuts c), Finset.card_map]

theorem true_cuts_eq_interiorCuts (c : Composition 4) :
    Finset.univ.filter (fun j : Fin 3 => compositionCutsEquiv c j = true) =
      interiorCuts c := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    cut_true_iff_boundary, interiorCuts_mem_iff]

theorem composition_length_eq_true_cut_card_add_one (c : Composition 4) :
    c.length =
      (Finset.univ.filter (fun j : Fin 3 => compositionCutsEquiv c j = true)).card + 1 := by
  rw [true_cuts_eq_interiorCuts]
  have h := c.card_boundaries_eq_succ_length
  rw [boundary_card_eq_cut_card_add_two] at h
  omega

/-- A true cut is precisely a proper cumulative block-size boundary. -/
theorem cut_true_iff_proper_partial_sum (c : Composition 4) (j : Fin 3) :
    compositionCutsEquiv c j = true ↔
      ∃ a : ℕ, 0 < a ∧ a < c.length ∧ c.sizeUpTo a = (j : ℕ) + 1 := by
  rw [cut_true_iff_boundary]
  constructor
  · intro hj
    obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hj
    have hval := congrArg Fin.val ha
    change c.sizeUpTo (a : ℕ) = 1 + (j : ℕ) at hval
    have ha0 : 0 < (a : ℕ) := by
      by_contra h
      have haz : (a : ℕ) = 0 := by omega
      rw [haz, c.sizeUpTo_zero] at hval
      omega
    have halt : (a : ℕ) < c.length := by
      have habound := a.isLt
      by_contra h
      have hae : (a : ℕ) = c.length := by omega
      rw [hae, c.sizeUpTo_length] at hval
      have hjlt := j.isLt
      omega
    refine ⟨a, ha0, halt, ?_⟩
    omega
  · rintro ⟨a, _, halt, ha⟩
    change cutBoundaryEmbedding j ∈ Finset.univ.map c.boundary.toEmbedding
    refine Finset.mem_map.mpr ⟨⟨a, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change c.sizeUpTo a = 1 + (j : ℕ)
    omega

/-- Literal block/cut semantics of the actual ordered datum, not a surrogate code. -/
theorem datum_cut_true_iff_block_boundary (d : OrderedClusterDatum) (j : Fin 3) :
    (datumEncoding d).2 j = true ↔
      ∃ a : ℕ, 0 < a ∧ a < d.blocks.length ∧
        ((d.blocks.map List.length).take a).sum = (j : ℕ) + 1 := by
  change compositionCutsEquiv d.composition j = true ↔ _
  simpa only [OrderedClusterDatum.composition, Composition.length,
    Composition.sizeUpTo, List.length_map] using
    cut_true_iff_proper_partial_sum d.composition j

theorem ordered_blocks_length_eq_true_cut_card_add_one (d : OrderedClusterDatum) :
    d.blocks.length =
      (Finset.univ.filter (fun j : Fin 3 => (datumEncoding d).2 j = true)).card + 1 := by
  change d.blockCount = _
  rw [← d.composition_length]
  change d.composition.length =
    (Finset.univ.filter (fun j : Fin 3 => compositionCutsEquiv d.composition j = true)).card + 1
  exact composition_length_eq_true_cut_card_add_one d.composition

theorem decoded_blocks_length_eq_true_cut_card_add_one
    (p : Equiv.Perm Label × (Fin 3 → Bool)) :
    (datumEncoding.symm p).blocks.length =
      (Finset.univ.filter (fun j : Fin 3 => p.2 j = true)).card + 1 := by
  simpa only [encode_decode] using
    ordered_blocks_length_eq_true_cut_card_add_one (datumEncoding.symm p)

/-- Normalize the actual centered line, retaining the same labeled coordinates. -/
theorem centered_collinear_unit_direction {m : Masses} (hm : PositiveMasses m)
    {q : Configuration} (hc : centerLM m q = 0) (hcol : Collinear q) :
    ∃ e : Point, ‖e‖ = 1 ∧ ∃ t : Label → ℝ, ∀ i, q i = t i • e := by
  obtain ⟨e, he, t, ht⟩ := collinear_centered_through_origin hm hc hcol
  have hn : 0 < ‖e‖ := norm_pos_iff.mpr he
  have hn0 : ‖e‖ ≠ 0 := ne_of_gt hn
  refine ⟨‖e‖⁻¹ • e, ?_, fun i => t i * ‖e‖, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
      inv_mul_cancel₀ hn0]
  · intro i
    rw [ht i, smul_smul]
    congr 1
    rw [mul_assoc, mul_inv_cancel₀ hn0, mul_one]

/-- Collision freedom supplies an actual nonzero line parameter after normalization. -/
theorem centered_collinear_collisionFree_unit_direction {m : Masses}
    (hm : PositiveMasses m) {q : Configuration} (hc : centerLM m q = 0)
    (hcol : Collinear q) (hcf : CollisionFree q) :
    ∃ e : Point, ‖e‖ = 1 ∧ ∃ t : Label → ℝ,
      (∀ i, q i = t i • e) ∧ ∃ i, t i ≠ 0 := by
  obtain ⟨e, he, t, ht⟩ := centered_collinear_unit_direction hm hc hcol
  refine ⟨e, he, t, ht, ?_⟩
  by_contra h
  push Not at h
  have h01 : q (0 : Label) = q (1 : Label) := by simp [ht, h]
  exact hcf 0 1 (by decide) h01

/-- The manuscript's unit direction for every actual collinear positive-s solution. -/
theorem collinear_solution_unit_direction {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : IsSolution m s q)
    (hcol : Collinear q) :
    ∃ e : Point, ‖e‖ = 1 ∧ ∃ t : Label → ℝ,
      (∀ i, q i = t i • e) ∧ ∃ i, t i ≠ 0 :=
  centered_collinear_collisionFree_unit_direction hm
    (solution_center_zero m hs hq) hcol hq.1

/-- Signed/zero ε are included: the exact scaling factor is the real absolute value. -/
theorem same_block_distance_abs_epsilon {m : Masses} {d : OrderedClusterDatum}
    (ε : ℝ) (h : BlowupCoordinates m d) (i j : Label)
    (hblock : blockOf d i = blockOf d j) :
    dist (physicalCoordinates ε h i) (physicalCoordinates ε h j) =
      |ε| * internalRho h i j := by
  rw [dist_eq_norm, physicalCoordinates_difference_sameBlock ε h i j hblock,
    norm_smul, Real.norm_eq_abs]
  rfl

theorem same_block_distance_positive_epsilon {m : Masses} {d : OrderedClusterDatum}
    {ε : ℝ} (hε : 0 < ε) (h : BlowupCoordinates m d) (i j : Label)
    (hblock : blockOf d i = blockOf d j) :
    dist (physicalCoordinates ε h i) (physicalCoordinates ε h j) =
      ε * internalRho h i j := by
  rw [same_block_distance_abs_epsilon ε h i j hblock, abs_of_pos hε]

end FourBody.SourceLiteralBridges


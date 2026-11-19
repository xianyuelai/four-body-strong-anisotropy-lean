import FourBody.SeedConstruction
import FourBody.InternalCoordinates
import FourBody.InternalEquationLimits
import FourBody.SequenceBlockIndices
import FourBody.VerticalPairing
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option warningAsError true

/-!
STATIC source-literal supplements for v2 S3-U19/U35/U38/U41.
Frozen original v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

The one-block facts concern the actual weighted mean and actual constrained
coordinate kernel. Canonical singleton values transfer the checked Fin 1
ordered-root zero theorem to the real datum's dependent index lengths.
The unordered vertical energy is derived directly from actual individual
limit equations, before any vertical-zero conclusion is used.

No Lean/Lake/checker run has validated this candidate. It is outside the
formal project and introduces no axiom, certificate or target hypothesis.
-/

noncomputable section
open scoped BigOperators
namespace FourBody.SequenceExtremeLiteralSupplement

theorem one_block_index_eq (d : OrderedClusterDatum)
    (hsize : d.blocks.length = 1) (a b : BlockIndex d) : a = b := by
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  omega

theorem one_block_sum_eq (d : OrderedClusterDatum)
    (hsize : d.blocks.length = 1) (f : BlockIndex d → ℝ) (a : BlockIndex d) :
    (∑ b, f b) = f a := by
  classical
  apply Finset.sum_eq_single a
  · intro b _hb hba
    exact (hba (one_block_index_eq d hsize b a)).elim
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

/-- Any actual centered outer scalar tuple, including H and Y, is zero. -/
theorem one_block_centered_scalar_zero {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (hsize : d.blocks.length = 1)
    (z : BlockIndex d → ℝ) (hc : (∑ b, datumBlockMass m d b * z b) = 0)
    (a : BlockIndex d) : z a = 0 := by
  have h := (one_block_sum_eq d hsize (fun b => datumBlockMass m d b * z b) a).symm.trans hc
  exact (mul_eq_zero.mp h).resolve_left (datumBlockMass_ne_zero hm d a)

/-- Source H and Y vanish identically for one block, for every coordinate point. -/
theorem one_block_outer_coordinates_zero {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (hsize : d.blocks.length = 1)
    (h : BlowupCoordinates m d) (a : BlockIndex d) :
    outerH h a = 0 ∧ outerY h a = 0 := by
  have hc := coordinate_constraints h
  exact ⟨one_block_centered_scalar_zero hm d hsize (outerH h) hc.1 a,
    one_block_centered_scalar_zero hm d hsize (outerY h) hc.2.1 a⟩

/-- The physical mass mean is the zero Point before dividing by epsilon. -/
theorem one_block_physical_mean_zero {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (hsize : d.blocks.length = 1)
    (q : Configuration) (hcenter : centerLM m q = 0) (a : BlockIndex d) :
    datumBlockMean m d q a = 0 := by
  ext k
  have hsum := sum_block_mass_means hm d q k
  rw [one_block_sum_eq d hsize
    (fun b => datumBlockMass m d b * datumBlockMean m d q b k) a] at hsum
  have hc := center_coordinate_zero hcenter k
  have hmul : datumBlockMass m d a * datumBlockMean m d q a k = 0 := hsum.trans hc
  exact (mul_eq_zero.mp hmul).resolve_left (datumBlockMass_ne_zero hm d a)

/-- H=c_x/epsilon and Y=c_y are exactly zero, including totalized epsilon=0. -/
theorem one_block_physical_center_coordinates_zero {m : Masses}
    (hm : PositiveMasses m) (d : OrderedClusterDatum) (hsize : d.blocks.length = 1)
    (ε : ℝ) (q : Configuration) (hcenter : centerLM m q = 0) (a : BlockIndex d) :
    horizontalCenterCoordinate m d ε q a = 0 ∧
      verticalCenterCoordinate m d q a = 0 := by
  have hmean := one_block_physical_mean_zero hm d hsize q hcenter a
  constructor
  · simp only [horizontalCenterCoordinate, hmean, PiLp.zero_apply, zero_div]
  · simp only [verticalCenterCoordinate, hmean, PiLp.zero_apply]

/-- Actual original positive-s solutions have these zero physical centers. -/
theorem one_block_solution_center_coordinates_zero {m : Masses}
    (hm : PositiveMasses m) (d : OrderedClusterDatum) (hsize : d.blocks.length = 1)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : IsSolution m s q)
    (a : BlockIndex d) :
    horizontalCenterCoordinate m d (epsilon s) q a = 0 ∧
      verticalCenterCoordinate m d q a = 0 :=
  one_block_physical_center_coordinates_zero hm d hsize (epsilon s) q
    (solution_center_zero m hs hq) a

/-- Exact dependent-size transfer of the checked Fin 1 canonical-root theorem. -/
theorem ordered_root_size_one_zero {n : ℕ} (hn : n = 1) (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (i : Fin n) : (orderedScalarRoot μ hμ).val i = 0 := by
  subst n
  have h := congrArg (fun z : ScalarGeometry.ScalarW μ => z.val i)
    (orderedScalarRoot_singleton_zero μ hμ)
  change (orderedScalarRoot μ hμ).val i = 0 at h
  exact h

/-- The outer canonical seed is the same actual zero singleton root. -/
theorem one_block_canonical_outer_seed_zero {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (hsize : d.blocks.length = 1) (a : BlockIndex d) :
    outerY (seedCoordinates hm d) a = 0 := by
  rw [seedCoordinates_outerY]
  exact ordered_root_size_one_zero hsize (datumBlockMass m d)
    (fun b => datumBlockMass_pos hm d b) a

/-- The singleton internal seed uses its own actual original mass and label. -/
theorem singleton_canonical_internal_seed_zero {m : Masses}
    (hm : PositiveMasses m) (d : OrderedClusterDatum) (a : BlockIndex d)
    (i : Label) (hblock : datumBlock d a = [i]) :
    innerU (seedCoordinates hm d) i = 0 ∧ innerV (seedCoordinates hm d) i = 0 := by
  have hi : i ∈ datumBlock d a := by simp only [hblock, List.mem_singleton]
  obtain ⟨j, hj⟩ := internalLabel_surjective d a hi
  have hsize : (datumBlock d a).length = 1 := by simp only [hblock, List.length_singleton]
  constructor
  · rw [← hj, seedCoordinates_innerU]
    exact ordered_root_size_one_zero hsize (fun k => m (internalLabel d a k))
      (fun k => hm (internalLabel d a k)) j
  · exact seedCoordinates_innerV hm d i

/-- The same singleton centered constraints force actual U and V to vanish. -/
theorem singleton_internal_coordinates_zero {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (h : BlowupCoordinates m d) (a : BlockIndex d)
    (i : Label) (hblock : datumBlock d a = [i]) : innerU h i = 0 ∧ innerV h i = 0 := by
  classical
  have hlabels : datumBlockLabels d a = {i} := by simp [datumBlockLabels, hblock]
  have hc := coordinate_constraints h
  have hu : m i * innerU h i = 0 := by simpa only [hlabels, Finset.sum_singleton] using hc.2.2.1 a
  have hv : m i * innerV h i = 0 := by simpa only [hlabels, Finset.sum_singleton] using hc.2.2.2 a
  exact ⟨(mul_eq_zero.mp hu).resolve_left (ne_of_gt (hm i)),
    (mul_eq_zero.mp hv).resolve_left (ne_of_gt (hm i))⟩

/-- Four nonempty blocks covering the four original labels have length one.
The actual composition theorem derives this; no singleton certificate is input. -/
theorem four_block_length_one (d : OrderedClusterDatum)
    (hsize : d.blocks.length = 4) (a : BlockIndex d) :
    (datumBlock d a).length = 1 := by
  have hc : d.composition = Composition.ones 4 :=
    Composition.eq_ones_iff_length.mpr
      (by simpa only [OrderedClusterDatum.composition_length,
        OrderedClusterDatum.blockCount] using hsize)
  have hm : (datumBlock d a).length ∈ d.composition.blocks := by
    change (datumBlock d a).length ∈ d.blocks.map List.length
    exact List.mem_map.mpr ⟨datumBlock d a, List.get_mem d.blocks a, rfl⟩
  exact (Composition.eq_ones_iff.mp hc) _ hm

/-- The singleton list contains its actual label in its original order. -/
theorem four_blocks_are_singletons (d : OrderedClusterDatum)
    (hsize : d.blocks.length = 4) (a : BlockIndex d) :
    ∃ i : Label, datumBlock d a = [i] := by
  have hlen := four_block_length_one d hsize a
  cases hblock : datumBlock d a with
  | nil =>
      simp only [hblock, List.length_nil] at hlen
      omega
  | cons i l =>
      have hl : l = [] := by
        cases l with
        | nil => rfl
        | cons j t =>
            simp only [hblock, List.length_cons] at hlen
            omega
      exact ⟨i, by simp only [hl]⟩

/-- All original inner coordinates vanish for the four-block extreme. -/
theorem four_block_inner_coordinates_zero {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (hsize : d.blocks.length = 4)
    (h : BlowupCoordinates m d) :
    ∀ i : Label, innerU h i = 0 ∧ innerV h i = 0 := by
  intro i
  obtain ⟨j, hj⟩ := four_blocks_are_singletons d hsize (blockOf d i)
  have hij : i = j := by
    simpa only [hj, List.mem_singleton] using label_mem_blockOf d i
  rw [hij]
  exact singleton_internal_coordinates_zero hm d h (blockOf d i) j hj

/-- The four-block canonical seed has these same actual zero inner values. -/
theorem four_block_canonical_inner_seed_zero {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (hsize : d.blocks.length = 4) :
    ∀ i : Label, innerU (seedCoordinates hm d) i = 0 ∧
      innerV (seedCoordinates hm d) i = 0 :=
  four_block_inner_coordinates_zero hm d hsize (seedCoordinates hm d)

/-- All physical P vectors are exactly zero in the four-block extreme. -/
theorem four_block_physical_internal_vectors_zero {m : Masses}
    (hm : PositiveMasses m) (d : OrderedClusterDatum) (hsize : d.blocks.length = 4)
    (ε : ℝ) (q : Configuration) :
    ∀ i : Label, internalVectorCoordinate m d ε q (blockOf d i) i = 0 := by
  intro i
  obtain ⟨j, hj⟩ := four_blocks_are_singletons d hsize (blockOf d i)
  have hij : i = j := by
    simpa only [hj, List.mem_singleton] using label_mem_blockOf d i
  have hblock : datumBlock d (blockOf d i) = [i] := by
    simpa only [← hij] using hj
  exact InternalCoordinates.internalVector_eq_zero_of_singleton hm d ε q
    (blockOf d i) i hblock

/-- The literal one-pair coefficient, derived before using v=0.
InternalIndex enumerates exactly the original labels of this actual block. -/
theorem internal_limit_indexed_vertical_energy_zero {m : Masses}
    {y : Label → ℝ} {P₀ : Configuration}
    (heq : InternalEquationLimits.InternalEquationAtLimit m y P₀)
    (a : BlockIndex (VerticalPartition.verticalPartitionDatum y)) :
    (∑ p ∈ VerticalEnergy.orderedPairs
        ((datumBlock (VerticalPartition.verticalPartitionDatum y) a).length),
      m (internalLabel (VerticalPartition.verticalPartitionDatum y) a p.1) *
        m (internalLabel (VerticalPartition.verticalPartitionDatum y) a p.2) *
        (P₀ (internalLabel (VerticalPartition.verticalPartitionDatum y) a p.1) 1 -
          P₀ (internalLabel (VerticalPartition.verticalPartitionDatum y) a p.2) 1) ^ 2 /
        dist (P₀ (internalLabel (VerticalPartition.verticalPartitionDatum y) a p.1))
          (P₀ (internalLabel (VerticalPartition.verticalPartitionDatum y) a p.2)) ^ 3) = 0 := by
  refine VerticalEnergy.distance_energy_eq_zero_of_vertical_force_zero
    (fun j : InternalIndex (VerticalPartition.verticalPartitionDatum y) a =>
      m (internalLabel (VerticalPartition.verticalPartitionDatum y) a j))
    (fun j : InternalIndex (VerticalPartition.verticalPartitionDatum y) a =>
      P₀ (internalLabel (VerticalPartition.verticalPartitionDatum y) a j))
    (fun j : InternalIndex (VerticalPartition.verticalPartitionDatum y) a =>
      P₀ (internalLabel (VerticalPartition.verticalPartitionDatum y) a j) 1) ?_
  intro j
  rw [SequenceBlockIndices.verticalForce_eq_actual_internal_field m _ P₀ a j]
  exact (heq (internalLabel (VerticalPartition.verticalPartitionDatum y) a j)).2

/-- All selected physical mean-coordinate points have the same exact zeros. -/
theorem one_block_selected_outer_zero {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (hsize : d.blocks.length = 1)
    (h : ℕ → BlowupCoordinates m d) :
    ∀ (ν : ℕ) (a : BlockIndex d), outerH (h ν) a = 0 ∧ outerY (h ν) a = 0 := by
  intro ν a
  exact one_block_outer_coordinates_zero hm d hsize (h ν) a

end FourBody.SequenceExtremeLiteralSupplement

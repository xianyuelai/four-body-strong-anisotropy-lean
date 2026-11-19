import FourBody.RecoveryBounds
import Mathlib.Data.List.Sort
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-!
# Unique reconstruction of the literal ordered datum

Frozen manuscript SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
Source Section 5, lines 692--699: recover blocks by distance, outer order
by vertical separation, and internal order by x_j-x_i = epsilon(u_j-u_i).

STATIC CANDIDATE, uncompiled. The final equality is proved for the actual
list-of-nonempty-lists OrderedClusterDatum. Configurations are the actual
four labeled Euclidean points, and equality is literal tuple equality.
No permutation, reflection, rotation, or dilation is identified.

The finite-list argument first matches member sets by block equivalence,
then matches each internally q-x-sorted list, and finally matches the
outer lists by their actual mass-mean-height key. Neither datum equality
nor the whole source recovery conclusion is an input hypothesis.
-/

noncomputable section
open scoped BigOperators
namespace FourBody

/-- Ordering properties read directly from physical block means and points. -/
structure OrderedByConfiguration (m : Masses) (q : Configuration)
    (d : OrderedClusterDatum) : Prop where
  block_height_order : StrictMono (fun a : BlockIndex d => datumBlockMean m d q a 1)
  internal_x_order : ∀ a : BlockIndex d,
    StrictMono (fun i : InternalIndex d a => q (internalLabel d a i) 0)

/-- The unordered labelled partition relation; no order or recovery theorem
is included. This is the component which the physical distance cut proves. -/
def BlockPartitionEquivalent (d e : OrderedClusterDatum) : Prop :=
  ∀ i j : Label, blockOf d i = blockOf d j ↔ blockOf e i = blockOf e j

/-- Strict real-key sorting identifies a finite list from its members.
Global injectivity of the key is unnecessary: the two opposite strict
inequalities are already inconsistent. -/
theorem list_eq_of_pairwise_real_key {α : Type*} (key : α → ℝ)
    {l r : List α} (hl : l.Pairwise (fun a b => key a < key b))
    (hr : r.Pairwise (fun a b => key a < key b))
    (hmem : ∀ a : α, a ∈ l ↔ a ∈ r) : l = r := by
  let : Std.Antisymm (fun a b : α => key a < key b) :=
    ⟨fun _ _ hab hba => (lt_asymm hab hba).elim⟩
  let : Std.Irrefl (fun a b : α => key a < key b) :=
    ⟨fun a => lt_irrefl (key a)⟩
  exact hl.eq_of_mem_iff hr hmem

theorem datum_block_pairwise_physical_x {m : Masses} {q : Configuration}
    {d : OrderedClusterDatum} (hd : OrderedByConfiguration m q d)
    (a : BlockIndex d) :
    (datumBlock d a).Pairwise (fun i j => q i 0 < q j 0) := by
  apply List.pairwise_iff_get.mpr
  intro i j hij
  exact hd.internal_x_order a hij

/-- A list's physical mass-mean height is independent of its internal order. -/
def listBarycenterHeight (m : Masses) (q : Configuration) (B : List Label) : ℝ :=
  (∑ i ∈ B.toFinset, m i)⁻¹ * (∑ i ∈ B.toFinset, m i * q i 1)

theorem listBarycenterHeight_datumBlock (m : Masses) (d : OrderedClusterDatum)
    (q : Configuration) (a : BlockIndex d) :
    listBarycenterHeight m q (datumBlock d a) = datumBlockMean m d q a 1 := by
  rw [datumBlockMean_apply]
  rfl

theorem datum_blocks_pairwise_physical_height {m : Masses} {q : Configuration}
    {d : OrderedClusterDatum} (hd : OrderedByConfiguration m q d) :
    d.blocks.Pairwise (fun B C => listBarycenterHeight m q B < listBarycenterHeight m q C) := by
  apply List.pairwise_iff_get.mpr
  intro a b hab
  change listBarycenterHeight m q (datumBlock d a) <
    listBarycenterHeight m q (datumBlock d b)
  rw [listBarycenterHeight_datumBlock, listBarycenterHeight_datumBlock]
  exact hd.block_height_order hab

/-- Unordered partition equivalence matches ACTUAL internally ordered lists
once both lists are sorted by the same physical horizontal coordinate. -/
theorem datum_block_matches_of_partition_equivalent {m : Masses} {q : Configuration}
    {d e : OrderedClusterDatum} (hd : OrderedByConfiguration m q d)
    (he : OrderedByConfiguration m q e) (hp : BlockPartitionEquivalent d e)
    (a : BlockIndex d) : ∃ b : BlockIndex e, datumBlock d a = datumBlock e b := by
  obtain ⟨i, hi⟩ := datumBlockLabels_nonempty d a
  have himem : i ∈ datumBlock d a := by simpa [datumBlockLabels] using hi
  have hdi : blockOf d i = a := blockOf_eq_of_mem d himem
  let b : BlockIndex e := blockOf e i
  refine ⟨b, list_eq_of_pairwise_real_key (fun j : Label => q j 0)
    (datum_block_pairwise_physical_x hd a) (datum_block_pairwise_physical_x he b) ?_⟩
  intro j
  constructor
  · intro hj
    have hdji : blockOf d j = blockOf d i := (blockOf_eq_of_mem d hj).trans hdi.symm
    have heji : blockOf e j = blockOf e i := (hp j i).mp hdji
    exact (mem_datumBlock_iff e j b).mpr heji
  · intro hj
    have heji : blockOf e j = blockOf e i := blockOf_eq_of_mem e hj
    have hdji : blockOf d j = blockOf d i := (hp j i).mpr heji
    exact (mem_datumBlock_iff d j a).mpr (hdji.trans hdi)

/-- The requested datum equality from only block equivalence, strict actual
barycenter order, and strict actual within-block horizontal order. -/
theorem orderedDatum_eq_of_partition_and_physical_orders {m : Masses}
    {q : Configuration} {d e : OrderedClusterDatum}
    (hp : BlockPartitionEquivalent d e) (hd : OrderedByConfiguration m q d)
    (he : OrderedByConfiguration m q e) : d = e := by
  apply OrderedClusterDatum.ext
  apply list_eq_of_pairwise_real_key (listBarycenterHeight m q)
    (datum_blocks_pairwise_physical_height hd) (datum_blocks_pairwise_physical_height he)
  intro B
  constructor
  · intro hB
    obtain ⟨a, ha⟩ := List.exists_mem_iff_get.mp
      (show ∃ C ∈ d.blocks, C = B from ⟨B, hB, rfl⟩)
    obtain ⟨b, hab⟩ := datum_block_matches_of_partition_equivalent hd he hp a
    have hBe : B = datumBlock e b := ha.symm.trans hab
    rw [hBe]
    exact datumBlock_mem e b
  · intro hB
    obtain ⟨b, hb⟩ := List.exists_mem_iff_get.mp
      (show ∃ C ∈ e.blocks, C = B from ⟨B, hB, rfl⟩)
    have hp' : BlockPartitionEquivalent e d := fun i j => (hp i j).symm
    obtain ⟨a, hba⟩ := datum_block_matches_of_partition_equivalent he hd hp' b
    have hBd : B = datumBlock d a := hb.symm.trans hba
    rw [hBd]
    exact datumBlock_mem d a

theorem partition_equivalent_of_common_distance_cut {d e : OrderedClusterDatum}
    {q : Configuration} {cut : ℝ} (hd : DistanceRecoversBlocks d q cut)
    (he : DistanceRecoversBlocks e q cut) : BlockPartitionEquivalent d e :=
  fun i j => (hd i j).symm.trans (he i j)

/-- A finite, concrete compatibility test on the actual data and physical q. -/
def CompatibleRecoveryDatum (m : Masses) (q : Configuration) (cut : ℝ)
    (d : OrderedClusterDatum) : Prop :=
  DistanceRecoversBlocks d q cut ∧ OrderedByConfiguration m q d

theorem compatibleRecoveryDatum_unique {m : Masses} {q : Configuration} {cut : ℝ}
    {d e : OrderedClusterDatum} (hd : CompatibleRecoveryDatum m q cut d)
    (he : CompatibleRecoveryDatum m q cut e) : d = e :=
  orderedDatum_eq_of_partition_and_physical_orders
    (partition_equivalent_of_common_distance_cut hd.1 he.1) hd.2 he.2

/-- Search over the already derived genuine finite type, rather than over a
surrogate 192-element certificate type. Real comparison is classical. -/
def recoveryDatumCandidates (m : Masses) (q : Configuration) (cut : ℝ) :
    Finset OrderedClusterDatum := by
  classical
  exact Finset.univ.filter (CompatibleRecoveryDatum m q cut)

theorem recoveryDatumCandidates_eq_singleton {m : Masses} {q : Configuration}
    {cut : ℝ} {d : OrderedClusterDatum} (hd : CompatibleRecoveryDatum m q cut d) :
    recoveryDatumCandidates m q cut = {d} := by
  classical
  ext e
  simp only [recoveryDatumCandidates, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro he
    exact compatibleRecoveryDatum_unique he hd
  · rintro rfl
    exact hd

/-- Choice is taken only after compatibility is witnessed; uniqueness is a
proved theorem above, not a field of the witness or an imported axiom. -/
def recoveredDatum (m : Masses) (q : Configuration) (cut : ℝ)
    (hex : ∃ d : OrderedClusterDatum, CompatibleRecoveryDatum m q cut d) :
    OrderedClusterDatum := Classical.choose hex

theorem recoveredDatum_eq {m : Masses} {q : Configuration} {cut : ℝ}
    (hex : ∃ d : OrderedClusterDatum, CompatibleRecoveryDatum m q cut d)
    {d : OrderedClusterDatum} (hd : CompatibleRecoveryDatum m q cut d) :
    recoveredDatum m q cut hex = d :=
  compatibleRecoveryDatum_unique (Classical.choose_spec hex) hd

/-- Geometry yields the full concrete compatibility predicate. The required
rectangle inputs are explicit and must later come from IFT continuity. -/
theorem recovery_compatible_of_rectangle {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {γ A ε : ℝ} {h : BlowupCoordinates m d}
    {q : Configuration} (hγ : 0 < γ) (hA : 1 ≤ A) (hε : 0 < ε)
    (hs : RecoverySmall γ A ε) (hr : RecoveryRectangle m d γ A h)
    (hq : RepresentsCoordinates m d ε h q) :
    CompatibleRecoveryDatum m q (recoveryCut γ) d := by
  refine ⟨distance_recovers_blocks hγ hA hε.le hs hr hq, ?_⟩
  exact ⟨recovery_barycenter_heights_strictMono hm hγ hr hq,
    recovery_internal_horizontal_strictMono hε hr hq⟩

/-- The actual Section 5 local recovery statement, including a concrete
finite reconstruction set and uniqueness on literal labelled q. It makes
no claim of analytic branches or global exhaustiveness. -/
theorem recovery_candidates_of_actual_coordinates {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {γ A ε : ℝ} {h : BlowupCoordinates m d}
    {q : Configuration} (hγ : 0 < γ) (hA : 1 ≤ A) (hε : 0 < ε)
    (hs : RecoverySmall γ A ε) (hr : RecoveryRectangle m d γ A h)
    (hq : RepresentsCoordinates m d ε h q) :
    recoveryDatumCandidates m q (recoveryCut γ) = {d} ∧
      ∃! e : OrderedClusterDatum, CompatibleRecoveryDatum m q (recoveryCut γ) e := by
  have hd := recovery_compatible_of_rectangle hm hγ hA hε hs hr hq
  refine ⟨recoveryDatumCandidates_eq_singleton hd, d, hd, ?_⟩
  intro e he
  exact compatibleRecoveryDatum_unique he hd

/-- No two distinct literal data in the shortened coordinate rectangles
can reconstruct the same literal physical four-tuple. -/
theorem actual_coordinates_determine_datum {m : Masses} (hm : PositiveMasses m)
    {d e : OrderedClusterDatum} {γ A ε : ℝ}
    {h : BlowupCoordinates m d} {g : BlowupCoordinates m e} {q : Configuration}
    (hγ : 0 < γ) (hA : 1 ≤ A) (hε : 0 < ε) (hs : RecoverySmall γ A ε)
    (hd : RecoveryRectangle m d γ A h) (he : RecoveryRectangle m e γ A g)
    (hq : RepresentsCoordinates m d ε h q) (gq : RepresentsCoordinates m e ε g q) : d = e :=
  compatibleRecoveryDatum_unique
    (recovery_compatible_of_rectangle hm hγ hA hε hs hd hq)
    (recovery_compatible_of_rectangle hm hγ hA hε hs he gq)

/-- The final local injectivity implication uses the actual common gamma,
actual finite seed-based A, and an explicit positive common epsilon bound. -/
theorem actual_common_constants_determine_datum {m : Masses} (hm : PositiveMasses m)
    {d e : OrderedClusterDatum} {ε : ℝ}
    {h : BlowupCoordinates m d} {g : BlowupCoordinates m e}
    (hε : 0 < ε)
    (hεlt : ε < recoveryParameterBound (commonSeedGap hm) (commonSeedInnerBound hm))
    (hd : RecoveryRectangle m d (commonSeedGap hm) (commonSeedInnerBound hm) h)
    (he : RecoveryRectangle m e (commonSeedGap hm) (commonSeedInnerBound hm) g)
    (hq : physicalCoordinates ε h = physicalCoordinates ε g) : d = e := by
  apply actual_coordinates_determine_datum hm (commonSeedGap_positive hm)
    (commonSeedInnerBound_ge_one hm) hε
    (recoverySmall_of_lt_bound (commonSeedGap_positive hm) (commonSeedInnerBound_ge_one hm) hεlt)
    hd he (represents_physicalCoordinates ε h)
  rw [hq]
  exact represents_physicalCoordinates ε g

/-- The same statement for the manuscript's actual linear map Q_epsilon
into W; equality is equality of literal labelled points in that subspace. -/
theorem coordinateQ_common_constants_determine_datum {m : Masses} (hm : PositiveMasses m)
    {d e : OrderedClusterDatum} {ε : ℝ}
    {h : BlowupCoordinates m d} {g : BlowupCoordinates m e}
    (hε : 0 < ε)
    (hεlt : ε < recoveryParameterBound (commonSeedGap hm) (commonSeedInnerBound hm))
    (hd : RecoveryRectangle m d (commonSeedGap hm) (commonSeedInnerBound hm) h)
    (he : RecoveryRectangle m e (commonSeedGap hm) (commonSeedInnerBound hm) g)
    (hq : coordinateQ m d ε h = coordinateQ m e ε g) : d = e :=
  actual_common_constants_determine_datum hm hε hεlt hd he (congrArg Subtype.val hq)
/-- A raw-seed-comparison version of the literal Q_epsilon injectivity
implication. Even preservation of internal signs is derived, not assumed. -/
theorem coordinateQ_seed_comparisons_determine_datum {m : Masses} (hm : PositiveMasses m)
    {d e : OrderedClusterDatum} {ε : ℝ}
    {h : BlowupCoordinates m d} {g : BlowupCoordinates m e}
    (hε : 0 < ε)
    (hεlt : ε < recoveryParameterBound (commonSeedGap hm) (commonSeedInnerBound hm))
    (hd : SeedComparisonBounds hm d h) (he : SeedComparisonBounds hm e g)
    (hq : coordinateQ m d ε h = coordinateQ m e ε g) : d = e :=
  coordinateQ_common_constants_determine_datum hm hε hεlt
    (recoveryRectangle_of_seedComparisons hm hd)
    (recoveryRectangle_of_seedComparisons hm he) hq
/-- A singleton's centered internal coordinates are zero, for arbitrary
constrained coordinates; no inner force or branch certificate is assumed. -/
theorem singleton_internal_coordinates_zero {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (h : BlowupCoordinates m d)
    (a : BlockIndex d) (i : Label) (hb : datumBlock d a = [i]) :
    innerU h i = 0 ∧ innerV h i = 0 := by
  have hu : m i * innerU h i = 0 := by
    simpa [datumBlockLabels, hb] using (coordinate_constraints h).2.2.1 a
  have hv : m i * innerV h i = 0 := by
    simpa [datumBlockLabels, hb] using (coordinate_constraints h).2.2.2 a
  exact ⟨(mul_eq_zero.mp hu).resolve_left (ne_of_gt (hm i)),
    (mul_eq_zero.mp hv).resolve_left (ne_of_gt (hm i))⟩

/-- The outer centered coordinate factors are really zero when k=1.
No division by a nonexistent outer gap occurs in this case. -/
theorem one_block_outer_coordinates_zero {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (hd : d.blocks.length = 1)
    (h : BlowupCoordinates m d) (a : BlockIndex d) :
    outerH h a = 0 ∧ outerY h a = 0 := by
  have hall : ∀ b : BlockIndex d, b = a := by
    intro b
    apply Fin.ext
    have hb := b.isLt
    have ha := a.isLt
    omega
  have hsumH : (∑ b : BlockIndex d, datumBlockMass m d b * outerH h b) =
      datumBlockMass m d a * outerH h a := by
    apply Finset.sum_eq_single a
    · intro b _ hba
      exact (hba (hall b)).elim
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  have hsumY : (∑ b : BlockIndex d, datumBlockMass m d b * outerY h b) =
      datumBlockMass m d a * outerY h a := by
    apply Finset.sum_eq_single a
    · intro b _ hba
      exact (hba (hall b)).elim
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  have hH := (coordinate_constraints h).1
  have hY := (coordinate_constraints h).2.1
  rw [hsumH] at hH
  rw [hsumY] at hY
  exact ⟨(mul_eq_zero.mp hH).resolve_left (datumBlockMass_ne_zero hm d a),
    (mul_eq_zero.mp hY).resolve_left (datumBlockMass_ne_zero hm d a)⟩
/-- For k=1 all labels belong to the same block, without a cross-block gap. -/
theorem one_block_same_blockOf (d : OrderedClusterDatum) (hd : d.blocks.length = 1)
    (i j : Label) : blockOf d i = blockOf d j := by
  apply Fin.ext
  have hi := (blockOf d i).isLt
  have hj := (blockOf d j).isLt
  omega

theorem one_block_all_distances_lt_cut {_m : Masses} {d : OrderedClusterDatum}
    {q : Configuration} {cut : ℝ} (hd : d.blocks.length = 1)
    (hr : DistanceRecoversBlocks d q cut) (i j : Label) : dist (q i) (q j) < cut :=
  (hr i j).mpr (one_block_same_blockOf d hd i j)

theorem blockOf_surjective (d : OrderedClusterDatum) : Function.Surjective (blockOf d) := by
  intro a
  obtain ⟨i, hi⟩ := datumBlockLabels_nonempty d a
  exact ⟨i, blockOf_eq_of_mem d (by simpa [datumBlockLabels] using hi)⟩

/-- Four nonempty disjoint blocks on the four literal labels are singleton
blocks. This proof uses finite surjectivity, not an extra singleton axiom. -/
theorem four_block_blockOf_injective (d : OrderedClusterDatum) (hd : d.blocks.length = 4) :
    Function.Injective (blockOf d) :=
  (Finite.injective_iff_surjective_of_equiv (finCongr hd.symm)).mpr (blockOf_surjective d)

theorem four_block_unique_label (d : OrderedClusterDatum) (hd : d.blocks.length = 4)
    (a : BlockIndex d) : ∃! i : Label, i ∈ datumBlock d a := by
  obtain ⟨i, hi⟩ := datumBlockLabels_nonempty d a
  have himem : i ∈ datumBlock d a := by simpa [datumBlockLabels] using hi
  refine ⟨i, himem, ?_⟩
  intro j hj
  apply four_block_blockOf_injective d hd
  exact (blockOf_eq_of_mem d hj).trans (blockOf_eq_of_mem d himem).symm

theorem four_block_distinct_labels_not_close {d : OrderedClusterDatum}
    {q : Configuration} {cut : ℝ} (hd : d.blocks.length = 4)
    (hr : DistanceRecoversBlocks d q cut) {i j : Label} (hij : i ≠ j) :
    ¬ dist (q i) (q j) < cut := by
  intro hdist
  exact hij (four_block_blockOf_injective d hd ((hr i j).mp hdist))

end FourBody

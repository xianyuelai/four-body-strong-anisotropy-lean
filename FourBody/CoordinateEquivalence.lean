import FourBody.StatementDefinitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Pairwise
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The actual blow-up coordinate equivalence

For a datum of actual ordered blocks, this file constructs the unique
block containing each label, proves the finite partition sum identity,
and constructs Qε and its inverse using the physical mass means.
No solution, seed, compactness or implicit-function conclusion is assumed.

Frozen source: four_body_strong_anisotropy_pro_v2.tex, SHA256
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD,
eq:constraints and eq:coordinates (lines 512--536), together with the
sequence's literal mass-mean coordinates in eq:sequence-coordinates.

The algebraic identities use ε ≠ 0. Hence they apply in particular to the
paper's physical ε > 0 range, without claiming physical force equivalence
for negative ε.

Finite weighted-mean proof patterns were inspected read-only in the
authorized older local project; this module does not import that project.
Their source hashes and the current verification status are recorded in
COORDINATE_EQUIVALENCE.prep.json.
-/

noncomputable section

open scoped BigOperators

namespace FourBody

theorem datumBlock_mem (d : OrderedClusterDatum) (a : BlockIndex d) :
    datumBlock d a ∈ d.blocks :=
  List.get_mem d.blocks a

theorem datumBlock_nonempty (d : OrderedClusterDatum) (a : BlockIndex d) :
    datumBlock d a ≠ [] :=
  d.nonempty_blocks _ (datumBlock_mem d a)

theorem datumBlockLabels_nonempty (d : OrderedClusterDatum) (a : BlockIndex d) :
    (datumBlockLabels d a).Nonempty := by
  have h := datumBlock_nonempty d a
  cases hb : datumBlock d a with
  | nil => exact (h hb).elim
  | cons i b =>
    exact ⟨i, by simp [datumBlockLabels, hb]⟩

theorem datumBlockMass_pos {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (a : BlockIndex d) : 0 < datumBlockMass m d a := by
  exact Finset.sum_pos (fun i _ => hm i) (datumBlockLabels_nonempty d a)

theorem datumBlockMass_ne_zero {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (a : BlockIndex d) : datumBlockMass m d a ≠ 0 :=
  ne_of_gt (datumBlockMass_pos hm d a)

/-- Uniqueness is for block POSITIONS, not merely for equal block lists. -/
theorem datumBlock_index_unique (d : OrderedClusterDatum) {i : Label}
    {a b : BlockIndex d} (ha : i ∈ datumBlock d a) (hb : i ∈ datumBlock d b) :
    a = b := by
  by_contra hab
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact (d.pairwise_disjoint_blocks.rel_get_of_lt hab) ha hb
  · exact (d.pairwise_disjoint_blocks.rel_get_of_lt hba) hb ha

theorem datumBlock_existsUnique (d : OrderedClusterDatum) (i : Label) :
    ∃! a : BlockIndex d, i ∈ datumBlock d a := by
  have hex : ∃ b ∈ d.blocks, i ∈ b := List.mem_flatten.mp (d.every_label_mem i)
  obtain ⟨a, ha⟩ := List.exists_mem_iff_get.mp hex
  refine ⟨a, ha, ?_⟩
  intro b hb
  exact datumBlock_index_unique d hb ha

/-- The choice selects a PROVED unique actual block; no datum certificate. -/
def blockOf (d : OrderedClusterDatum) (i : Label) : BlockIndex d :=
  Classical.choose (ExistsUnique.exists (datumBlock_existsUnique d i))

theorem label_mem_blockOf (d : OrderedClusterDatum) (i : Label) :
    i ∈ datumBlock d (blockOf d i) :=
  Classical.choose_spec (ExistsUnique.exists (datumBlock_existsUnique d i))

theorem blockOf_eq_of_mem (d : OrderedClusterDatum) {i : Label}
    {a : BlockIndex d} (hi : i ∈ datumBlock d a) : blockOf d i = a :=
  datumBlock_index_unique d (label_mem_blockOf d i) hi

theorem mem_datumBlock_iff (d : OrderedClusterDatum) (i : Label) (a : BlockIndex d) :
    i ∈ datumBlock d a ↔ blockOf d i = a := by
  constructor
  · exact blockOf_eq_of_mem d
  · intro h
    simpa only [h] using label_mem_blockOf d i

theorem datumBlockLabels_eq_fiber (d : OrderedClusterDatum) (a : BlockIndex d) :
    datumBlockLabels d a = Finset.univ.filter (fun i => blockOf d i = a) := by
  ext i
  simp [datumBlockLabels, mem_datumBlock_iff]

/-- The partition sum is proved for every additive commutative monoid.
It is then used for genuine scalar and Euclidean weighted sums. -/
theorem sum_datumBlocks {A : Type*} [AddCommMonoid A] (d : OrderedClusterDatum)
    (f : Label → A) :
    (∑ a : BlockIndex d, ∑ i ∈ datumBlockLabels d a, f i) = ∑ i, f i := by
  classical
  simp_rw [datumBlockLabels_eq_fiber]
  exact Finset.sum_fiberwise Finset.univ (blockOf d) f

/-- All four equations of eq:constraints, with the original masses. -/
theorem mem_coordinateSpace_iff (m : Masses) (d : OrderedClusterDatum)
    (z : CoordinateAmbient d) :
    z ∈ coordinateSpace m d ↔
      (∑ a, datumBlockMass m d a * z.1.1 a) = 0 ∧
      (∑ a, datumBlockMass m d a * z.1.2 a) = 0 ∧
      (∀ a, (∑ i ∈ datumBlockLabels d a, m i * z.2.1 i) = 0) ∧
      (∀ a, (∑ i ∈ datumBlockLabels d a, m i * z.2.2 i) = 0) := by
  constructor
  · intro hz
    change coordinateConstraintLM m d z = 0 at hz
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [coordinateConstraintLM] using congrArg (fun t => t.1.1) hz
    · simpa [coordinateConstraintLM] using congrArg (fun t => t.1.2) hz
    · intro a
      simpa [coordinateConstraintLM] using congrArg (fun t => t.2.1 a) hz
    · intro a
      simpa [coordinateConstraintLM] using congrArg (fun t => t.2.2 a) hz
  · rintro ⟨hH, hY, hu, hv⟩
    change coordinateConstraintLM m d z = 0
    ext <;> simp [coordinateConstraintLM, hH, hY, hu, hv]

theorem coordinate_constraints {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) :
    (∑ a, datumBlockMass m d a * outerH h a) = 0 ∧
    (∑ a, datumBlockMass m d a * outerY h a) = 0 ∧
    (∀ a, (∑ i ∈ datumBlockLabels d a, m i * innerU h i) = 0) ∧
    (∀ a, (∑ i ∈ datumBlockLabels d a, m i * innerV h i) = 0) :=
  (mem_coordinateSpace_iff m d h.val).mp h.property

theorem mem_W_iff (m : Masses) (q : Configuration) :
    q ∈ W m ↔
      (∑ i, m i * q i 0) = 0 ∧ (∑ i, m i * q i 1) = 0 := by
  constructor
  · intro hq
    change centerLM m q = 0 at hq
    constructor
    · simpa only [centerLM_apply, WithLp.ofLp_sum, Finset.sum_apply,
        PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul] using
        congrArg (fun p : Point => p 0) hq
    · simpa only [centerLM_apply, WithLp.ofLp_sum, Finset.sum_apply,
        PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul] using
        congrArg (fun p : Point => p 1) hq
  · rintro ⟨hx, hy⟩
    change centerLM m q = 0
    ext k
    fin_cases k
    · simpa only [centerLM_apply, WithLp.ofLp_sum, Finset.sum_apply,
        PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, Fin.mk_zero] using hx
    · simpa only [centerLM_apply, WithLp.ofLp_sum, Finset.sum_apply,
        PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, Fin.mk_one] using hy

private theorem weighted_affine_sum (m : Masses) (d : OrderedClusterDatum)
    (a : BlockIndex d) (f : Label → ℝ) (c t : ℝ) :
    (∑ i ∈ datumBlockLabels d a, m i * (c + t * f i)) =
      datumBlockMass m d a * c + t * (∑ i ∈ datumBlockLabels d a, m i * f i) := by
  simp_rw [mul_add, show ∀ i, m i * (t * f i) = t * (m i * f i) from
    fun i => by ring]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rfl

/-- Literal q_i=(εH_a+εu_i,Y_a+εv_i), at the unique actual block. -/
def physicalCoordinates {m : Masses} {d : OrderedClusterDatum} (ε : ℝ)
    (h : BlowupCoordinates m d) : Configuration :=
  fun i => !₂[ε * outerH h (blockOf d i) + ε * innerU h i,
    outerY h (blockOf d i) + ε * innerV h i]

theorem represents_physicalCoordinates {m : Masses} {d : OrderedClusterDatum}
    (ε : ℝ) (h : BlowupCoordinates m d) :
    RepresentsCoordinates m d ε h (physicalCoordinates ε h) := by
  intro a i hi
  simp only [physicalCoordinates, blockOf_eq_of_mem d hi]

theorem represents_iff_eq_physicalCoordinates {m : Masses} {d : OrderedClusterDatum}
    (ε : ℝ) (h : BlowupCoordinates m d) (q : Configuration) :
    RepresentsCoordinates m d ε h q ↔ q = physicalCoordinates ε h := by
  constructor
  · intro hq
    funext i
    exact hq (blockOf d i) i (label_mem_blockOf d i)
  · rintro rfl
    exact represents_physicalCoordinates ε h

theorem physicalCoordinates_block_sum_x {m : Masses} {d : OrderedClusterDatum}
    (ε : ℝ) (h : BlowupCoordinates m d) (a : BlockIndex d) :
    (∑ i ∈ datumBlockLabels d a, m i * physicalCoordinates ε h i 0) =
      datumBlockMass m d a * (ε * outerH h a) := by
  have hi : ∀ i ∈ datumBlockLabels d a,
      physicalCoordinates ε h i 0 = ε * outerH h a + ε * innerU h i := by
    intro i hi
    have himem : i ∈ datumBlock d a := by simpa [datumBlockLabels] using hi
    simp [physicalCoordinates, blockOf_eq_of_mem d himem]
  calc
    _ = ∑ i ∈ datumBlockLabels d a, m i * (ε * outerH h a + ε * innerU h i) :=
      Finset.sum_congr rfl (fun i hmem => by rw [hi i hmem])
    _ = _ := by
      rw [weighted_affine_sum, (coordinate_constraints h).2.2.1 a, mul_zero, add_zero]

theorem physicalCoordinates_block_sum_y {m : Masses} {d : OrderedClusterDatum}
    (ε : ℝ) (h : BlowupCoordinates m d) (a : BlockIndex d) :
    (∑ i ∈ datumBlockLabels d a, m i * physicalCoordinates ε h i 1) =
      datumBlockMass m d a * outerY h a := by
  have hi : ∀ i ∈ datumBlockLabels d a,
      physicalCoordinates ε h i 1 = outerY h a + ε * innerV h i := by
    intro i hi
    have himem : i ∈ datumBlock d a := by simpa [datumBlockLabels] using hi
    simp [physicalCoordinates, blockOf_eq_of_mem d himem]
  calc
    _ = ∑ i ∈ datumBlockLabels d a, m i * (outerY h a + ε * innerV h i) :=
      Finset.sum_congr rfl (fun i hmem => by rw [hi i hmem])
    _ = _ := by
      rw [weighted_affine_sum, (coordinate_constraints h).2.2.2 a, mul_zero, add_zero]

theorem physicalCoordinates_mem_W {m : Masses} {d : OrderedClusterDatum}
    (ε : ℝ) (h : BlowupCoordinates m d) : physicalCoordinates ε h ∈ W m := by
  apply (mem_W_iff m _).mpr
  constructor
  · calc
      (∑ i, m i * physicalCoordinates ε h i 0) =
          ∑ a, ∑ i ∈ datumBlockLabels d a, m i * physicalCoordinates ε h i 0 :=
        (sum_datumBlocks d _).symm
      _ = ∑ a, datumBlockMass m d a * (ε * outerH h a) :=
        Finset.sum_congr rfl (fun a _ => physicalCoordinates_block_sum_x ε h a)
      _ = ε * (∑ a, datumBlockMass m d a * outerH h a) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = 0 := by rw [(coordinate_constraints h).1, mul_zero]
  · calc
      (∑ i, m i * physicalCoordinates ε h i 1) =
          ∑ a, ∑ i ∈ datumBlockLabels d a, m i * physicalCoordinates ε h i 1 :=
        (sum_datumBlocks d _).symm
      _ = ∑ a, datumBlockMass m d a * outerY h a :=
        Finset.sum_congr rfl (fun a _ => physicalCoordinates_block_sum_y ε h a)
      _ = 0 := (coordinate_constraints h).2.1

/-- The paper's Qε as a genuine linear map to the original mass-centered W. -/
def coordinateQ (m : Masses) (d : OrderedClusterDatum) (ε : ℝ) :
    BlowupCoordinates m d →ₗ[ℝ] W m where
  toFun h := ⟨physicalCoordinates ε h, physicalCoordinates_mem_W ε h⟩
  map_add' h g := by
    apply Subtype.ext
    funext i
    ext k
    fin_cases k <;>
      simp [physicalCoordinates, outerH, outerY, innerU, innerV, mul_add] <;> ring
  map_smul' c h := by
    apply Subtype.ext
    funext i
    ext k
    fin_cases k <;>
      simp [physicalCoordinates, outerH, outerY, innerU, innerV,
        smul_eq_mul, mul_add, mul_left_comm]

theorem datumBlockMean_apply (m : Masses) (d : OrderedClusterDatum)
    (q : Configuration) (a : BlockIndex d) (k : Axis) :
    datumBlockMean m d q a k =
      (datumBlockMass m d a)⁻¹ * (∑ i ∈ datumBlockLabels d a, m i * q i k) := by
  simp only [datumBlockMean, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul]

theorem block_mass_mul_mean {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (q : Configuration) (a : BlockIndex d) (k : Axis) :
    datumBlockMass m d a * datumBlockMean m d q a k =
      ∑ i ∈ datumBlockLabels d a, m i * q i k := by
  rw [datumBlockMean_apply, ← mul_assoc, mul_inv_cancel₀ (datumBlockMass_ne_zero hm d a),
    one_mul]

theorem sum_block_mass_means {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (q : Configuration) (k : Axis) :
    (∑ a, datumBlockMass m d a * datumBlockMean m d q a k) =
      ∑ i, m i * q i k := by
  simp_rw [block_mass_mul_mean hm]
  exact sum_datumBlocks d _

theorem datumBlockMean_physicalCoordinates {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (ε : ℝ) (h : BlowupCoordinates m d) (a : BlockIndex d) :
    datumBlockMean m d (physicalCoordinates ε h) a = !₂[ε * outerH h a, outerY h a] := by
  have hM := datumBlockMass_ne_zero hm d a
  ext k
  fin_cases k
  · simp only [Fin.mk_zero, datumBlockMean_apply, physicalCoordinates_block_sum_x]
    simp [hM, ← mul_assoc]
  · simp only [Fin.mk_one, datumBlockMean_apply, physicalCoordinates_block_sum_y]
    simp [hM]

/-- Every coordinate is the literal physical block mean/deviation formula.
This is defined even at ε=0, but inverse laws are only asserted for ε≠0. -/
def meanInverseAmbient (m : Masses) (d : OrderedClusterDatum) (ε : ℝ)
    (q : Configuration) : CoordinateAmbient d :=
  ((fun a => datumBlockMean m d q a 0 / ε,
    fun a => datumBlockMean m d q a 1),
   (fun i => (q i 0 - datumBlockMean m d q (blockOf d i) 0) / ε,
    fun i => (q i 1 - datumBlockMean m d q (blockOf d i) 1) / ε))

private theorem block_mean_deviations_sum {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (ε : ℝ) (q : Configuration) (a : BlockIndex d) (k : Axis) :
    (∑ i ∈ datumBlockLabels d a,
      m i * ((q i k - datumBlockMean m d q (blockOf d i) k) / ε)) = 0 := by
  have hblock : ∀ i ∈ datumBlockLabels d a, blockOf d i = a := by
    intro i hi
    exact blockOf_eq_of_mem d (by simpa [datumBlockLabels] using hi)
  calc
    _ = ∑ i ∈ datumBlockLabels d a,
        (m i * q i k - m i * datumBlockMean m d q a k) / ε := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hblock i hi]
      ring
    _ = ((∑ i ∈ datumBlockLabels d a, m i * q i k) -
        datumBlockMass m d a * datumBlockMean m d q a k) / ε := by
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul]
      rfl
    _ = 0 := by rw [block_mass_mul_mean hm, sub_self, zero_div]

theorem meanInverseAmbient_mem {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (ε : ℝ) (q : W m) :
    meanInverseAmbient m d ε q.val ∈ coordinateSpace m d := by
  have hq := (mem_W_iff m q.val).mp q.property
  apply (mem_coordinateSpace_iff m d _).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (∑ a, datumBlockMass m d a * (datumBlockMean m d q.val a 0 / ε)) = 0
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, sum_block_mass_means hm, hq.1, zero_div]
  · change (∑ a, datumBlockMass m d a * datumBlockMean m d q.val a 1) = 0
    rw [sum_block_mass_means hm, hq.2]
  · exact fun a => block_mean_deviations_sum hm d ε q.val a 0
  · exact fun a => block_mean_deviations_sum hm d ε q.val a 1

def meanInverse {m : Masses} (hm : PositiveMasses m) (d : OrderedClusterDatum)
    (ε : ℝ) (q : W m) : BlowupCoordinates m d :=
  ⟨meanInverseAmbient m d ε q.val, meanInverseAmbient_mem hm d ε q⟩

theorem meanInverse_coordinateQ {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) {ε : ℝ} (hε : ε ≠ 0) (h : BlowupCoordinates m d) :
    meanInverse hm d ε (coordinateQ m d ε h) = h := by
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · funext a
      change datumBlockMean m d (physicalCoordinates ε h) a 0 / ε = outerH h a
      rw [datumBlockMean_physicalCoordinates hm]
      simp [hε]
    · funext a
      change datumBlockMean m d (physicalCoordinates ε h) a 1 = outerY h a
      rw [datumBlockMean_physicalCoordinates hm]
      simp
  · apply Prod.ext
    · funext i
      change (physicalCoordinates ε h i 0 -
        datumBlockMean m d (physicalCoordinates ε h) (blockOf d i) 0) / ε = innerU h i
      rw [datumBlockMean_physicalCoordinates hm]
      simp [physicalCoordinates, hε]
    · funext i
      change (physicalCoordinates ε h i 1 -
        datumBlockMean m d (physicalCoordinates ε h) (blockOf d i) 1) / ε = innerV h i
      rw [datumBlockMean_physicalCoordinates hm]
      simp [physicalCoordinates, hε]

theorem coordinateQ_meanInverse {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) {ε : ℝ} (hε : ε ≠ 0) (q : W m) :
    coordinateQ m d ε (meanInverse hm d ε q) = q := by
  apply Subtype.ext
  funext i
  ext k
  fin_cases k
  · change ε * (datumBlockMean m d q.val (blockOf d i) 0 / ε) +
      ε * ((q.val i 0 - datumBlockMean m d q.val (blockOf d i) 0) / ε) = q.val i 0
    field_simp [hε]
    ring
  · change datumBlockMean m d q.val (blockOf d i) 1 +
      ε * ((q.val i 1 - datumBlockMean m d q.val (blockOf d i) 1) / ε) = q.val i 1
    field_simp [hε]
    ring

/-- Explicit linear equivalence, with proved inverse mass-centroid formulas.
It supplies the representation bridge, not invertibility of any Jacobian. -/
def coordinateEquivalence {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) {ε : ℝ} (hε : ε ≠ 0) :
    BlowupCoordinates m d ≃ₗ[ℝ] W m where
  toFun := coordinateQ m d ε
  invFun := meanInverse hm d ε
  left_inv := meanInverse_coordinateQ hm d hε
  right_inv := coordinateQ_meanInverse hm d hε
  map_add' := (coordinateQ m d ε).map_add
  map_smul' := (coordinateQ m d ε).map_smul

/-- The concrete kernel has the original six dimensions, through Q at ε=1. -/
theorem finrank_coordinateSpace {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) : Module.finrank ℝ (BlowupCoordinates m d) = 6 := by
  calc
    _ = Module.finrank ℝ (W m) :=
      (coordinateEquivalence hm d (ε := 1) one_ne_zero).finrank_eq
    _ = 6 := finrank_W hm

def coordinateEquivalencePositive {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) {ε : ℝ} (hε : 0 < ε) :
    BlowupCoordinates m d ≃ₗ[ℝ] W m :=
  coordinateEquivalence hm d (ne_of_gt hε)

/-- Continuity follows from the derived finite-dimensional concrete spaces. -/
def coordinateContinuousEquivalence {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) {ε : ℝ} (hε : ε ≠ 0) :
    BlowupCoordinates m d ≃L[ℝ] W m :=
  (coordinateEquivalence hm d hε).toContinuousLinearEquiv

theorem represents_unique_configuration {m : Masses} {d : OrderedClusterDatum}
    {ε : ℝ} {h : BlowupCoordinates m d} {q q' : Configuration}
    (hq : RepresentsCoordinates m d ε h q)
    (hq' : RepresentsCoordinates m d ε h q') : q = q' := by
  rw [represents_iff_eq_physicalCoordinates] at hq hq'
  exact hq.trans hq'.symm

theorem represents_unique_coordinates {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {ε : ℝ} (hε : ε ≠ 0)
    {h h' : BlowupCoordinates m d} {q : Configuration}
    (hq : RepresentsCoordinates m d ε h q)
    (hq' : RepresentsCoordinates m d ε h' q) : h = h' := by
  apply (coordinateEquivalence hm d hε).injective
  apply Subtype.ext
  have hleft := (represents_iff_eq_physicalCoordinates ε h q).mp hq
  have hright := (represents_iff_eq_physicalCoordinates ε h' q).mp hq'
  exact hleft.symm.trans hright

/-- The sequence-coordinate predicate is equivalent to the original position
formula when mass and parameter denominators are nonzero. -/
theorem represents_iff_coordinatesOfConfiguration {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {ε : ℝ} (hε : ε ≠ 0)
    (h : BlowupCoordinates m d) (q : Configuration) :
    RepresentsCoordinates m d ε h q ↔ CoordinatesOfConfiguration m d ε q h := by
  constructor
  · intro hq
    have heq := (represents_iff_eq_physicalCoordinates ε h q).mp hq
    refine ⟨hq, ?_, ?_, ?_⟩
    · intro a
      rw [heq]
      simp [horizontalCenterCoordinate, datumBlockMean_physicalCoordinates hm, hε]
    · intro a
      rw [heq]
      simp [verticalCenterCoordinate, datumBlockMean_physicalCoordinates hm]
    · intro a i hi
      rw [heq]
      rw [internalVectorCoordinate, datumBlockMean_physicalCoordinates hm]
      ext k
      fin_cases k <;>
        simp [physicalCoordinates, blockOf_eq_of_mem d hi, hε, smul_eq_mul]
  · exact fun hq => hq.1

theorem represents_existsUnique {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) {ε : ℝ} (hε : ε ≠ 0) (q : W m) :
    ∃! h : BlowupCoordinates m d, RepresentsCoordinates m d ε h q.val := by
  refine ⟨meanInverse hm d ε q, ?_, ?_⟩
  · apply (represents_iff_eq_physicalCoordinates ε _ q.val).mpr
    exact (congrArg Subtype.val (coordinateQ_meanInverse hm d hε q)).symm
  · intro h hh
    exact represents_unique_coordinates hm hε hh (by
      apply (represents_iff_eq_physicalCoordinates ε _ q.val).mpr
      exact (congrArg Subtype.val (coordinateQ_meanInverse hm d hε q)).symm)

end FourBody


import FourBody.DatumRecovery
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-!
# Actual mixed data lie on neither axis

Frozen manuscript SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

Exact source mapping, Section 5:
* lines 726--730: a collinear IsSolution with s > 1 lies on an axis;
  this module uses Geometry.collinear_solution_axis as proved there.
* lines 730--732: 1 < k gives distinct physical block mean heights;
  k < 4 gives a nonsingleton actual block and distinct physical x values.
* lines 732--733: these two axis exclusions imply genuine noncollinearity.
* line 734: the number 144 is not a solution-count conclusion of this
  module. The existing actual-data cardinality theorem counts data only.
* lines 735--740: end of proof and bibliography; no additional assumption.

STATIC CANDIDATE, not elaborated or compiled. The datum is the original
list of nonempty ordered lists on Label = Fin 4. The finite-card argument
uses the actual blockOf map. Collinear keeps its affine-line definition;
it is not replaced by an axis disjunction or by the block-count predicate.
The rectangle corollaries derive actual orders from RecoveryBounds.
No analytic branch, classification, or global exhaustion is assumed.
-/

noncomputable section
open scoped BigOperators
namespace FourBody

/-- The finite-card pigeonhole principle applies to the actual assignment
of the four literal labels to the actual block positions. -/
theorem distinct_labels_same_blockOf_of_blockCount_lt_four
    (d : OrderedClusterDatum) (hk : d.blocks.length < 4) :
    ∃ i j : Label, i ≠ j ∧ blockOf d i = blockOf d j := by
  classical
  have hcard : Fintype.card (BlockIndex d) < Fintype.card Label := by
    simpa only [BlockIndex, Label, Fintype.card_fin] using hk
  have hnot := Fintype.not_injective_of_card_lt (blockOf d) hcard
  by_contra hex
  apply hnot
  intro i j hij
  by_contra hne
  exact hex ⟨i, j, hne, hij⟩

/-- An actual list block contains two different literal labels, and its
actual number of positions exceeds one. No singleton certificate is input. -/
theorem actual_nonsingleton_block_of_blockCount_lt_four
    (d : OrderedClusterDatum) (hk : d.blocks.length < 4) :
    ∃ a : BlockIndex d, 1 < (datumBlock d a).length ∧
      ∃ i j : Label, i ≠ j ∧ i ∈ datumBlock d a ∧ j ∈ datumBlock d a := by
  obtain ⟨i, j, hij, hblock⟩ :=
    distinct_labels_same_blockOf_of_blockCount_lt_four d hk
  let a : BlockIndex d := blockOf d i
  have hi : i ∈ datumBlock d a := label_mem_blockOf d i
  have hj : j ∈ datumBlock d a := (mem_datumBlock_iff d j a).mpr hblock.symm
  obtain ⟨u, hu⟩ := List.exists_mem_iff_get.mp
    (show ∃ k ∈ datumBlock d a, k = i from ⟨i, hi, rfl⟩)
  obtain ⟨v, hv⟩ := List.exists_mem_iff_get.mp
    (show ∃ k ∈ datumBlock d a, k = j from ⟨j, hj, rfl⟩)
  have huv : u ≠ v := by
    intro huv
    apply hij
    calc
      i = (datumBlock d a).get u := hu.symm
      _ = (datumBlock d a).get v :=
        congrArg (fun w : InternalIndex d a => (datumBlock d a).get w) huv
      _ = j := hv
  have hlen : 1 < (datumBlock d a).length := by
    have huBound := u.isLt
    have hvBound := v.isLt
    have huvVal : u.val ≠ v.val := fun h => huv (Fin.ext h)
    omega
  exact ⟨a, hlen, i, j, hij, hi, hj⟩

/-- The manuscript's horizontal difference is witnessed by actual points:
positions zero and one of a real nonsingleton list block give distinct
literal labels with strictly ordered physical x coordinates. -/
theorem actual_horizontal_pair_of_internal_order {d : OrderedClusterDatum}
    {q : Configuration}
    (horder : ∀ a : BlockIndex d,
      StrictMono (fun i : InternalIndex d a => q (internalLabel d a i) 0))
    (hk : d.blocks.length < 4) :
    ∃ (a : BlockIndex d) (i j : Label), i ≠ j ∧
      i ∈ datumBlock d a ∧ j ∈ datumBlock d a ∧
      blockOf d i = blockOf d j ∧ q i 0 < q j 0 := by
  obtain ⟨a, hlen, _⟩ := actual_nonsingleton_block_of_blockCount_lt_four d hk
  let u : InternalIndex d a := ⟨0, by omega⟩
  let v : InternalIndex d a := ⟨1, hlen⟩
  have huv : u < v := by
    change (0 : ℕ) < 1
    omega
  let i : Label := internalLabel d a u
  let j : Label := internalLabel d a v
  have hi : i ∈ datumBlock d a := List.get_mem (datumBlock d a) u
  have hj : j ∈ datumBlock d a := List.get_mem (datumBlock d a) v
  have hlt : q i 0 < q j 0 := horder a huv
  have hij : i ≠ j := fun heq =>
    (ne_of_lt hlt) (congrArg (fun k : Label => q k 0) heq)
  have hblock : blockOf d i = blockOf d j :=
    (blockOf_eq_of_mem d hi).trans (blockOf_eq_of_mem d hj).symm
  exact ⟨a, i, j, hij, hi, hj, hblock, hlt⟩

/-- Strict internal order refers to the actual horizontal coordinates.
On the y-axis those values would all be zero, including the two positions
of the nonsingleton block obtained by finite-card pigeonhole. -/
theorem not_onYAxis_of_actual_internal_order {d : OrderedClusterDatum}
    {q : Configuration}
    (horder : ∀ a : BlockIndex d,
      StrictMono (fun i : InternalIndex d a => q (internalLabel d a i) 0))
    (hk : d.blocks.length < 4) : ¬OnYAxis q := by
  obtain ⟨a, hlen, _⟩ := actual_nonsingleton_block_of_blockCount_lt_four d hk
  let u : InternalIndex d a := ⟨0, by omega⟩
  let v : InternalIndex d a := ⟨1, hlen⟩
  have huv : u < v := by
    change (0 : ℕ) < 1
    omega
  intro hy
  have hlt := horder a huv
  change q (internalLabel d a u) 0 < q (internalLabel d a v) 0 at hlt
  rw [hy (internalLabel d a u), hy (internalLabel d a v)] at hlt
  exact (lt_irrefl (0 : ℝ)) hlt

/-- Actual block mass-mean heights vanish on the x-axis. This uses the
literal mean formula, and is valid even without positivity of the masses. -/
theorem datumBlockMean_height_zero_of_onXAxis (m : Masses)
    (d : OrderedClusterDatum) {q : Configuration} (hx : OnXAxis q)
    (a : BlockIndex d) : datumBlockMean m d q a 1 = 0 := by
  rw [datumBlockMean_apply]
  have hz : (∑ i ∈ datumBlockLabels d a, m i * q i 1) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hx i, mul_zero]
  rw [hz, mul_zero]

/-- With more than one actual block, strict order of physical barycenter
heights supplies a nonzero vertical difference, excluding the x-axis. -/
theorem not_onXAxis_of_actual_barycenter_order {m : Masses}
    {d : OrderedClusterDatum} {q : Configuration}
    (horder : StrictMono (fun a : BlockIndex d => datumBlockMean m d q a 1))
    (hk : 1 < d.blocks.length) : ¬OnXAxis q := by
  let a : BlockIndex d := ⟨0, by omega⟩
  let b : BlockIndex d := ⟨1, hk⟩
  have hab : a < b := by
    change (0 : ℕ) < 1
    omega
  intro hx
  have hlt := horder hab
  change datumBlockMean m d q a 1 < datumBlockMean m d q b 1 at hlt
  rw [datumBlockMean_height_zero_of_onXAxis m d hx a,
    datumBlockMean_height_zero_of_onXAxis m d hx b] at hlt
  exact (lt_irrefl (0 : ℝ)) hlt

theorem not_onYAxis_of_orderedByConfiguration {m : Masses}
    {d : OrderedClusterDatum} {q : Configuration}
    (hd : OrderedByConfiguration m q d) (hk : d.blocks.length < 4) :
    ¬OnYAxis q :=
  not_onYAxis_of_actual_internal_order hd.internal_x_order hk

theorem not_onXAxis_of_orderedByConfiguration {m : Masses}
    {d : OrderedClusterDatum} {q : Configuration}
    (hd : OrderedByConfiguration m q d) (hk : 1 < d.blocks.length) :
    ¬OnXAxis q :=
  not_onXAxis_of_actual_barycenter_order hd.block_height_order hk

/-- The datum's proved nonempty-block lower bound and axis exclusion
identify the only block count compatible with the x-axis. -/
theorem onXAxis_blockCount_eq_one_of_orderedByConfiguration {m : Masses}
    {d : OrderedClusterDatum} {q : Configuration}
    (hd : OrderedByConfiguration m q d) (hx : OnXAxis q) :
    d.blocks.length = 1 := by
  have hpos : 0 < d.blocks.length := by
    simpa only [OrderedClusterDatum.blockCount] using d.blockCount_pos
  by_contra hk
  have hgt : 1 < d.blocks.length := by omega
  exact not_onXAxis_of_orderedByConfiguration hd hgt hx

/-- The datum's proved four-label upper bound and axis exclusion
identify the only block count compatible with the y-axis. -/
theorem onYAxis_blockCount_eq_four_of_orderedByConfiguration {m : Masses}
    {d : OrderedClusterDatum} {q : Configuration}
    (hd : OrderedByConfiguration m q d) (hy : OnYAxis q) :
    d.blocks.length = 4 := by
  have hle : d.blocks.length ≤ 4 := by
    simpa only [OrderedClusterDatum.blockCount] using d.blockCount_le_four
  by_contra hk
  have hlt : d.blocks.length < 4 := by omega
  exact not_onYAxis_of_orderedByConfiguration hd hlt hy

/-- The original affine-line predicate is used by the imported geometric
theorem. For an actual anisotropic solution, either axis contradicts one
of the two actual orders when 1 < k < 4. -/
theorem mixed_ordered_solution_noncollinear {m : Masses}
    (hm : PositiveMasses m) {s : ℝ} (hs : 1 < s) {q : Configuration}
    (hsol : IsSolution m s q) {d : OrderedClusterDatum}
    (hd : OrderedByConfiguration m q d)
    (hklo : 1 < d.blocks.length) (hkhi : d.blocks.length < 4) :
    ¬Collinear q := by
  intro hcol
  rcases collinear_solution_axis hm hs hsol hcol with hx | hy
  · exact not_onXAxis_of_orderedByConfiguration hd hklo hx
  · exact not_onYAxis_of_orderedByConfiguration hd hkhi hy

/-- Every collinear actual solution carrying these physical orders has
one of the two extreme block counts. This is a converse constraint only. -/
theorem ordered_collinear_solution_has_extreme_blockCount {m : Masses}
    (hm : PositiveMasses m) {s : ℝ} (hs : 1 < s) {q : Configuration}
    (hsol : IsSolution m s q) {d : OrderedClusterDatum}
    (hd : OrderedByConfiguration m q d) (hcol : Collinear q) :
    d.blocks.length = 1 ∨ d.blocks.length = 4 := by
  rcases collinear_solution_axis hm hs hsol hcol with hx | hy
  · exact Or.inl (onXAxis_blockCount_eq_one_of_orderedByConfiguration hd hx)
  · exact Or.inr (onYAxis_blockCount_eq_four_of_orderedByConfiguration hd hy)

/-- Derive both actual physical orders from the existing rectangle and
representation lemmas. Distance recovery and a small-epsilon estimate
are unnecessary for these two order implications. -/
theorem orderedByConfiguration_of_recoveryRectangle {m : Masses}
    (hm : PositiveMasses m) {d : OrderedClusterDatum} {γ A ε : ℝ}
    {h : BlowupCoordinates m d} {q : Configuration}
    (hγ : 0 < γ) (hε : 0 < ε) (hr : RecoveryRectangle m d γ A h)
    (hq : RepresentsCoordinates m d ε h q) : OrderedByConfiguration m q d :=
  ⟨recovery_barycenter_heights_strictMono hm hγ hr hq,
    recovery_internal_horizontal_strictMono hε hr hq⟩

/-- The manuscript's vertical difference is a difference of actual label
positions, with the quantitative gamma/4 bound. The first two actual
nonempty blocks supply labels; the already proved cross-block estimate
then supplies their vertical separation. No whole recovery theorem is input. -/
theorem actual_vertical_pair_of_recoveryRectangle {m : Masses}
    {d : OrderedClusterDatum} {γ A ε : ℝ} {h : BlowupCoordinates m d}
    {q : Configuration} (hγ : 0 < γ) (hε : 0 ≤ ε)
    (hs : RecoverySmall γ A ε) (hr : RecoveryRectangle m d γ A h)
    (hq : RepresentsCoordinates m d ε h q) (hk : 1 < d.blocks.length) :
    ∃ (a b : BlockIndex d) (i j : Label), a < b ∧
      i ∈ datumBlock d a ∧ j ∈ datumBlock d b ∧ i ≠ j ∧
      γ / 4 < q j 1 - q i 1 ∧ q i 1 < q j 1 := by
  let a : BlockIndex d := ⟨0, by omega⟩
  let b : BlockIndex d := ⟨1, hk⟩
  have hab : a < b := by
    change (0 : ℕ) < 1
    omega
  obtain ⟨i, hi⟩ := datumBlockLabels_nonempty d a
  obtain ⟨j, hj⟩ := datumBlockLabels_nonempty d b
  have himem : i ∈ datumBlock d a := by simpa [datumBlockLabels] using hi
  have hjmem : j ∈ datumBlock d b := by simpa [datumBlockLabels] using hj
  have hgap : γ / 4 < q j 1 - q i 1 :=
    cross_block_vertical_gap hε hs hr hq a b hab i j himem hjmem
  have hpos : 0 < q j 1 - q i 1 :=
    lt_trans (div_pos hγ (by norm_num)) hgap
  have hlt : q i 1 < q j 1 := sub_pos.mp hpos
  have hij : i ≠ j := fun heq =>
    (ne_of_lt hlt) (congrArg (fun k : Label => q k 1) heq)
  exact ⟨a, b, i, j, hab, himem, hjmem, hij, hgap, hlt⟩

/-- The natural rectangle/representation version of the actual axis
exclusions, with no branch or classification hypothesis. -/
theorem mixed_recoveryRectangle_neither_axis {m : Masses}
    (hm : PositiveMasses m) {d : OrderedClusterDatum} {γ A ε : ℝ}
    {h : BlowupCoordinates m d} {q : Configuration}
    (hγ : 0 < γ) (hε : 0 < ε) (hr : RecoveryRectangle m d γ A h)
    (hq : RepresentsCoordinates m d ε h q)
    (hklo : 1 < d.blocks.length) (hkhi : d.blocks.length < 4) :
    ¬OnXAxis q ∧ ¬OnYAxis q := by
  have hd := orderedByConfiguration_of_recoveryRectangle hm hγ hε hr hq
  exact ⟨not_onXAxis_of_orderedByConfiguration hd hklo,
    not_onYAxis_of_orderedByConfiguration hd hkhi⟩

/-- The natural Section 5 mixed-stratum conclusion is noncollinearity
of the represented literal tuple, provided it satisfies IsSolution. -/
theorem mixed_represented_solution_noncollinear {m : Masses}
    (hm : PositiveMasses m) {d : OrderedClusterDatum} {γ A ε s : ℝ}
    {h : BlowupCoordinates m d} {q : Configuration}
    (hγ : 0 < γ) (hε : 0 < ε) (hr : RecoveryRectangle m d γ A h)
    (hq : RepresentsCoordinates m d ε h q) (hs : 1 < s)
    (hsol : IsSolution m s q)
    (hklo : 1 < d.blocks.length) (hkhi : d.blocks.length < 4) :
    ¬Collinear q :=
  mixed_ordered_solution_noncollinear hm hs hsol
    (orderedByConfiguration_of_recoveryRectangle hm hγ hε hr hq) hklo hkhi

theorem onXAxis_blockCount_eq_one_of_recoveryRectangle {m : Masses}
    (hm : PositiveMasses m) {d : OrderedClusterDatum} {γ A ε : ℝ}
    {h : BlowupCoordinates m d} {q : Configuration}
    (hγ : 0 < γ) (hε : 0 < ε) (hr : RecoveryRectangle m d γ A h)
    (hq : RepresentsCoordinates m d ε h q) (hx : OnXAxis q) :
    d.blocks.length = 1 :=
  onXAxis_blockCount_eq_one_of_orderedByConfiguration
    (orderedByConfiguration_of_recoveryRectangle hm hγ hε hr hq) hx

theorem onYAxis_blockCount_eq_four_of_recoveryRectangle {m : Masses}
    (hm : PositiveMasses m) {d : OrderedClusterDatum} {γ A ε : ℝ}
    {h : BlowupCoordinates m d} {q : Configuration}
    (hγ : 0 < γ) (hε : 0 < ε) (hr : RecoveryRectangle m d γ A h)
    (hq : RepresentsCoordinates m d ε h q) (hy : OnYAxis q) :
    d.blocks.length = 4 :=
  onYAxis_blockCount_eq_four_of_orderedByConfiguration
    (orderedByConfiguration_of_recoveryRectangle hm hγ hε hr hq) hy

/-- Qε carries the actual mass-centered configuration. Its underlying
literal tuple has exactly the same geometric noncollinearity conclusion. -/
theorem mixed_coordinateQ_solution_noncollinear {m : Masses}
    (hm : PositiveMasses m) {d : OrderedClusterDatum} {γ A ε s : ℝ}
    (h : BlowupCoordinates m d) (hγ : 0 < γ) (hε : 0 < ε)
    (hr : RecoveryRectangle m d γ A h) (hs : 1 < s)
    (hsol : IsSolution m s (coordinateQ m d ε h).val)
    (hklo : 1 < d.blocks.length) (hkhi : d.blocks.length < 4) :
    ¬Collinear (coordinateQ m d ε h).val :=
  mixed_represented_solution_noncollinear hm hγ hε hr
    (represents_physicalCoordinates ε h) hs hsol hklo hkhi

/-- The raw comparison-neighborhood endpoint derives the rectangle and
physical orders; no axis exclusion or noncollinearity is an input. -/
theorem mixed_seedComparisons_solution_noncollinear {m : Masses}
    (hm : PositiveMasses m) {d : OrderedClusterDatum} {ε s : ℝ}
    (h : BlowupCoordinates m d) (hε : 0 < ε)
    (hr : SeedComparisonBounds hm d h) (hs : 1 < s)
    (hsol : IsSolution m s (coordinateQ m d ε h).val)
    (hklo : 1 < d.blocks.length) (hkhi : d.blocks.length < 4) :
    ¬Collinear (coordinateQ m d ε h).val :=
  mixed_coordinateQ_solution_noncollinear hm h (commonSeedGap_positive hm) hε
    (recoveryRectangle_of_seedComparisons hm hr) hs hsol hklo hkhi

end FourBody

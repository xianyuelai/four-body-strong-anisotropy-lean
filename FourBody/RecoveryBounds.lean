import FourBody.CommonSeedGaps
import FourBody.CoordinateEquivalence
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Literal physical recovery estimates from the frozen Pro v2 Section 5

Frozen manuscript SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
Source lines 677--699: the common positive outer gap, the finite inner
bound A >= 1, d = gamma/8, and the two displayed small-parameter bounds.

STATIC CANDIDATE: this source has not been passed to Lean. Its import
FourBody.CommonSeedGaps is an exact copy of seed-prep/CommonSeedGaps.lean,
which is itself still a static candidate. No main, branch, analytic IFT,
or arbitrary-sequence classification conclusion is assumed here.

RecoveryRectangle records only the three coordinate inputs which the
manuscript obtains by shortening its already constructed local branches.
They are outer gap >= gamma/2, absolute u/v bounds, and the retained
internal horizontal order. Later IFT work must derive these inputs on a
common interval; the present theorems are actual geometric implications
for Q_epsilon, and do not claim that any branch exists.
-/

noncomputable section
open scoped BigOperators
namespace FourBody

/-- A finite bound for an ACTUAL family of constrained coordinates on all
192 literal data. No compact parameter range or branch is postulated. -/
def finiteCoordinateBound {m : Masses}
    (h : ∀ d : OrderedClusterDatum, BlowupCoordinates m d) : ℝ :=
  1 + ∑ d : OrderedClusterDatum, ∑ i : Label, (|innerU (h d) i| + |innerV (h d) i|)

theorem finiteCoordinateBound_ge_one {m : Masses}
    (h : ∀ d : OrderedClusterDatum, BlowupCoordinates m d) :
    1 ≤ finiteCoordinateBound h := by
  have hsum : 0 ≤ ∑ d : OrderedClusterDatum,
      ∑ i : Label, (|innerU (h d) i| + |innerV (h d) i|) := by
    apply Finset.sum_nonneg
    intro d _
    apply Finset.sum_nonneg
    intro i _
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  unfold finiteCoordinateBound
  linarith

theorem finiteCoordinateBound_bounds {m : Masses}
    (h : ∀ d : OrderedClusterDatum, BlowupCoordinates m d)
    (d : OrderedClusterDatum) (i : Label) :
    |innerU (h d) i| + 1 ≤ finiteCoordinateBound h ∧
      |innerV (h d) i| + 1 ≤ finiteCoordinateBound h := by
  classical
  have hi : |innerU (h d) i| + |innerV (h d) i| ≤
      ∑ j : Label, (|innerU (h d) j| + |innerV (h d) j|) :=
    Finset.single_le_sum
      (fun j _ => add_nonneg (abs_nonneg (innerU (h d) j))
        (abs_nonneg (innerV (h d) j))) (Finset.mem_univ i)
  have hd : (∑ j : Label, (|innerU (h d) j| + |innerV (h d) j|)) ≤
      ∑ e : OrderedClusterDatum, ∑ j : Label,
        (|innerU (h e) j| + |innerV (h e) j|) := by
    apply Finset.single_le_sum _ (Finset.mem_univ d)
    intro e _
    exact Finset.sum_nonneg (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  unfold finiteCoordinateBound
  constructor <;> linarith [abs_nonneg (innerU (h d) i), abs_nonneg (innerV (h d) i)]

/-- This bound is mass-dependent and built from the actual unique seeds. -/
def commonSeedInnerBound {m : Masses} (hm : PositiveMasses m) : ℝ :=
  finiteCoordinateBound (seedCoordinates hm)

theorem commonSeedInnerBound_ge_one {m : Masses} (hm : PositiveMasses m) :
    1 ≤ commonSeedInnerBound hm :=
  finiteCoordinateBound_ge_one (seedCoordinates hm)

/-- Closed unit coordinate rectangles around every seed share one finite A. -/
theorem inner_bounds_near_seed {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (h : BlowupCoordinates m d)
    (hu : ∀ i, |innerU h i - innerU (seedCoordinates hm d) i| ≤ 1)
    (hv : ∀ i, |innerV h i - innerV (seedCoordinates hm d) i| ≤ 1) :
    (∀ i, |innerU h i| ≤ commonSeedInnerBound hm) ∧
      (∀ i, |innerV h i| ≤ commonSeedInnerBound hm) := by
  constructor
  · intro i
    have hs := (finiteCoordinateBound_bounds (seedCoordinates hm) d i).1
    have hseed : |innerU (seedCoordinates hm d) i| ≤ commonSeedInnerBound hm - 1 := by
      change |innerU (seedCoordinates hm d) i| ≤ finiteCoordinateBound (seedCoordinates hm) - 1
      linarith
    have hs' := abs_le.mp hseed
    have hn := abs_le.mp (hu i)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro i
    have hs := (finiteCoordinateBound_bounds (seedCoordinates hm) d i).2
    have hseed : |innerV (seedCoordinates hm d) i| ≤ commonSeedInnerBound hm - 1 := by
      change |innerV (seedCoordinates hm d) i| ≤ finiteCoordinateBound (seedCoordinates hm) - 1
      linarith
    have hs' := abs_le.mp hseed
    have hn := abs_le.mp (hv i)
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Exactly the geometric inputs of the manuscript's shortened neighborhoods. -/
structure RecoveryRectangle (m : Masses) (d : OrderedClusterDatum)
    (γ A : ℝ) (h : BlowupCoordinates m d) : Prop where
  outer_gap : ∀ a b : BlockIndex d, a < b → γ / 2 ≤ outerY h b - outerY h a
  inner_u : ∀ i : Label, |innerU h i| ≤ A
  inner_v : ∀ i : Label, |innerV h i| ≤ A
  inner_order : ∀ a : BlockIndex d,
    StrictMono (fun i : InternalIndex d a => innerU h (internalLabel d a i))

/-- The actual finite constants are valid at all the actual seed points,
including k=1, singleton blocks, and k=4. No cross-pair witness is required
for one datum with one block: its outer-gap condition is vacuous. -/
theorem seed_recoveryRectangle {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) :
    RecoveryRectangle m d (commonSeedGap hm) (commonSeedInnerBound hm)
      (seedCoordinates hm d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hab
    have hg := commonSeedGap_le hm d a b hab
    have hp := commonSeedGap_positive hm
    linarith
  · intro i
    have hb := (finiteCoordinateBound_bounds (seedCoordinates hm) d i).1
    change |innerU (seedCoordinates hm d) i| ≤ finiteCoordinateBound (seedCoordinates hm)
    linarith
  · intro i
    have hb := (finiteCoordinateBound_bounds (seedCoordinates hm) d i).2
    change |innerV (seedCoordinates hm d) i| ≤ finiteCoordinateBound (seedCoordinates hm)
    linarith
  · intro a
    exact ((seedCoordinates_isSeed hm d).2.2.2.2 a).1

/-- Literal small coordinate/seed comparisons which continuity at the
already proved actual seed can later supply. This records raw deviations,
not physical datum recovery, solution existence, or analytic regularity.
The internal comparison is required only for real ordered pairs, so it
has no hypothesis for a singleton block. -/
structure SeedComparisonBounds {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (h : BlowupCoordinates m d) : Prop where
  outer_near : ∀ a : BlockIndex d,
    |outerY h a - outerY (seedCoordinates hm d) a| ≤ commonSeedGap hm / 4
  inner_u_near : ∀ i : Label, |innerU h i - innerU (seedCoordinates hm d) i| ≤ 1
  inner_v_near : ∀ i : Label, |innerV h i - innerV (seedCoordinates hm d) i| ≤ 1
  inner_gap_near : ∀ (a : BlockIndex d) (i j : InternalIndex d a), i < j →
    |(innerU h (internalLabel d a j) - innerU h (internalLabel d a i)) -
      (innerU (seedCoordinates hm d) (internalLabel d a j) -
        innerU (seedCoordinates hm d) (internalLabel d a i))| <
      (innerU (seedCoordinates hm d) (internalLabel d a j) -
        innerU (seedCoordinates hm d) (internalLabel d a i)) / 2

/-- Strict outer and inner seed gaps give the recovery rectangle from raw
coordinate deviations. The retained-sign conclusion is proved here. -/
theorem recoveryRectangle_of_seedComparisons {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {h : BlowupCoordinates m d}
    (hn : SeedComparisonBounds hm d h) :
    RecoveryRectangle m d (commonSeedGap hm) (commonSeedInnerBound hm) h := by
  have hb := inner_bounds_near_seed hm h hn.inner_u_near hn.inner_v_near
  refine ⟨?_, hb.1, hb.2, ?_⟩
  · intro a b hab
    have hseed := commonSeedGap_le hm d a b hab
    have ha := abs_le.mp (hn.outer_near a)
    have hb := abs_le.mp (hn.outer_near b)
    linarith
  · intro a i j hij
    have hseed : innerU (seedCoordinates hm d) (internalLabel d a i) <
        innerU (seedCoordinates hm d) (internalLabel d a j) :=
      ((seedCoordinates_isSeed hm d).2.2.2.2 a).1 hij
    have hnear := abs_lt.mp (hn.inner_gap_near a i j hij)
    linarith

/-- These comparisons hold at every actual seed, with strict positive
internal margins, and include one-block and singleton cases uniformly. -/
theorem seed_seedComparisonBounds {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) : SeedComparisonBounds hm d (seedCoordinates hm d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    have hγ := commonSeedGap_positive hm
    simp only [sub_self, abs_zero]
    linarith
  · intro i
    simp
  · intro i
    simp
  · intro a i j hij
    have hseed := ((seedCoordinates_isSeed hm d).2.2.2.2 a).1 hij
    simp only [sub_self, abs_zero]
    linarith
def recoveryCut (γ : ℝ) : ℝ := γ / 8

/-- The two literal displayed inequalities in the Section 5 recovery proof. -/
def RecoverySmall (γ A ε : ℝ) : Prop :=
  2 * Real.sqrt 2 * A * ε < recoveryCut γ ∧ 2 * A * ε < γ / 4

/-- An explicit common positive upper threshold, independent of the datum. -/
def recoveryParameterBound (γ A : ℝ) : ℝ :=
  min (recoveryCut γ / (2 * Real.sqrt 2 * A)) (γ / (8 * A))

theorem recoveryParameterBound_pos {γ A : ℝ} (hγ : 0 < γ) (hA : 1 ≤ A) :
    0 < recoveryParameterBound γ A := by
  have hAp : 0 < A := by linarith
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hd : 0 < recoveryCut γ := by unfold recoveryCut; linarith
  exact lt_min (div_pos hd (by positivity)) (div_pos hγ (by positivity))

theorem recoverySmall_of_lt_bound {γ A ε : ℝ}
    (_hγ : 0 < γ) (hA : 1 ≤ A) (hε : ε < recoveryParameterBound γ A) :
    RecoverySmall γ A ε := by
  have hAp : 0 < A := by linarith
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hden₁ : 0 < 2 * Real.sqrt 2 * A := by positivity
  have hden₂ : 0 < 8 * A := by positivity
  have he₁ : ε < recoveryCut γ / (2 * Real.sqrt 2 * A) :=
    lt_of_lt_of_le hε (min_le_left _ _)
  have he₂ : ε < γ / (8 * A) :=
    lt_of_lt_of_le hε (min_le_right _ _)
  have hb₁ := (lt_div_iff₀ hden₁).mp he₁
  have hb₂ := (lt_div_iff₀ hden₂).mp he₂
  constructor
  · change 2 * Real.sqrt 2 * A * ε < recoveryCut γ
    nlinarith
  · nlinarith

private theorem point_distance_square (p t : Point) :
    dist p t ^ 2 = (p 0 - t 0) ^ 2 + (p 1 - t 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [Fin.sum_univ_two, Real.dist_eq]

private theorem bounded_difference_square {x y A : ℝ} (hA : 0 ≤ A)
    (hx : |x| ≤ A) (hy : |y| ≤ A) : (x - y) ^ 2 ≤ (2 * A) ^ 2 := by
  have hxb := abs_le.mp hx
  have hyb := abs_le.mp hy
  have hdiff : |x - y| ≤ 2 * A := abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    (x - y) ^ 2 = |x - y| ^ 2 := (sq_abs _).symm
    _ ≤ (2 * A) ^ 2 := (sq_le_sq₀ (abs_nonneg _) (by linarith)).mpr hdiff

/-- The actual two-dimensional Euclidean internal-pair estimate. The bound
uses the common cluster center cancelling in both physical coordinates. -/
theorem same_block_distance_le {m : Masses} {d : OrderedClusterDatum}
    {γ A ε : ℝ} {h : BlowupCoordinates m d} {q : Configuration}
    (hA : 1 ≤ A) (hε : 0 ≤ ε)
    (hr : RecoveryRectangle m d γ A h) (hq : RepresentsCoordinates m d ε h q)
    (a : BlockIndex d) (i j : Label)
    (hi : i ∈ datumBlock d a) (hj : j ∈ datumBlock d a) :
    dist (q i) (q j) ≤ 2 * Real.sqrt 2 * A * ε := by
  have hAp : 0 ≤ A := by linarith
  have hx : q i 0 - q j 0 = ε * (innerU h i - innerU h j) := by
    rw [hq a i hi, hq a j hj]
    change ε * outerH h a + ε * innerU h i -
      (ε * outerH h a + ε * innerU h j) = ε * (innerU h i - innerU h j)
    ring
  have hy : q i 1 - q j 1 = ε * (innerV h i - innerV h j) := by
    rw [hq a i hi, hq a j hj]
    change outerY h a + ε * innerV h i -
      (outerY h a + ε * innerV h j) = ε * (innerV h i - innerV h j)
    ring
  have hu := bounded_difference_square hAp (hr.inner_u i) (hr.inner_u j)
  have hv := bounded_difference_square hAp (hr.inner_v i) (hr.inner_v j)
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsquare : dist (q i) (q j) ^ 2 ≤ (2 * Real.sqrt 2 * A * ε) ^ 2 := by
    calc
      dist (q i) (q j) ^ 2 =
          ε ^ 2 * (innerU h i - innerU h j) ^ 2 +
            ε ^ 2 * (innerV h i - innerV h j) ^ 2 := by
        rw [point_distance_square, hx, hy]
        ring
      _ ≤ ε ^ 2 * (2 * A) ^ 2 + ε ^ 2 * (2 * A) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hu (sq_nonneg ε))
          (mul_le_mul_of_nonneg_left hv (sq_nonneg ε))
      _ = 4 * (Real.sqrt 2) ^ 2 * A ^ 2 * ε ^ 2 := by rw [hsqrt]; ring
      _ = (2 * Real.sqrt 2 * A * ε) ^ 2 := by ring
  exact (sq_le_sq₀ dist_nonneg (by positivity)).mp hsquare

/-- The literal vertical comparison y_j-y_i > gamma/4 for ordered blocks. -/
theorem cross_block_vertical_gap {m : Masses} {d : OrderedClusterDatum}
    {γ A ε : ℝ} {h : BlowupCoordinates m d} {q : Configuration}
    (hε : 0 ≤ ε) (hs : RecoverySmall γ A ε)
    (hr : RecoveryRectangle m d γ A h) (hq : RepresentsCoordinates m d ε h q)
    (a b : BlockIndex d) (hab : a < b) (i j : Label)
    (hi : i ∈ datumBlock d a) (hj : j ∈ datumBlock d b) :
    γ / 4 < q j 1 - q i 1 := by
  have hvi := abs_le.mp (hr.inner_v i)
  have hvj := abs_le.mp (hr.inner_v j)
  have hvdiff : -(2 * A) ≤ innerV h j - innerV h i := by linarith
  have he := mul_le_mul_of_nonneg_left hvdiff hε
  have hgap := hr.outer_gap a b hab
  have hy : q j 1 - q i 1 = outerY h b - outerY h a +
      ε * (innerV h j - innerV h i) := by
    rw [hq b j hj, hq a i hi]
    change outerY h b + ε * innerV h j -
      (outerY h a + ε * innerV h i) = _
    ring
  rw [hy]
  have hsmall := hs.2
  linarith

theorem cross_block_distance_gt_cut {m : Masses} {d : OrderedClusterDatum}
    {γ A ε : ℝ} {h : BlowupCoordinates m d} {q : Configuration}
    (hγ : 0 < γ) (hε : 0 ≤ ε) (hs : RecoverySmall γ A ε)
    (hr : RecoveryRectangle m d γ A h) (hq : RepresentsCoordinates m d ε h q)
    (a b : BlockIndex d) (hab : a < b) (i j : Label)
    (hi : i ∈ datumBlock d a) (hj : j ∈ datumBlock d b) :
    recoveryCut γ < dist (q i) (q j) := by
  have hgap := cross_block_vertical_gap hε hs hr hq a b hab i j hi hj
  have hcoord : |q j 1 - q i 1| ≤ dist (q i) (q j) := by
    simpa only [Real.dist_eq, dist_comm (q j) (q i)] using
      (PiLp.dist_apply_le (q j) (q i) (1 : Axis))
  have hcut : recoveryCut γ < q j 1 - q i 1 := by
    unfold recoveryCut
    linarith
  exact hcut.trans_le ((le_abs_self _).trans hcoord)

/-- A physical relation on literal labels; it never quotients configurations.
The statement includes equal labels, so it is a reflexive block relation. -/
def DistanceRecoversBlocks (d : OrderedClusterDatum) (q : Configuration) (cut : ℝ) : Prop :=
  ∀ i j : Label, dist (q i) (q j) < cut ↔ blockOf d i = blockOf d j

/-- Section 5's actual '< d iff same block', proved from the coordinate
rectangle. No solution equation or analytic branch theorem is needed. -/
theorem distance_recovers_blocks {m : Masses} {d : OrderedClusterDatum}
    {γ A ε : ℝ} {h : BlowupCoordinates m d} {q : Configuration}
    (hγ : 0 < γ) (hA : 1 ≤ A) (hε : 0 ≤ ε)
    (hs : RecoverySmall γ A ε) (hr : RecoveryRectangle m d γ A h)
    (hq : RepresentsCoordinates m d ε h q) :
    DistanceRecoversBlocks d q (recoveryCut γ) := by
  intro i j
  constructor
  · intro hd
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hgt := cross_block_distance_gt_cut hγ hε hs hr hq
        (blockOf d i) (blockOf d j) hij i j (label_mem_blockOf d i) (label_mem_blockOf d j)
      linarith
    · have hgt := cross_block_distance_gt_cut hγ hε hs hr hq
        (blockOf d j) (blockOf d i) hji j i (label_mem_blockOf d j) (label_mem_blockOf d i)
      rw [dist_comm] at hgt
      linarith
  · intro hij
    have hj : j ∈ datumBlock d (blockOf d i) := by
      rw [hij]
      exact label_mem_blockOf d j
    exact (same_block_distance_le hA hε hr hq (blockOf d i) i j
      (label_mem_blockOf d i) hj).trans_lt hs.1

/-- Actual block barycenter heights are strictly ordered, not abstract Y tags. -/
theorem recovery_barycenter_heights_strictMono {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {γ A ε : ℝ} {h : BlowupCoordinates m d}
    {q : Configuration} (hγ : 0 < γ)
    (hr : RecoveryRectangle m d γ A h) (hq : RepresentsCoordinates m d ε h q) :
    StrictMono (fun a : BlockIndex d => datumBlockMean m d q a 1) := by
  have heq := (represents_iff_eq_physicalCoordinates ε h q).mp hq
  intro a b hab
  change datumBlockMean m d q a 1 < datumBlockMean m d q b 1
  rw [heq, datumBlockMean_physicalCoordinates hm, datumBlockMean_physicalCoordinates hm]
  change outerY h a < outerY h b
  have hgap := hr.outer_gap a b hab
  linarith

/-- The prescribed order in each ACTUAL list is the physical x order. -/
theorem recovery_internal_horizontal_strictMono {m : Masses} {d : OrderedClusterDatum}
    {γ A ε : ℝ} {h : BlowupCoordinates m d} {q : Configuration}
    (hε : 0 < ε) (hr : RecoveryRectangle m d γ A h)
    (hq : RepresentsCoordinates m d ε h q) (a : BlockIndex d) :
    StrictMono (fun i : InternalIndex d a => q (internalLabel d a i) 0) := by
  intro i j hij
  change q (internalLabel d a i) 0 < q (internalLabel d a j) 0
  rw [hq a (internalLabel d a i) (internalLabel_mem d a i),
    hq a (internalLabel d a j) (internalLabel_mem d a j)]
  change ε * outerH h a + ε * innerU h (internalLabel d a i) <
    ε * outerH h a + ε * innerU h (internalLabel d a j)
  have hmul := mul_lt_mul_of_pos_left (hr.inner_order a hij) hε
  linarith

end FourBody

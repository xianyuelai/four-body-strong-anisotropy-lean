import FourBody.InternalScaleBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Abel

/-!
# Concrete scaled internal mass-mean identities and bounds

Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD,
eq:sequence-coordinates and lines 441--446.
Every scalar denominator is the actual positive block mass. The global
bound is DERIVED from InternalScale.eventually_all_internal_scaled on
original solutions, not introduced as a certificate or main hypothesis.
All new proof bodies and the TwoScale dependency are still uncompiled.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace FourBody.InternalCoordinates

/-- Every actual label uses its proved unique actual block. -/
def internalVectors (m : Masses) (d : OrderedClusterDatum) (ε : ℝ)
    (q : Configuration) : Label → Point :=
  fun i => internalVectorCoordinate m d ε q (blockOf d i) i

theorem internalVectors_apply_of_mem (m : Masses) (d : OrderedClusterDatum) (ε : ℝ)
    (q : Configuration) {a : BlockIndex d} {i : Label} (hi : i ∈ datumBlock d a) :
    internalVectors m d ε q i = internalVectorCoordinate m d ε q a i := by
  simp only [internalVectors, blockOf_eq_of_mem d hi]

theorem normalized_block_weights_sum {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (a : BlockIndex d) :
    (∑ j ∈ datumBlockLabels d a, m j / datumBlockMass m d a) = 1 := by
  rw [← Finset.sum_div]
  change datumBlockMass m d a / datumBlockMass m d a = 1
  exact div_self (datumBlockMass_ne_zero hm d a)

theorem datumBlockMean_eq_weighted_sum (m : Masses) (d : OrderedClusterDatum)
    (q : Configuration) (a : BlockIndex d) :
    datumBlockMean m d q a =
      ∑ j ∈ datumBlockLabels d a, (m j / datumBlockMass m d a) • q j := by
  rw [datumBlockMean, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [smul_smul, div_eq_mul_inv, mul_comm]

/-- The exact paper identity holds algebraically even for totalized ε=0.
Physical norm and distance claims below require ε>0. -/
theorem internalVector_mean_difference {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (ε : ℝ) (q : Configuration)
    (a : BlockIndex d) (i : Label) :
    internalVectorCoordinate m d ε q a i =
      ∑ j ∈ datumBlockLabels d a, (m j / datumBlockMass m d a) •
        (ε⁻¹ • (q i - q j)) := by
  have hdiff :
      (∑ j ∈ datumBlockLabels d a, (m j / datumBlockMass m d a) • (q i - q j)) =
        q i - datumBlockMean m d q a := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, normalized_block_weights_sum hm,
      one_smul, ← datumBlockMean_eq_weighted_sum]
  rw [internalVectorCoordinate, ← hdiff, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  exact smul_comm _ _ _

/-- Elementary finite estimate, subsequently discharged by the actual
derived internal pair bounds. It is not a compactness or analysis interface. -/
theorem internalVector_norm_le_of_pair_bound {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) {ε : ℝ} (hε : 0 < ε) (q : Configuration)
    (a : BlockIndex d) (i : Label) (C : ℝ)
    (hpair : ∀ j ∈ datumBlockLabels d a, dist (q i) (q j) ≤ C * ε) :
    ‖internalVectorCoordinate m d ε q a i‖ ≤ C := by
  have hscaled : ∀ j ∈ datumBlockLabels d a, ‖ε⁻¹ • (q i - q j)‖ ≤ C := by
    intro j hj
    calc
      ‖ε⁻¹ • (q i - q j)‖ = dist (q i) (q j) / ε := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε, ← dist_eq_norm]
        ring
      _ ≤ C := (div_le_iff₀ hε).mpr (hpair j hj)
  calc
    ‖internalVectorCoordinate m d ε q a i‖ =
        ‖∑ j ∈ datumBlockLabels d a, (m j / datumBlockMass m d a) •
          (ε⁻¹ • (q i - q j))‖ := by rw [internalVector_mean_difference hm]
    _ ≤ ∑ j ∈ datumBlockLabels d a, ‖(m j / datumBlockMass m d a) •
        (ε⁻¹ • (q i - q j))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ datumBlockLabels d a, (m j / datumBlockMass m d a) * C := by
      apply Finset.sum_le_sum
      intro j hj
      have hw : 0 ≤ m j / datumBlockMass m d a :=
        div_nonneg (hm j).le (datumBlockMass_pos hm d a).le
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (hscaled j hj) hw
    _ = C := by
      rw [← Finset.sum_mul, normalized_block_weights_sum hm, one_mul]

/-- The singleton case is an exact zero, without any limiting argument. -/
theorem internalVector_eq_zero_of_singleton {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (ε : ℝ) (q : Configuration)
    (a : BlockIndex d) (i : Label) (hblock : datumBlock d a = [i]) :
    internalVectorCoordinate m d ε q a i = 0 := by
  have hmean : datumBlockMean m d q a = q i := by
    rw [datumBlockMean_eq_weighted_sum]
    simp [datumBlockLabels, datumBlockMass, hblock, ne_of_gt (hm i)]
  rw [internalVectorCoordinate, hmean, sub_self, smul_zero]

/-- Exact internal weighted centering in the physical two-dimensional space. -/
theorem internalVectors_center_zero {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (ε : ℝ) (q : Configuration) (a : BlockIndex d) :
    (∑ i ∈ datumBlockLabels d a, m i • internalVectorCoordinate m d ε q a i) = 0 := by
  ext k
  simp only [internalVectorCoordinate, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, PiLp.sub_apply, PiLp.zero_apply, smul_eq_mul]
  calc
    (∑ i ∈ datumBlockLabels d a,
        m i * (ε⁻¹ * (q i k - datumBlockMean m d q a k))) =
        ∑ i ∈ datumBlockLabels d a,
          ε⁻¹ * (m i * q i k - m i * datumBlockMean m d q a k) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = ε⁻¹ * ((∑ i ∈ datumBlockLabels d a, m i * q i k) -
        datumBlockMass m d a * datumBlockMean m d q a k) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul]
      rfl
    _ = 0 := by rw [block_mass_mul_mean hm, sub_self, mul_zero]

/-- The same-block affine centers cancel in actual Euclidean distance. -/
theorem internalVectors_dist_of_mem (m : Masses) (d : OrderedClusterDatum)
    {ε : ℝ} (hε : 0 < ε) (q : Configuration)
    {a : BlockIndex d} {i j : Label} (hi : i ∈ datumBlock d a) (hj : j ∈ datumBlock d a) :
    dist (internalVectors m d ε q i) (internalVectors m d ε q j) =
      dist (q i) (q j) / ε := by
  calc
    dist (internalVectors m d ε q i) (internalVectors m d ε q j) =
        ‖ε⁻¹ • (q i - q j)‖ := by
      rw [dist_eq_norm, internalVectors_apply_of_mem m d _ q hi,
        internalVectors_apply_of_mem m d _ q hj]
      unfold internalVectorCoordinate
      rw [← smul_sub]
      congr 1
      abel
    _ = dist (q i) (q j) / ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε, ← dist_eq_norm]
      ring

/-- The source's common C controls ALL four actual internal vectors
eventually. This theorem takes only actual original solutions and the
previously derived initial limit, and DISCHARGES every pair bound. -/
theorem eventually_internal_vectors_bound {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    (hq : ∀ ν, IsSolution m (s ν) (q ν))
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y) :
    ∀ᶠ ν in atTop, ∀ i : Label,
      ‖internalVectors m (VerticalPartition.verticalPartitionDatum y)
        (epsilon (s (φ ν))) (q (φ ν)) i‖ ≤ ScaleConstants.C m := by
  have hC : 0 < ScaleConstants.C m := (ScaleConstants.constants_positive m hm).2.2.2
  filter_upwards [InternalScale.eventually_all_internal_scaled hm hq hlim] with ν hν
  intro i
  let d := VerticalPartition.verticalPartitionDatum y
  let a : BlockIndex d := blockOf d i
  have hi : i ∈ datumBlock d a := label_mem_blockOf d i
  have hε : 0 < epsilon (s (φ ν)) := hlim.2.2.2.1 ν
  apply internalVector_norm_le_of_pair_bound hm d hε (q (φ ν)) a i (ScaleConstants.C m)
  intro j hj
  have hj' : j ∈ datumBlock d a := by simpa only [datumBlockLabels, List.mem_toFinset] using hj
  by_cases hij : i = j
  · subst j
    simpa only [dist_self] using mul_nonneg hC.le hε.le
  · exact (hν a i j hi hj' hij).2.le

end FourBody.InternalCoordinates


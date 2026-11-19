import FourBody.NewtonFieldLimits

/-!
# Uniform actual exterior Point-field bounds on the selected sequence

Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD,
lines 467--469. The source's common cross distance δ is constructed by
CrossSeparation. Exact physical pair norms are m_j/r², giving the actual
Euclidean bound M/δ² for all four exterior fields and every mass mean.
Singleton and one-block cases need no cross pair; empty sums are handled
by the literal conditional finite field. All new bodies uncompiled.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace FourBody.ExternalNormBounds

theorem physicalNewtonForce_norm {μ : ℝ} (hμ : 0 ≤ μ) (a b : Point)
    (hd : 0 < dist b a) :
    ‖Reuse.physicalNewtonForce μ a b‖ = μ / dist b a ^ 2 := by
  have hcoeff : 0 ≤ μ / dist b a ^ 3 := div_nonneg hμ (pow_pos hd 3).le
  rw [Reuse.physicalNewtonForce, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hcoeff, ← dist_eq_norm]
  field_simp [ne_of_gt hd]

theorem physicalNewtonForce_norm_le {μ δ : ℝ} (hμ : 0 ≤ μ)
    (a b : Point) (hδ : 0 < δ) (hsep : δ ≤ dist b a) :
    ‖Reuse.physicalNewtonForce μ a b‖ ≤ μ / δ ^ 2 := by
  rw [physicalNewtonForce_norm hμ a b (hδ.trans_le hsep)]
  exact div_le_div_of_nonneg_left hμ (pow_pos hδ 2)
    (pow_le_pow_left₀ hδ.le hsep 2)

theorem actual_external_norm_bound {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (q : Configuration) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j : Label, blockOf d i ≠ blockOf d j → δ ≤ dist (q i) (q j))
    (i : Label) :
    ‖NewtonFieldLimits.physicalExternalField m d q i‖ ≤ totalMass m / δ ^ 2 := by
  classical
  unfold NewtonFieldLimits.physicalExternalField
  calc
    ‖∑ j : Label, if blockOf d j ≠ blockOf d i then
        Reuse.physicalNewtonForce (m j) (q j) (q i) else 0‖ ≤
        ∑ j : Label, ‖if blockOf d j ≠ blockOf d i then
          Reuse.physicalNewtonForce (m j) (q j) (q i) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ j : Label, m j / δ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _hj
      by_cases hblock : blockOf d j ≠ blockOf d i
      · simp only [if_pos hblock]
        exact physicalNewtonForce_norm_le (hm j).le
          (q j) (q i) hδ (hsep i j (Ne.symm hblock))
      · simp only [hblock, if_false, norm_zero]
        exact div_nonneg (hm j).le (pow_pos hδ 2).le
    _ = totalMass m / δ ^ 2 := by rw [← Finset.sum_div]; rfl

/-- Actual positive weighted means preserve a uniform Euclidean norm
bound. The normalized weights sum to 1 by the literal block mass. -/
theorem actual_block_mean_norm_bound {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (field : Configuration) (a : BlockIndex d)
    (K : ℝ) (hfield : ∀ i : Label, ‖field i‖ ≤ K) :
    ‖datumBlockMean m d field a‖ ≤ K := by
  rw [InternalCoordinates.datumBlockMean_eq_weighted_sum]
  calc
    ‖∑ i ∈ datumBlockLabels d a, (m i / datumBlockMass m d a) • field i‖ ≤
        ∑ i ∈ datumBlockLabels d a, ‖(m i / datumBlockMass m d a) • field i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ datumBlockLabels d a, (m i / datumBlockMass m d a) * K := by
      apply Finset.sum_le_sum
      intro i _hi
      have hw : 0 ≤ m i / datumBlockMass m d a :=
        div_nonneg (hm i).le (datumBlockMass_pos hm d a).le
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (hfield i) hw
    _ = K := by
      rw [← Finset.sum_mul, InternalCoordinates.normalized_block_weights_sum hm, one_mul]

/-- δ and the common all-field/all-mean bound are DERIVED from the actual
initial limit. They are not supplied as an analytic interface. -/
theorem exists_actual_eventual_external_norm_bound {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ν in atTop,
      (∀ i : Label, ‖NewtonFieldLimits.physicalExternalField m
        (VerticalPartition.verticalPartitionDatum y) (q (φ ν)) i‖ ≤ totalMass m / δ ^ 2) ∧
      (∀ a : BlockIndex (VerticalPartition.verticalPartitionDatum y),
        ‖NewtonFieldLimits.physicalExternalMean m (VerticalPartition.verticalPartitionDatum y)
          (q (φ ν)) a‖ ≤ totalMass m / δ ^ 2) := by
  obtain ⟨δ, hδ, hsep⟩ := CrossSeparation.exists_eventual_cross_separation hlim
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hsep] with ν hν
  have hfield := fun i => actual_external_norm_bound hm
    (VerticalPartition.verticalPartitionDatum y) (q (φ ν)) hδ hν i
  refine ⟨hfield, ?_⟩
  intro a
  exact actual_block_mean_norm_bound hm _ _ a _ hfield

end FourBody.ExternalNormBounds

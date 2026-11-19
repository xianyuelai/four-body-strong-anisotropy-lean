import FourBody.InternalHorizontalLimit

/-!
# Exact finite regrouping into the two one-dimensional seed equations

Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
The outer finite physical field is regrouped by the ACTUAL disjoint label
blocks and their actual positive masses. For the inner equation, the
ACTUAL Euclidean distance at vertical-zero points is |u_i-u_j| and the
same erased finite-sum reindexing preserves every physical label.
The internal equations below are true in the provisional natural-label
order; they do NOT yet claim StrictMono in that order. All bodies are
uncompiled candidates.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace FourBody.ScalarLimitEquations

theorem vertical_pair_component (m : Masses) (y : Label → ℝ) (i j : Label) :
    Reuse.physicalNewtonForce (m j)
      (NewtonFieldLimits.initialVerticalConfiguration y j)
      (NewtonFieldLimits.initialVerticalConfiguration y i) 1 =
      m j * (y i - y j) / |y i - y j| ^ 3 := by
  rw [Reuse.physicalNewtonForce, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul]
  change (m j / dist (SequencePointLimits.verticalPoint (y i))
      (SequencePointLimits.verticalPoint (y j)) ^ 3) * (y i - y j) =
    m j * (y i - y j) / |y i - y j| ^ 3
  rw [SequencePointLimits.verticalPoint_dist]
  ring

/-- The sum over all labels is regrouped using the proved actual block
partition. No outer force identity is an assumption. -/
theorem external_vertical_eq_outer_force (m : Masses) (y : Label → ℝ)
    (a : BlockIndex (VerticalPartition.verticalPartitionDatum y))
    {i : Label} (hi : i ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) a) :
    NewtonFieldLimits.physicalExternalField m (VerticalPartition.verticalPartitionDatum y)
      (NewtonFieldLimits.initialVerticalConfiguration y) i 1 =
      oneDimensionalForce (datumBlockMass m (VerticalPartition.verticalPartitionDatum y))
        (VerticalPartition.verticalHeight y) a := by
  classical
  let d := VerticalPartition.verticalPartitionDatum y
  let Y := VerticalPartition.verticalHeight y
  have hia : blockOf d i = a := blockOf_eq_of_mem d hi
  have hyi : y i = Y a := (VerticalPartition.mem_datumBlock_iff_height y a i).mp hi
  let f : Label → ℝ := fun j => if blockOf d j ≠ blockOf d i then
    Reuse.physicalNewtonForce (m j) (NewtonFieldLimits.initialVerticalConfiguration y j)
      (NewtonFieldLimits.initialVerticalConfiguration y i) 1 else 0
  have hcoord : NewtonFieldLimits.physicalExternalField m d
      (NewtonFieldLimits.initialVerticalConfiguration y) i 1 = ∑ j : Label, f j := by
    simp only [NewtonFieldLimits.physicalExternalField, WithLp.ofLp_sum,
      Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _hj
    dsimp [f]
    split_ifs <;> rfl
  have hblock : ∀ b : BlockIndex d,
      (∑ j ∈ datumBlockLabels d b, f j) =
        if b ≠ a then datumBlockMass m d b * (Y a - Y b) / |Y a - Y b| ^ 3 else 0 := by
    intro b
    by_cases hba : b ≠ a
    · rw [if_pos hba]
      calc
        (∑ j ∈ datumBlockLabels d b, f j) =
            ∑ j ∈ datumBlockLabels d b, m j * (Y a - Y b) / |Y a - Y b| ^ 3 := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjmem : j ∈ datumBlock d b := by
            simpa only [datumBlockLabels, List.mem_toFinset] using hj
          have hjb : blockOf d j = b := blockOf_eq_of_mem d hjmem
          have hyj : y j = Y b := (VerticalPartition.mem_datumBlock_iff_height y b j).mp hjmem
          dsimp [f]
          rw [hjb, hia, if_pos hba, vertical_pair_component, hyi, hyj]
        _ = datumBlockMass m d b * (Y a - Y b) / |Y a - Y b| ^ 3 := by
          rw [← Finset.sum_div, ← Finset.sum_mul]
          rfl
    · rw [if_neg hba]
      apply Finset.sum_eq_zero
      intro j hj
      have hjmem : j ∈ datumBlock d b := by
        simpa only [datumBlockLabels, List.mem_toFinset] using hj
      dsimp [f]
      rw [blockOf_eq_of_mem d hjmem, hia, if_neg hba]
  rw [hcoord, ← sum_datumBlocks d f]
  simp_rw [hblock]
  change (∑ b : BlockIndex d,
      if b ≠ a then datumBlockMass m d b * (Y a - Y b) / |Y a - Y b| ^ 3 else 0) =
    ∑ b ∈ (Finset.univ : Finset (BlockIndex d)).erase a,
      datumBlockMass m d b * (Y a - Y b) / |Y a - Y b| ^ 3
  have hdiag : datumBlockMass m d a * (Y a - Y a) / |Y a - Y a| ^ 3 = 0 := by simp
  rw [Finset.sum_erase (Finset.univ : Finset (BlockIndex d))
    (f := fun b => datumBlockMass m d b * (Y a - Y b) / |Y a - Y b| ^ 3)
    (a := a) hdiag]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hba : b ≠ a
  · simp only [if_pos hba]
  · have heq : b = a := not_ne_iff.mp hba
    subst b
    simp

/-- Positive mass-averaging of the block-constant exterior limit preserves
the exact outer force. The mass divisor is proved nonzero. -/
theorem external_mean_vertical_eq_outer_force {m : Masses} (hm : PositiveMasses m)
    (y : Label → ℝ) (a : BlockIndex (VerticalPartition.verticalPartitionDatum y)) :
    NewtonFieldLimits.physicalExternalMean m (VerticalPartition.verticalPartitionDatum y)
      (NewtonFieldLimits.initialVerticalConfiguration y) a 1 =
      oneDimensionalForce (datumBlockMass m (VerticalPartition.verticalPartitionDatum y))
        (VerticalPartition.verticalHeight y) a := by
  classical
  rw [NewtonFieldLimits.physicalExternalMean, datumBlockMean_apply]
  have hsum : (∑ i ∈ datumBlockLabels (VerticalPartition.verticalPartitionDatum y) a,
      m i * NewtonFieldLimits.physicalExternalField m (VerticalPartition.verticalPartitionDatum y)
        (NewtonFieldLimits.initialVerticalConfiguration y) i 1) =
      datumBlockMass m (VerticalPartition.verticalPartitionDatum y) a *
        oneDimensionalForce (datumBlockMass m (VerticalPartition.verticalPartitionDatum y))
          (VerticalPartition.verticalHeight y) a := by
    calc
      _ = ∑ i ∈ datumBlockLabels (VerticalPartition.verticalPartitionDatum y) a,
          m i * oneDimensionalForce (datumBlockMass m (VerticalPartition.verticalPartitionDatum y))
            (VerticalPartition.verticalHeight y) a := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [external_vertical_eq_outer_force m y a
          (by simpa only [datumBlockLabels, List.mem_toFinset] using hi)]
      _ = _ := by rw [← Finset.sum_mul]; rfl
  rw [hsum, ← mul_assoc, inv_mul_cancel₀ (datumBlockMass_ne_zero hm _ a), one_mul]

theorem outer_height_is_oneDimensionalSolution {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    (hq : ∀ ν, IsSolution m (s ν) (q ν))
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y) :
    OneDimensionalSolution (datumBlockMass m (VerticalPartition.verticalPartitionDatum y))
      (VerticalPartition.verticalHeight y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    exact fun h => hab ((VerticalPartition.verticalHeight_strictMono y).injective h)
  · exact VerticalPartition.vertical_group_center_zero m hlim.2.2.2.2.2.2.2.2
  · intro a
    rw [← external_mean_vertical_eq_outer_force hm]
    exact InternalEquationLimits.outer_mean_limit_equation hm hq hlim a

theorem point_dist_eq_abs_horizontal {p r : Point} (hp : p 1 = 0) (hr : r 1 = 0) :
    dist p r = |p 0 - r 0| := by
  simp [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, hp, hr,
    Real.sqrt_sq_eq_abs]

theorem indexed_horizontal_force_eq_actual_internal_field (m : Masses)
    (d : OrderedClusterDatum) (P : Configuration) (hv : ∀ i : Label, P i 1 = 0)
    (a : BlockIndex d) (j : InternalIndex d a) :
    oneDimensionalForce (fun k => m (internalLabel d a k))
      (fun k => P (internalLabel d a k) 0) j =
      NewtonFieldLimits.physicalInternalField m d P (internalLabel d a j) 0 := by
  classical
  rw [oneDimensionalForce, SequenceBlockIndices.sum_erase_internalLabels d a j
    (fun i => m i * (P (internalLabel d a j) 0 - P i 0) /
      |P (internalLabel d a j) 0 - P i 0| ^ 3)]
  rw [NewtonFieldLimits.physicalInternalField,
    blockOf_eq_of_mem d (SequenceBlockIndices.internalLabel_mem d a j)]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, Reuse.physicalNewtonForce,
    PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [point_dist_eq_abs_horizontal (hv _) (hv _)]
  ring

/-- Literal inner one-dimensional equations, still in the provisional
natural-label list. Sorting that list is a separate representation task. -/
theorem internal_limit_is_oneDimensionalSolution {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    {P₀ : Configuration}
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀)
    (heq : InternalEquationLimits.InternalEquationAtLimit m y P₀)
    (a : BlockIndex (VerticalPartition.verticalPartitionDatum y)) :
    OneDimensionalSolution
      (fun j => m (internalLabel (VerticalPartition.verticalPartitionDatum y) a j))
      (fun j => P₀ (internalLabel (VerticalPartition.verticalPartitionDatum y) a j) 0) := by
  have hv := InternalHorizontalLimit.internal_limit_vertical_zero hm hdata heq
  refine ⟨?_, ?_, ?_⟩
  · intro j k hjk
    exact fun h => hjk (InternalHorizontalLimit.internal_limit_horizontal_injective hm hdata heq a h)
  · exact SequenceBlockIndices.indexed_coordinate_center_zero m _ P₀ a 0 (hdata.2.2.1 a)
  · intro j
    rw [indexed_horizontal_force_eq_actual_internal_field m _ P₀ hv]
    exact (heq (internalLabel (VerticalPartition.verticalPartitionDatum y) a j)).1

/-- Both one-dimensional equations follow from arbitrary original solution
inputs. Every intermediate limit and force equation is constructed. -/
theorem exists_scalar_equation_limits {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration}
    (hs : Tendsto s atTop atTop) (hq : ∀ ν, IsSolution m (s ν) (q ν)) :
    ∃ φ : ℕ → ℕ, ∃ y : Label → ℝ, ∃ P₀ : Configuration,
      SequenceStart.InitialVerticalLimit m s q φ y ∧
      InternalSubsequence.InternalLimitData m s q φ y P₀ ∧
      InternalEquationLimits.InternalEquationAtLimit m y P₀ ∧
      (∀ i : Label, P₀ i 1 = 0) ∧
      OneDimensionalSolution (datumBlockMass m (VerticalPartition.verticalPartitionDatum y))
        (VerticalPartition.verticalHeight y) ∧
      (∀ a : BlockIndex (VerticalPartition.verticalPartitionDatum y),
        OneDimensionalSolution
          (fun j => m (internalLabel (VerticalPartition.verticalPartitionDatum y) a j))
          (fun j => P₀ (internalLabel (VerticalPartition.verticalPartitionDatum y) a j) 0)) := by
  obtain ⟨φ, y, P₀, hlim, hdata, heq, _houter⟩ :=
    InternalEquationLimits.exists_internal_equation_limit hm hs hq
  exact ⟨φ, y, P₀, hlim, hdata, heq,
    InternalHorizontalLimit.internal_limit_vertical_zero hm hdata heq,
    outer_height_is_oneDimensionalSolution hm hq hlim,
    internal_limit_is_oneDimensionalSolution hm hdata heq⟩

end FourBody.ScalarLimitEquations

import FourBody.NaturalOrderLimitCoordinates
import FourBody.FiniteHorizontalSort

/-!
# The actual final datum and seed obtained by sorting the limiting u values

Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
FiniteHorizontalSort sorts each ACTUAL label list, preserving its labels,
masses, means, and its outer height position. The within-block injection
required by the sort is derived from the actual separated horizontal
limit, not supplied as a seed assumption. The finite force reindexing and
coordinate constraints are proved below. All bodies remain uncompiled.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace FourBody.ReorderedLimitCoordinates

def finalDatum (y : Label → ℝ) (P₀ : Configuration) : OrderedClusterDatum :=
  FiniteHorizontalSort.reorderedDatum (VerticalPartition.verticalPartitionDatum y)
    (fun i => P₀ i 0)

def oldIndex (y : Label → ℝ) (P₀ : Configuration) :
    BlockIndex (finalDatum y P₀) ≃ BlockIndex (VerticalPartition.verticalPartitionDatum y) :=
  FiniteHorizontalSort.oldIndex (VerticalPartition.verticalPartitionDatum y) (fun i => P₀ i 0)

def finalHeight (y : Label → ℝ) (P₀ : Configuration) :
    BlockIndex (finalDatum y P₀) → ℝ :=
  fun a => VerticalPartition.verticalHeight y (oldIndex y P₀ a)

theorem final_block_mem_iff (y : Label → ℝ) (P₀ : Configuration)
    (a : BlockIndex (finalDatum y P₀)) (i : Label) :
    i ∈ datumBlock (finalDatum y P₀) a ↔
      i ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) (oldIndex y P₀ a) :=
  FiniteHorizontalSort.mem_datumBlock_iff _ _ a i

theorem final_block_labels_eq (y : Label → ℝ) (P₀ : Configuration)
    (a : BlockIndex (finalDatum y P₀)) :
    datumBlockLabels (finalDatum y P₀) a =
      datumBlockLabels (VerticalPartition.verticalPartitionDatum y) (oldIndex y P₀ a) :=
  FiniteHorizontalSort.datumBlockLabels_eq _ _ a

theorem final_block_mass_eq (m : Masses) (y : Label → ℝ) (P₀ : Configuration)
    (a : BlockIndex (finalDatum y P₀)) :
    datumBlockMass m (finalDatum y P₀) a =
      datumBlockMass m (VerticalPartition.verticalPartitionDatum y) (oldIndex y P₀ a) :=
  FiniteHorizontalSort.datumBlockMass_eq m _ _ a

theorem final_block_mean_eq (m : Masses) (y : Label → ℝ) (P₀ : Configuration)
    (q : Configuration) (a : BlockIndex (finalDatum y P₀)) :
    datumBlockMean m (finalDatum y P₀) q a =
      datumBlockMean m (VerticalPartition.verticalPartitionDatum y) q (oldIndex y P₀ a) :=
  FiniteHorizontalSort.datumBlockMean_eq m _ _ q a

theorem final_blockOf_to_old (y : Label → ℝ) (P₀ : Configuration) (i : Label) :
    oldIndex y P₀ (blockOf (finalDatum y P₀) i) =
      blockOf (VerticalPartition.verticalPartitionDatum y) i :=
  FiniteHorizontalSort.blockOf_new_to_old _ _ i

theorem finalHeight_strictMono (y : Label → ℝ) (P₀ : Configuration) :
    StrictMono (finalHeight y P₀) :=
  (VerticalPartition.verticalHeight_strictMono y).comp
    (FiniteHorizontalSort.oldIndex_strictMono _ _)

theorem final_height_center_zero (m : Masses) {y : Label → ℝ} (P₀ : Configuration)
    (hy : (∑ i, m i * y i) = 0) :
    (∑ a : BlockIndex (finalDatum y P₀), datumBlockMass m (finalDatum y P₀) a *
      finalHeight y P₀ a) = 0 := by
  calc
    _ = ∑ a : BlockIndex (VerticalPartition.verticalPartitionDatum y),
        datumBlockMass m (VerticalPartition.verticalPartitionDatum y) a *
          VerticalPartition.verticalHeight y a := by
      apply Fintype.sum_equiv (oldIndex y P₀)
      intro a
      rw [final_block_mass_eq]
      rfl
    _ = 0 := VerticalPartition.vertical_group_center_zero m hy

theorem final_internal_center_zero {m : Masses} {s : ℕ → ℝ} {q : ℕ → Configuration}
    {φ : ℕ → ℕ} {y : Label → ℝ} {P₀ : Configuration}
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀)
    (a : BlockIndex (finalDatum y P₀)) :
    (∑ i ∈ datumBlockLabels (finalDatum y P₀) a, m i • P₀ i) = 0 := by
  rw [final_block_labels_eq]
  exact hdata.2.2.1 (oldIndex y P₀ a)

theorem horizontal_label_injective_on_block {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    {P₀ : Configuration}
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀)
    (heq : InternalEquationLimits.InternalEquationAtLimit m y P₀)
    (a : BlockIndex (VerticalPartition.verticalPartitionDatum y)) {i j : Label}
    (hi : i ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) a)
    (hj : j ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) a)
    (hu : P₀ i 0 = P₀ j 0) : i = j := by
  by_contra hij
  have hv := InternalHorizontalLimit.internal_limit_vertical_zero hm hdata heq
  have hpoint : P₀ i = P₀ j := by
    ext k
    fin_cases k
    · exact hu
    · change P₀ i 1 = P₀ j 1
      rw [hv i, hv j]
  have hd : 0 < dist (P₀ i) (P₀ j) :=
    ((ScaleConstants.constants_positive m hm).2.1).trans_le (hdata.2.2.2 a i j hi hj hij)
  simp only [hpoint, dist_self, lt_self_iff_false] at hd

theorem final_internal_strictMono {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    {P₀ : Configuration}
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀)
    (heq : InternalEquationLimits.InternalEquationAtLimit m y P₀)
    (a : BlockIndex (finalDatum y P₀)) :
    StrictMono (fun j : InternalIndex (finalDatum y P₀) a =>
      P₀ (internalLabel (finalDatum y P₀) a j) 0) := by
  apply FiniteHorizontalSort.strictMono_internalLabel
  intro b i j hi hj hu
  exact horizontal_label_injective_on_block hm hdata heq b hi hj hu

/-- Reindex an actual finite scalar force by a genuine finite equivalence,
including the erased self term. No permutation-invariance interface is
assumed. The diagonal term is zero by the literal scalar definition. -/
theorem oneDimensionalForce_equiv {n k : ℕ} (e : Fin n ≃ Fin k)
    (μ z : Fin k → ℝ) (i : Fin n) :
    oneDimensionalForce (fun j => μ (e j)) (fun j => z (e j)) i =
      oneDimensionalForce μ z (e i) := by
  classical
  unfold oneDimensionalForce
  calc
    (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        μ (e j) * (z (e i) - z (e j)) / |z (e i) - z (e j)| ^ 3) =
        ∑ j : Fin n, μ (e j) * (z (e i) - z (e j)) / |z (e i) - z (e j)| ^ 3 :=
      Finset.sum_erase _ (by simp)
    _ = ∑ j : Fin k, μ j * (z (e i) - z j) / |z (e i) - z j| ^ 3 :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = ∑ j ∈ (Finset.univ : Finset (Fin k)).erase (e i),
        μ j * (z (e i) - z j) / |z (e i) - z j| ^ 3 :=
      (Finset.sum_erase _ (by simp)).symm

theorem oneDimensionalSolution_equiv {n k : ℕ} (e : Fin n ≃ Fin k)
    (μ z : Fin k → ℝ) (hz : OneDimensionalSolution μ z) :
    OneDimensionalSolution (fun j => μ (e j)) (fun j => z (e j)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    exact hz.1 (e i) (e j) (fun h => hij (e.injective h))
  · calc
      (∑ i : Fin n, μ (e i) * z (e i)) = ∑ i : Fin k, μ i * z i :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = 0 := hz.2.1
  · intro i
    rw [oneDimensionalForce_equiv]
    exact hz.2.2 (e i)

theorem final_height_is_oneDimensionalSolution {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    (P₀ : Configuration) (hq : ∀ ν, IsSolution m (s ν) (q ν))
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y) :
    OneDimensionalSolution (datumBlockMass m (finalDatum y P₀)) (finalHeight y P₀) := by
  have hmass : datumBlockMass m (finalDatum y P₀) =
      fun a => datumBlockMass m (VerticalPartition.verticalPartitionDatum y) (oldIndex y P₀ a) := by
    funext a
    exact final_block_mass_eq m y P₀ a
  rw [hmass]
  exact oneDimensionalSolution_equiv (oldIndex y P₀) _ _
    (ScalarLimitEquations.outer_height_is_oneDimensionalSolution hm hq hlim)

theorem final_internal_field_eq_old (m : Masses) (y : Label → ℝ)
    (P₀ : Configuration) (P : Configuration) (i : Label) :
    NewtonFieldLimits.physicalInternalField m (finalDatum y P₀) P i =
      NewtonFieldLimits.physicalInternalField m (VerticalPartition.verticalPartitionDatum y) P i := by
  unfold NewtonFieldLimits.physicalInternalField
  rw [final_block_labels_eq, final_blockOf_to_old]

theorem final_internal_is_oneDimensionalSolution {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    {P₀ : Configuration}
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀)
    (heq : InternalEquationLimits.InternalEquationAtLimit m y P₀)
    (a : BlockIndex (finalDatum y P₀)) :
    OneDimensionalSolution (fun j => m (internalLabel (finalDatum y P₀) a j))
      (fun j => P₀ (internalLabel (finalDatum y P₀) a j) 0) := by
  have hu := final_internal_strictMono hm hdata heq a
  refine ⟨?_, ?_, ?_⟩
  · intro j k hjk
    exact fun h => hjk (hu.injective h)
  · exact SequenceBlockIndices.indexed_coordinate_center_zero m _ P₀ a 0
      (final_internal_center_zero hdata a)
  · intro j
    rw [ScalarLimitEquations.indexed_horizontal_force_eq_actual_internal_field m _ P₀
      (InternalHorizontalLimit.internal_limit_vertical_zero hm hdata heq),
      final_internal_field_eq_old]
    exact (heq (internalLabel (finalDatum y P₀) a j)).1

def finalCoordinates {m : Masses} {s : ℕ → ℝ} {q : ℕ → Configuration}
    {φ : ℕ → ℕ} {y : Label → ℝ} {P₀ : Configuration}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀) :
    BlowupCoordinates m (finalDatum y P₀) := by
  refine ⟨((0, finalHeight y P₀), ((fun i => P₀ i 0), 0)), ?_⟩
  apply (mem_coordinateSpace_iff m (finalDatum y P₀) _).mpr
  refine ⟨?_, final_height_center_zero m P₀ hlim.2.2.2.2.2.2.2.2, ?_, ?_⟩
  · simp
  · intro a
    have hcenter := congrArg (fun p : Point => p 0) (final_internal_center_zero hdata a)
    simpa only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      PiLp.zero_apply, smul_eq_mul] using hcenter
  · intro a
    simp

theorem finalCoordinates_outerH {m : Masses} {s : ℕ → ℝ} {q : ℕ → Configuration}
    {φ : ℕ → ℕ} {y : Label → ℝ} {P₀ : Configuration}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀)
    (a : BlockIndex (finalDatum y P₀)) : outerH (finalCoordinates hlim hdata) a = 0 := rfl

theorem finalCoordinates_outerY {m : Masses} {s : ℕ → ℝ} {q : ℕ → Configuration}
    {φ : ℕ → ℕ} {y : Label → ℝ} {P₀ : Configuration}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀)
    (a : BlockIndex (finalDatum y P₀)) :
    outerY (finalCoordinates hlim hdata) a = finalHeight y P₀ a := rfl

theorem finalCoordinates_innerU {m : Masses} {s : ℕ → ℝ} {q : ℕ → Configuration}
    {φ : ℕ → ℕ} {y : Label → ℝ} {P₀ : Configuration}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀) (i : Label) :
    innerU (finalCoordinates hlim hdata) i = P₀ i 0 := rfl

theorem finalCoordinates_innerV {m : Masses} {s : ℕ → ℝ} {q : ℕ → Configuration}
    {φ : ℕ → ℕ} {y : Label → ℝ} {P₀ : Configuration}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀) (i : Label) :
    innerV (finalCoordinates hlim hdata) i = 0 := rfl

/-- The exact IsSeed predicate is reached only AFTER actual horizontal
sorting and the mass/force/coordinate representation bridges above. -/
theorem finalCoordinates_isSeed {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    {P₀ : Configuration} (hq : ∀ ν, IsSolution m (s ν) (q ν))
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀)
    (heq : InternalEquationLimits.InternalEquationAtLimit m y P₀) :
    IsSeed m (finalDatum y P₀) (finalCoordinates hlim hdata) := by
  refine ⟨fun _ => rfl, fun _ => rfl, finalHeight_strictMono y P₀,
    final_height_is_oneDimensionalSolution hm P₀ hq hlim, ?_⟩
  intro a
  exact ⟨final_internal_strictMono hm hdata heq a,
    final_internal_is_oneDimensionalSolution hm hdata heq a⟩

end FourBody.ReorderedLimitCoordinates

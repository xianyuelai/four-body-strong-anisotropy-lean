import FourBody.InternalSubsequence
import FourBody.CrossSeparation
import FourBody.Reuse.NewtonBounds

/-!
# Limits of the actual finite Newton fields

Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
The internal collision separation was derived from the true scale bound.
The external separation is derived from distinct initial limit heights.
Finite fields are the literal target-minus-source physical Newton force.
No limit field, seed equation or analytic branch is assumed.
All new proof bodies are uncompiled.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace FourBody.NewtonFieldLimits

def physicalInternalField (m : Masses) (d : OrderedClusterDatum)
    (p : Configuration) (i : Label) : Point :=
  ∑ j ∈ (datumBlockLabels d (blockOf d i)).erase i,
    Reuse.physicalNewtonForce (m j) (p j) (p i)

def physicalExternalField (m : Masses) (d : OrderedClusterDatum)
    (q : Configuration) (i : Label) : Point :=
  ∑ j, if blockOf d j ≠ blockOf d i then
    Reuse.physicalNewtonForce (m j) (q j) (q i) else 0

def physicalExternalMean (m : Masses) (d : OrderedClusterDatum)
    (q : Configuration) (a : BlockIndex d) : Point :=
  datumBlockMean m d (physicalExternalField m d q) a

def initialVerticalConfiguration (y : Label → ℝ) : Configuration :=
  fun i => SequencePointLimits.verticalPoint (y i)

/-- Genuine joint Newton continuity at a nonzero physical separation;
proved from the already checked actual Newton joint smoothness body. -/
theorem physicalNewtonForce_joint_tendsto (μ : ℝ)
    {source target : ℕ → Point} {a b : Point}
    (hs : Tendsto source atTop (nhds a)) (ht : Tendsto target atTop (nhds b))
    (hab : a ≠ b) :
    Tendsto (fun ν => Reuse.physicalNewtonForce μ (source ν) (target ν))
      atTop (nhds (Reuse.physicalNewtonForce μ a b)) := by
  have hfield := (Reuse.newtonTargetField_joint_contDiffAt 0 (a, b) hab).continuousAt.tendsto.comp
    (hs.prodMk_nhds ht)
  simpa only [Reuse.physicalNewtonForce_eq_neg_legacy, Function.comp_apply] using
    (hfield.const_smul μ).neg

/-- Internal field convergence at the actually separated P₀ limit, on all
four labels of the SAME composed subsequence. -/
theorem internal_field_tendsto {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    {P₀ : Label → Point}
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀) (i : Label) :
    Tendsto (fun ν => physicalInternalField m (VerticalPartition.verticalPartitionDatum y)
      (InternalCoordinates.internalVectors m (VerticalPartition.verticalPartitionDatum y)
        (epsilon (s (φ ν))) (q (φ ν))) i)
      atTop (nhds (physicalInternalField m (VerticalPartition.verticalPartitionDatum y) P₀ i)) := by
  classical
  unfold physicalInternalField
  apply tendsto_finsetSum
  intro j hj
  have hjBlock : j ∈ datumBlock (VerticalPartition.verticalPartitionDatum y)
      (blockOf (VerticalPartition.verticalPartitionDatum y) i) := by
    simpa only [datumBlockLabels, List.mem_toFinset] using (Finset.mem_erase.mp hj).2
  have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
  have hd : 0 < dist (P₀ i) (P₀ j) :=
    ((ScaleConstants.constants_positive m hm).2.1).trans_le
      (hdata.2.2.2 _ i j (label_mem_blockOf _ i) hjBlock hij)
  exact physicalNewtonForce_joint_tendsto (m j) (tendsto_pi_nhds.mp hdata.1 j)
    (tendsto_pi_nhds.mp hdata.1 i) (dist_pos.mp hd).symm

/-- External field convergence is on the literal original positions.
Its limit is a finite force sum of vertical points, with no singular cross
term because actual different blocks have different attained heights. -/
theorem external_field_tendsto {m : Masses} {s : ℕ → ℝ} {q : ℕ → Configuration}
    {φ : ℕ → ℕ} {y : Label → ℝ}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y) (i : Label) :
    Tendsto (fun ν => physicalExternalField m (VerticalPartition.verticalPartitionDatum y)
      (q (φ ν)) i) atTop
      (nhds (physicalExternalField m (VerticalPartition.verticalPartitionDatum y)
        (initialVerticalConfiguration y) i)) := by
  classical
  unfold physicalExternalField
  apply tendsto_finsetSum
  intro j _hj
  by_cases hblock : blockOf (VerticalPartition.verticalPartitionDatum y) j ≠
      blockOf (VerticalPartition.verticalPartitionDatum y) i
  · have hne : y j ≠ y i := fun h => hblock
      ((VerticalPartition.blockOf_eq_iff_vertical_eq y j i).mpr h)
    have hsep : initialVerticalConfiguration y j ≠ initialVerticalConfiguration y i := by
      apply dist_pos.mp
      change 0 < dist (SequencePointLimits.verticalPoint (y j))
        (SequencePointLimits.verticalPoint (y i))
      rw [SequencePointLimits.verticalPoint_dist]
      exact abs_pos.mpr (sub_ne_zero.mpr hne)
    simp only [if_pos hblock]
    exact physicalNewtonForce_joint_tendsto (m j) (SequencePointLimits.selected_point_tendsto hlim j)
        (SequencePointLimits.selected_point_tendsto hlim i) hsep
  · simpa only [hblock, if_false] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Point)) atTop (nhds 0))

/-- The vertical component limit of the actual external field. -/
theorem external_field_coordinate_tendsto {m : Masses} {s : ℕ → ℝ}
    {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y) (i : Label) (k : Axis) :
    Tendsto (fun ν => physicalExternalField m (VerticalPartition.verticalPartitionDatum y)
      (q (φ ν)) i k) atTop
      (nhds (physicalExternalField m (VerticalPartition.verticalPartitionDatum y)
        (initialVerticalConfiguration y) i k)) := by
  exact (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Axis => ℝ) k).continuousAt.tendsto.comp
    (external_field_tendsto hlim i)

/-- Actual external block mass means inherit the finite external limits.
This does not identify their limit with the outer seed force law yet. -/
theorem external_mean_coordinate_tendsto {m : Masses} {s : ℕ → ℝ}
    {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (a : BlockIndex (VerticalPartition.verticalPartitionDatum y)) (k : Axis) :
    Tendsto (fun ν => physicalExternalMean m (VerticalPartition.verticalPartitionDatum y)
      (q (φ ν)) a k) atTop
      (nhds (physicalExternalMean m (VerticalPartition.verticalPartitionDatum y)
        (initialVerticalConfiguration y) a k)) := by
  classical
  have hsum : Tendsto
      (fun ν => ∑ i ∈ datumBlockLabels (VerticalPartition.verticalPartitionDatum y) a,
        m i * physicalExternalField m (VerticalPartition.verticalPartitionDatum y) (q (φ ν)) i k)
      atTop (nhds (∑ i ∈ datumBlockLabels (VerticalPartition.verticalPartitionDatum y) a,
        m i * physicalExternalField m (VerticalPartition.verticalPartitionDatum y)
          (initialVerticalConfiguration y) i k)) := by
    apply tendsto_finsetSum
    intro i _hi
    exact tendsto_const_nhds.mul (external_field_coordinate_tendsto hlim i k)
  simpa only [physicalExternalMean, datumBlockMean_apply] using
    (tendsto_const_nhds (x := (datumBlockMass m (VerticalPartition.verticalPartitionDatum y) a)⁻¹)).mul hsum


/-- Original arbitrary-sequence hypotheses alone give the SAME physical
subsequence with both scaled internal Newton limits and exterior limits.
The intermediate limit/separation facts are existentially derived here,
never assumed as a final analysis interface. -/
theorem exists_initial_internal_field_limits {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration}
    (hs : Tendsto s atTop atTop) (hq : ∀ ν, IsSolution m (s ν) (q ν)) :
    ∃ φ : ℕ → ℕ, ∃ y : Label → ℝ, ∃ P₀ : Label → Point,
      SequenceStart.InitialVerticalLimit m s q φ y ∧
      InternalSubsequence.InternalLimitData m s q φ y P₀ ∧
      (∀ i : Label, Tendsto (fun ν => physicalInternalField m
        (VerticalPartition.verticalPartitionDatum y)
        (InternalCoordinates.internalVectors m (VerticalPartition.verticalPartitionDatum y)
          (epsilon (s (φ ν))) (q (φ ν))) i) atTop
        (nhds (physicalInternalField m (VerticalPartition.verticalPartitionDatum y) P₀ i))) ∧
      (∀ i : Label, Tendsto (fun ν => physicalExternalField m
        (VerticalPartition.verticalPartitionDatum y) (q (φ ν)) i) atTop
        (nhds (physicalExternalField m (VerticalPartition.verticalPartitionDatum y)
          (initialVerticalConfiguration y) i))) := by
  obtain ⟨φ, y, ψ, P₀, _hlim, _hψ, hlim', hdata⟩ :=
    InternalSubsequence.exists_initial_internal_limit hm hs hq
  exact ⟨(fun ν => φ (ψ ν)), y, P₀, hlim', hdata,
    internal_field_tendsto hm hdata, external_field_tendsto hlim'⟩

end FourBody.NewtonFieldLimits


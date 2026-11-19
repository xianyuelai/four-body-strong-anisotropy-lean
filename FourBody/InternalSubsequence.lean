import FourBody.InternalCoordinates
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Simultaneous limits of the four actual scaled internal vectors

Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD,
lines 447--452, with the actual mass-mean coordinates of lines 403--411.

The compact set is the concrete product of four closed Euclidean balls
with the source's C(m), obtained from the actual two-scale theorem body.
One further strictly increasing ψ extracts ALL four internal vectors.
The physical subsequence is φ ∘ ψ, and every previously derived limit is
preserved on that SAME composed subsequence.

This proves no internal limiting force equation, v⁰=0, final seed order,
outer seed equation, or H=O(ε³). No SeedLimitStatement, branch, boundedness
certificate or compactness interface is a hypothesis of the final
existence theorem. All these new bodies are still uncompiled.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace FourBody.InternalSubsequence

def internalCompactCube (m : Masses) : Set (Label → Point) :=
  Set.pi Set.univ (fun _ => Metric.closedBall (0 : Point) (ScaleConstants.C m))

theorem isCompact_internalCompactCube (m : Masses) : IsCompact (internalCompactCube m) := by
  exact isCompact_univ_pi (fun _ : Label => isCompact_closedBall (0 : Point) (ScaleConstants.C m))

theorem eventually_internal_mem_compactCube {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    (hq : ∀ ν, IsSolution m (s ν) (q ν))
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y) :
    ∀ᶠ ν in atTop, InternalCoordinates.internalVectors m
      (VerticalPartition.verticalPartitionDatum y) (epsilon (s (φ ν))) (q (φ ν))
        ∈ internalCompactCube m := by
  filter_upwards [InternalCoordinates.eventually_internal_vectors_bound hm hq hlim] with ν hν
  intro i _hi
  simpa only [Metric.mem_closedBall, dist_zero_right] using hν i

/-- Concrete product compactness, with no pre-assumed scaled limit. -/
theorem exists_internal_subsequence {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    (hq : ∀ ν, IsSolution m (s ν) (q ν))
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y) :
    ∃ P₀ : Label → Point, P₀ ∈ internalCompactCube m ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Tendsto (fun ν => InternalCoordinates.internalVectors m
          (VerticalPartition.verticalPartitionDatum y)
          (epsilon (s (φ (ψ ν)))) (q (φ (ψ ν)))) atTop (nhds P₀) := by
  simpa only [Function.comp_def] using
    (isCompact_internalCompactCube m).tendsto_subseq'
      (eventually_internal_mem_compactCube hm hq hlim).frequently

/-- The exact weighted internal center passes to the actual Point limits. -/
theorem internal_limit_center_zero {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    {P₀ : Label → Point}
    (hP : Tendsto (fun ν => InternalCoordinates.internalVectors m
      (VerticalPartition.verticalPartitionDatum y) (epsilon (s (φ ν))) (q (φ ν)))
      atTop (nhds P₀)) (a : BlockIndex (VerticalPartition.verticalPartitionDatum y)) :
    (∑ i ∈ datumBlockLabels (VerticalPartition.verticalPartitionDatum y) a, m i • P₀ i) = 0 := by
  classical
  have hsum : Tendsto
      (fun ν => ∑ i ∈ datumBlockLabels (VerticalPartition.verticalPartitionDatum y) a,
        m i • InternalCoordinates.internalVectors m (VerticalPartition.verticalPartitionDatum y)
          (epsilon (s (φ ν))) (q (φ ν)) i)
      atTop (nhds (∑ i ∈ datumBlockLabels (VerticalPartition.verticalPartitionDatum y) a,
        m i • P₀ i)) := by
    apply tendsto_finsetSum
    intro i _hi
    exact (tendsto_pi_nhds.mp hP i).const_smul (m i)
  have hzero : ∀ ν, (∑ i ∈ datumBlockLabels (VerticalPartition.verticalPartitionDatum y) a,
      m i • InternalCoordinates.internalVectors m (VerticalPartition.verticalPartitionDatum y)
        (epsilon (s (φ ν))) (q (φ ν)) i) = 0 := by
    intro ν
    calc
      _ = ∑ i ∈ datumBlockLabels (VerticalPartition.verticalPartitionDatum y) a,
          m i • internalVectorCoordinate m (VerticalPartition.verticalPartitionDatum y)
            (epsilon (s (φ ν))) (q (φ ν)) a i := by
        apply Finset.sum_congr rfl
        intro i hi
        have himem : i ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) a := by
          simpa only [datumBlockLabels, List.mem_toFinset] using hi
        rw [InternalCoordinates.internalVectors_apply_of_mem m
          (VerticalPartition.verticalPartitionDatum y) _ _ himem]
      _ = 0 := InternalCoordinates.internalVectors_center_zero hm _ _ _ a
  have hsum0 : Tendsto
      (fun ν => ∑ i ∈ datumBlockLabels (VerticalPartition.verticalPartitionDatum y) a,
        m i • InternalCoordinates.internalVectors m (VerticalPartition.verticalPartitionDatum y)
          (epsilon (s (φ ν))) (q (φ ν)) i) atTop (nhds 0) :=
    tendsto_const_nhds.congr' (Eventually.of_forall (fun ν => (hzero ν).symm))
  exact tendsto_nhds_unique hsum hsum0

/-- The actual lower-scale bound passes to the internal limit. It was
proved from original solutions and is not assumed as a limit certificate. -/
theorem internal_limit_separated {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    (hq : ∀ ν, IsSolution m (s ν) (q ν))
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y) {P₀ : Label → Point}
    (hP : Tendsto (fun ν => InternalCoordinates.internalVectors m
      (VerticalPartition.verticalPartitionDatum y) (epsilon (s (φ ν))) (q (φ ν)))
      atTop (nhds P₀)) {a : BlockIndex (VerticalPartition.verticalPartitionDatum y)}
    {i j : Label} (hi : i ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) a)
    (hj : j ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) a) (hij : i ≠ j) :
    ScaleConstants.c₀ m ≤ dist (P₀ i) (P₀ j) := by
  have hbound : ∀ ν, ScaleConstants.c₀ m ≤
      dist (InternalCoordinates.internalVectors m (VerticalPartition.verticalPartitionDatum y)
        (epsilon (s (φ ν))) (q (φ ν)) i)
        (InternalCoordinates.internalVectors m (VerticalPartition.verticalPartitionDatum y)
          (epsilon (s (φ ν))) (q (φ ν)) j) := by
    intro ν
    have hε : 0 < epsilon (s (φ ν)) := hlim.2.2.2.1 ν
    rw [InternalCoordinates.internalVectors_dist_of_mem m _ hε _ hi hj]
    exact (le_div_iff₀ hε).mpr
      (TwoScale.pair_distance_lower m hm (hlim.2.1 ν).le (hq (φ ν)) i j hij)
  exact ge_of_tendsto ((tendsto_pi_nhds.mp hP i).dist (tendsto_pi_nhds.mp hP j))
    (Eventually.of_forall hbound)

theorem internal_limit_singleton_zero {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    {P₀ : Label → Point}
    (hP : Tendsto (fun ν => InternalCoordinates.internalVectors m
      (VerticalPartition.verticalPartitionDatum y) (epsilon (s (φ ν))) (q (φ ν)))
      atTop (nhds P₀)) {a : BlockIndex (VerticalPartition.verticalPartitionDatum y)}
    {i : Label} (hblock : datumBlock (VerticalPartition.verticalPartitionDatum y) a = [i]) :
    P₀ i = 0 := by
  have hi : i ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) a := by simp [hblock]
  have hzero : ∀ ν, InternalCoordinates.internalVectors m
      (VerticalPartition.verticalPartitionDatum y) (epsilon (s (φ ν))) (q (φ ν)) i = 0 := by
    intro ν
    rw [InternalCoordinates.internalVectors_apply_of_mem m _ _ _ hi]
    exact InternalCoordinates.internalVector_eq_zero_of_singleton hm _ _ _ a i hblock
  exact tendsto_nhds_unique (tendsto_pi_nhds.mp hP i)
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun ν => (hzero ν).symm)))

/-- Literal intermediate conclusions, not a seed assertion. P₀ may still
have a nonzero vertical component until the internal force-limit proof. -/
def InternalLimitData (m : Masses) (s : ℕ → ℝ) (q : ℕ → Configuration)
    (φ : ℕ → ℕ) (y : Label → ℝ) (P₀ : Label → Point) : Prop :=
  Tendsto (fun ν => InternalCoordinates.internalVectors m
    (VerticalPartition.verticalPartitionDatum y) (epsilon (s (φ ν))) (q (φ ν)))
    atTop (nhds P₀) ∧
  (∀ i : Label, ‖P₀ i‖ ≤ ScaleConstants.C m) ∧
  (∀ a : BlockIndex (VerticalPartition.verticalPartitionDatum y),
    (∑ i ∈ datumBlockLabels (VerticalPartition.verticalPartitionDatum y) a, m i • P₀ i) = 0) ∧
  (∀ (a : BlockIndex (VerticalPartition.verticalPartitionDatum y)) (i j : Label),
    i ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) a →
    j ∈ datumBlock (VerticalPartition.verticalPartitionDatum y) a → i ≠ j →
      ScaleConstants.c₀ m ≤ dist (P₀ i) (P₀ j))

/-- All hypotheses are those of the actual arbitrary original solution
sequence. Initial vertical compactness and internal compactness are both
derived. The further ψ is explicit; the physical sequence is φ ∘ ψ. -/
theorem exists_initial_internal_limit {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration}
    (hs : Tendsto s atTop atTop) (hq : ∀ ν, IsSolution m (s ν) (q ν)) :
    ∃ φ : ℕ → ℕ, ∃ y : Label → ℝ, ∃ ψ : ℕ → ℕ, ∃ P₀ : Label → Point,
      SequenceStart.InitialVerticalLimit m s q φ y ∧ StrictMono ψ ∧
      SequenceStart.InitialVerticalLimit m s q (fun ν => φ (ψ ν)) y ∧
      InternalLimitData m s q (fun ν => φ (ψ ν)) y P₀ := by
  obtain ⟨φ, y, hlim⟩ := SequenceStart.exists_initial_vertical_limit hm hs hq
  obtain ⟨P₀, hcube, ψ, hψ, hP⟩ := exists_internal_subsequence hm hq hlim
  have hlim' := InternalScale.initial_limit_comp hlim hψ
  refine ⟨φ, y, ψ, P₀, hlim, hψ, hlim', hP, ?_, ?_, ?_⟩
  · intro i
    simpa only [Metric.mem_closedBall, dist_zero_right] using hcube i (Set.mem_univ i)
  · intro a
    exact internal_limit_center_zero hm hP a
  · intro a i j hi hj hij
    exact internal_limit_separated hm hq hlim' hP hi hj hij

end FourBody.InternalSubsequence


import FourBody.PhysicalSequenceRows

/-!
# Actual limiting internal equations after scaled compactness

Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
The exact scaled rows and finite Newton continuity imply
g(P₀)_x=P₀_x and g(P₀)_y=0. The outer mean limit equals its actual ordered
initial height. Neither conclusion is assumed through SeedLimitStatement,
IsSeed, branch membership or a pre-proved equation-limit interface.
All proof bodies and residual bridge dependencies remain uncompiled.
-/

noncomputable section
open Filter

namespace FourBody.InternalEquationLimits

theorem point_coordinate_tendsto {p : ℕ → Point} {p₀ : Point}
    (hp : Tendsto p atTop (nhds p₀)) (k : Axis) :
    Tendsto (fun ν => p ν k) atTop (nhds (p₀ k)) := by
  exact (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Axis => ℝ) k).continuousAt.tendsto.comp hp

/-- Genuine finite physical Newton equations at the internal limit.
The second row does not yet assert that P₀_y itself vanishes. -/
def InternalEquationAtLimit (m : Masses) (y : Label → ℝ) (P₀ : Label → Point) : Prop :=
  ∀ i : Label,
    NewtonFieldLimits.physicalInternalField m (VerticalPartition.verticalPartitionDatum y) P₀ i 0 =
      P₀ i 0 ∧
    NewtonFieldLimits.physicalInternalField m (VerticalPartition.verticalPartitionDatum y) P₀ i 1 = 0

/-- Intermediate facts are the concrete conclusions already derived by
InternalSubsequence, not unproved analytic interfaces. The actual hν is
constructed here by the proved mass-mean inverse, not supplied as a branch. -/
theorem internal_equation_at_limit {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    {P₀ : Label → Point} (hq : ∀ ν, IsSolution m (s ν) (q ν))
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (hdata : InternalSubsequence.InternalLimitData m s q φ y P₀) :
    InternalEquationAtLimit m y P₀ := by
  obtain ⟨h, hh⟩ := VerticalPartition.exists_selected_mean_coordinates hm hq hlim.2.1
    (VerticalPartition.verticalPartitionDatum y)
  intro i
  have he := hlim.2.2.2.2.1
  have hg := NewtonFieldLimits.internal_field_tendsto hm hdata i
  have hgx := point_coordinate_tendsto hg 0
  have hgy := point_coordinate_tendsto hg 1
  have hu := point_coordinate_tendsto (tendsto_pi_nhds.mp hdata.1 i) 0
  have hv := point_coordinate_tendsto (tendsto_pi_nhds.mp hdata.1 i) 1
  have hdx := (NewtonFieldLimits.external_field_coordinate_tendsto hlim i 0).sub
    (NewtonFieldLimits.external_mean_coordinate_tendsto hlim (blockOf _ i) 0)
  have hdy := (NewtonFieldLimits.external_field_coordinate_tendsto hlim i 1).sub
    (NewtonFieldLimits.external_mean_coordinate_tendsto hlim (blockOf _ i) 1)
  have hpertx : Tendsto (fun ν => (epsilon (s (φ ν))) ^ 2 *
      (NewtonFieldLimits.physicalExternalField m (VerticalPartition.verticalPartitionDatum y)
        (q (φ ν)) i 0 -
        NewtonFieldLimits.physicalExternalMean m (VerticalPartition.verticalPartitionDatum y)
          (q (φ ν)) (blockOf _ i) 0)) atTop (nhds 0) := by
    simpa using (he.pow 2).mul hdx
  have hperty : Tendsto (fun ν => (epsilon (s (φ ν))) ^ 2 *
      (NewtonFieldLimits.physicalExternalField m (VerticalPartition.verticalPartitionDatum y)
        (q (φ ν)) i 1 -
        NewtonFieldLimits.physicalExternalMean m (VerticalPartition.verticalPartitionDatum y)
          (q (φ ν)) (blockOf _ i) 1)) atTop (nhds 0) := by
    simpa using (he.pow 2).mul hdy
  have hrhs : Tendsto (fun ν => (epsilon (s (φ ν))) ^ 3 *
      InternalCoordinates.internalVectors m (VerticalPartition.verticalPartitionDatum y)
        (epsilon (s (φ ν))) (q (φ ν)) i 1) atTop (nhds 0) := by
    simpa using (he.pow 3).mul hv
  have hxrow := fun ν => PhysicalSequenceRows.internal_horizontal_row hm
    (lt_trans (by norm_num) (hlim.2.1 ν)) (hq (φ ν)) (hh ν) i
  have hyrow := fun ν => PhysicalSequenceRows.internal_vertical_row hm
    (lt_trans (by norm_num) (hlim.2.1 ν)) (hq (φ ν)) (hh ν) i
  constructor
  · have hleft := hgx.add hpertx
    have hright := hu.congr' (Eventually.of_forall (fun ν => (hxrow ν).symm))
    simpa only [add_zero] using tendsto_nhds_unique hleft hright
  · have hleft := hgy.add hperty
    have hright := hrhs.congr' (Eventually.of_forall (fun ν => (hyrow ν).symm))
    simpa only [add_zero] using tendsto_nhds_unique hleft hright

/-- The actual exterior vertical block mean satisfies the outer force
limit equation, before finite regrouping into oneDimensionalForce. -/
theorem outer_mean_limit_equation {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    (hq : ∀ ν, IsSolution m (s ν) (q ν))
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (a : BlockIndex (VerticalPartition.verticalPartitionDatum y)) :
    NewtonFieldLimits.physicalExternalMean m (VerticalPartition.verticalPartitionDatum y)
      (NewtonFieldLimits.initialVerticalConfiguration y) a 1 =
        VerticalPartition.verticalHeight y a := by
  obtain ⟨h, hh⟩ := VerticalPartition.exists_selected_mean_coordinates hm hq hlim.2.1
    (VerticalPartition.verticalPartitionDatum y)
  have hc := VerticalPartition.vertical_block_mean_tendsto hm hlim.2.2.2.2.2.1 a
  have hrow := fun ν => PhysicalSequenceRows.vertical_mean_row hm
    (lt_trans (by norm_num) (hlim.2.1 ν)) (hq (φ ν)) (hh ν) a
  have heq : ∀ ν,
      verticalCenterCoordinate m (VerticalPartition.verticalPartitionDatum y) (q (φ ν)) a =
        NewtonFieldLimits.physicalExternalMean m (VerticalPartition.verticalPartitionDatum y)
          (q (φ ν)) a 1 :=
    fun ν => ((hh ν).2.2.1 a).symm.trans (hrow ν)
  exact tendsto_nhds_unique
    (NewtonFieldLimits.external_mean_coordinate_tendsto hlim a 1)
    (hc.congr' (Eventually.of_forall heq))

/-- A fresh existential consequence of original hypotheses only: all
intermediate compactness and all limiting equations are DERIVED. -/
theorem exists_internal_equation_limit {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration}
    (hs : Tendsto s atTop atTop) (hq : ∀ ν, IsSolution m (s ν) (q ν)) :
    ∃ φ : ℕ → ℕ, ∃ y : Label → ℝ, ∃ P₀ : Label → Point,
      SequenceStart.InitialVerticalLimit m s q φ y ∧
      InternalSubsequence.InternalLimitData m s q φ y P₀ ∧
      InternalEquationAtLimit m y P₀ ∧
      (∀ a : BlockIndex (VerticalPartition.verticalPartitionDatum y),
        NewtonFieldLimits.physicalExternalMean m (VerticalPartition.verticalPartitionDatum y)
          (NewtonFieldLimits.initialVerticalConfiguration y) a 1 =
            VerticalPartition.verticalHeight y a) := by
  obtain ⟨φ, y, ψ, P₀, _hlim, _hψ, hlim', hdata⟩ :=
    InternalSubsequence.exists_initial_internal_limit hm hs hq
  exact ⟨(fun ν => φ (ψ ν)), y, P₀, hlim', hdata,
    internal_equation_at_limit hm hq hlim' hdata, outer_mean_limit_equation hm hq hlim'⟩

end FourBody.InternalEquationLimits


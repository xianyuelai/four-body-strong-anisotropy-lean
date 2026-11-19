import FourBody.SeedZero
import FourBody.SeedJacobian
import FourBody.BlowupAnalytic
import FourBody.Reuse.ImplicitRectangle
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
Actual application of the analytic implicit function theorem to F, including
a single fixed signed parameter interval and fixed open coordinate ball.
All analytic, root and Jacobian inputs are proved for the actual residual.
The final existence declaration only takes the original positive masses and
the ordered datum. STATIC candidate; serial compiler verification is pending.
-/

noncomputable section
open scoped ContDiff
open Filter Set Topology
namespace FourBody.LocalBranch

open BlowupAnalytic

/-- These are conclusion witnesses produced below, not branch hypotheses
supplied to the final datum-local theorem. -/
structure ZeroRectangle {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (seed : BlowupCoordinates m d) where
  eta : ℝ
  delta : ℝ
  neighborhood : Set (BlowupCoordinates m d)
  branch : ℝ → BlowupCoordinates m d
  eta_pos : 0 < eta
  delta_pos : 0 < delta
  neighborhood_open : IsOpen neighborhood
  seed_mem : seed ∈ neighborhood
  seed_isSeed : IsSeed m d seed
  branch_analytic : AnalyticOnNhd ℝ branch (Ioo (-eta) eta)
  branch_zero : branch 0 = seed
  branch_mem : ∀ ε ∈ Ioo (-eta) eta, branch ε ∈ neighborhood
  branch_root : ∀ ε ∈ Ioo (-eta) eta, blowupResidual hm ε (branch ε) = 0
  distances : ∀ ε ∈ Ioo (-eta) eta, ∀ z ∈ neighborhood,
    UniformDistanceBound delta (ε, z)
  residual_analytic : AnalyticOnNhd ℝ
    (fun p : Variables m d => blowupResidual hm p.1 p.2)
    (Ioo (-eta) eta ×ˢ neighborhood)
  derivative_invertible : ∀ ε ∈ Ioo (-eta) eta, ∀ z ∈ neighborhood,
    (Reuse.Implicit.jacobian (blowupResidual hm) ε z).IsInvertible
  graph_exact : ∀ ε ∈ Ioo (-eta) eta, ∀ z ∈ neighborhood,
    blowupResidual hm ε z = 0 ↔ branch ε = z

/-- Continuity of the true partial derivative and openness of the actual
continuous-linear-equivalence range preserve seed invertibility nearby. -/
theorem seed_jacobian_eventually_invertible {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) :
    ∀ᶠ p : Variables m d in 𝓝 (0, seed),
      (Reuse.Implicit.jacobian (blowupResidual hm) p.1 p.2).IsInvertible := by
  have han := blowupResidual_seed_joint_analyticAt hm hs
  have hc := Reuse.Implicit.jacobian_joint_continuousAt
    (blowupResidual hm) 0 seed han.contDiffAt
  have hJ : (Reuse.Implicit.jacobian (blowupResidual hm) 0 seed).IsInvertible :=
    SeedJacobian.blowupResidual_zero_fderiv_isInvertible hm hs
  obtain ⟨e, he⟩ := hJ
  have hnear : Set.range
      ((↑) : (BlowupCoordinates m d ≃L[ℝ] BlowupCoordinates m d) →
        (BlowupCoordinates m d →L[ℝ] BlowupCoordinates m d)) ∈
      𝓝 (Reuse.Implicit.jacobian (blowupResidual hm) 0 seed) := by
    rw [← he]
    exact ContinuousLinearEquiv.nhds e
  exact hc.tendsto.eventually hnear

theorem zeroRectangle_of_isSeed {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) :
    Nonempty (ZeroRectangle hm d seed) := by
  obtain ⟨κ, δ, hκ, hδ, hdist⟩ := seed_positive_distance_rectangle hs
  obtain ⟨b, hb, hJball⟩ := Metric.eventually_nhds_iff_ball.mp
    (seed_jacobian_eventually_invertible hm hs)
  obtain ⟨ψ, η₀, ζ, hη₀, hζ, hbase, hanalytic, hgraph⟩ :=
    Reuse.Implicit.local_analytic_rectangle_on_ball
      (blowupResidual hm) 0 seed (blowupResidual_seed_joint_analyticAt hm hs)
      (isSeed_blowupResidual_zero hm seed hs)
      (SeedJacobian.blowupResidual_zero_fderiv_isInvertible hm hs)
  let r : ℝ := min ζ (min κ b)
  have hr : 0 < r := lt_min hζ (lt_min hκ hb)
  have hrζ : r ≤ ζ := min_le_left _ _
  have hrκ : r ≤ κ := (min_le_right _ _).trans (min_le_left _ _)
  have hrb : r ≤ b := (min_le_right _ _).trans (min_le_right _ _)
  have hcψ : ContinuousAt ψ 0 :=
    (hanalytic 0 (Metric.mem_ball_self hη₀)).continuousAt
  have hψnear : ∀ᶠ ε in 𝓝 (0 : ℝ), ψ ε ∈ Metric.ball seed r := by
    apply hcψ.tendsto.eventually
    change Metric.ball seed r ∈ 𝓝 (ψ 0)
    rw [hbase]
    exact Metric.ball_mem_nhds seed hr
  obtain ⟨c, hc, hψball⟩ := Metric.eventually_nhds_iff_ball.mp hψnear
  let η : ℝ := min (min η₀ κ) (min b c)
  have hη : 0 < η := lt_min (lt_min hη₀ hκ) (lt_min hb hc)
  have hηη₀ : η ≤ η₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hηκ : η ≤ κ := (min_le_left _ _).trans (min_le_right _ _)
  have hηb : η ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hηc : η ≤ c := (min_le_right _ _).trans (min_le_right _ _)
  have hparam {ε : ℝ} (hε : ε ∈ Ioo (-η) η) : dist ε 0 < η := by
    simpa only [Real.dist_eq, sub_zero] using abs_lt.mpr hε
  have hdistAll : ∀ ε ∈ Ioo (-η) η, ∀ z ∈ Metric.ball seed r,
      UniformDistanceBound δ (ε, z) := by
    intro ε hε z hz
    have hεκ : ε ∈ Ioo (-κ) κ := by
      apply abs_lt.mp
      simpa only [Real.dist_eq, sub_zero] using (hparam hε).trans_le hηκ
    apply hdist ε hεκ z
    exact (Metric.mem_ball.mp hz).trans_le hrκ
  have hJAll : ∀ ε ∈ Ioo (-η) η, ∀ z ∈ Metric.ball seed r,
      (Reuse.Implicit.jacobian (blowupResidual hm) ε z).IsInvertible := by
    intro ε hε z hz
    apply hJball (ε, z)
    rw [Metric.mem_ball, Prod.dist_eq]
    exact max_lt ((hparam hε).trans_le hηb)
      ((Metric.mem_ball.mp hz).trans_le hrb)
  refine ⟨{
    eta := η
    delta := δ
    neighborhood := Metric.ball seed r
    branch := ψ
    eta_pos := hη
    delta_pos := hδ
    neighborhood_open := Metric.isOpen_ball
    seed_mem := Metric.mem_ball_self hr
    seed_isSeed := hs
    branch_analytic := ?_
    branch_zero := hbase
    branch_mem := ?_
    branch_root := ?_
    distances := hdistAll
    residual_analytic := ?_
    derivative_invertible := hJAll
    graph_exact := ?_
  }⟩
  · intro ε hε
    exact hanalytic ε ((hparam hε).trans_le hηη₀)
  · intro ε hε
    exact hψball ε ((hparam hε).trans_le hηc)
  · intro ε hε
    exact (hgraph ε ((hparam hε).trans_le hηη₀)).2.1
  · intro p hp
    have hsep := separated_of_uniformDistanceBound hδ (hdistAll p.1 hp.1 p.2 hp.2)
    exact blowupResidual_joint_analyticAt hm p hsep.1 hsep.2
  · intro ε hε z hz
    exact (hgraph ε ((hparam hε).trans_le hηη₀)).2.2 z
      ((Metric.mem_ball.mp hz).trans_le hrζ)

/-- Actual all-datum analytic zero-graph existence. All analytical, root and
invertibility inputs above are discharged by proofs for the concrete seed. -/
theorem zeroRectangle_exists {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) : Nonempty (ZeroRectangle hm d (seedCoordinates hm d)) :=
  zeroRectangle_of_isSeed hm (seedCoordinates_isSeed hm d)

end FourBody.LocalBranch

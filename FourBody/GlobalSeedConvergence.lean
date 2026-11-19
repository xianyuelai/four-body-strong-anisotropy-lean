import FourBody.SeedLimitCandidate
import FourBody.SeedConstruction
import Mathlib.Tactic.FunProp

/-!
Section 5 of frozen Pro v2, lines 650--660. Source SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

This is the topology bridge actually required by exhaustion: the component
limits in Proposition 3.2 imply convergence in the entire constrained
coordinate space. It includes every label, including singleton blocks.

Initially prepared as a proof candidate. Actual build/audit status is
recorded in strict receipts; this module alone does not attest
whole-paper acceptance.
-/

noncomputable section
open Filter Topology
namespace FourBody.Global

theorem point_coordinate_tendsto {f : ℕ → Point} {p : Point}
    (hf : Tendsto f atTop (nhds p)) (k : Axis) :
    Tendsto (fun ν => f ν k) atTop (nhds (p k)) := by
  have hc : Continuous (fun t : Point => t k) := by fun_prop
  exact hc.continuousAt.tendsto.comp hf

/-- The actual finite-product/subspace topology, without any substituted
coordinate norm or assumed convergence of the complete coordinate tuple. -/
theorem coordinates_tendsto_seed {m : Masses} {d : OrderedClusterDatum}
    {e : ℕ → ℝ} {q : ℕ → Configuration}
    {seed : BlowupCoordinates m d} {h : ℕ → BlowupCoordinates m d}
    (hs : IsSeed m d seed)
    (hc : ∀ ν, CoordinatesOfConfiguration m d (e ν) (q ν) (h ν))
    (houter : ∀ a : BlockIndex d,
      Tendsto (fun ν => outerH (h ν) a) atTop (nhds 0) ∧
      Tendsto (fun ν => outerY (h ν) a) atTop (nhds (outerY seed a)))
    (hinner : ∀ (a : BlockIndex d) (i : Label), i ∈ datumBlock d a →
      Tendsto (fun ν => internalVectorCoordinate m d (e ν) (q ν) a i)
        atTop (nhds (!₂[innerU seed i, 0] : Point))) :
    Tendsto h atTop (nhds seed) := by
  have hH : Tendsto (fun ν => outerH (h ν)) atTop (nhds (outerH seed)) := by
    apply tendsto_pi_nhds.mpr
    intro a
    simpa only [hs.1 a] using (houter a).1
  have hY : Tendsto (fun ν => outerY (h ν)) atTop (nhds (outerY seed)) :=
    tendsto_pi_nhds.mpr (fun a => (houter a).2)
  have hU : Tendsto (fun ν => innerU (h ν)) atTop (nhds (innerU seed)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    let a : BlockIndex d := blockOf d i
    have hi : i ∈ datumBlock d a := label_mem_blockOf d i
    have heq (ν : ℕ) : innerU (h ν) i =
        internalVectorCoordinate m d (e ν) (q ν) a i 0 := by
      exact congrArg (fun p : Point => p 0) ((hc ν).2.2.2 a i hi)
    have ht := point_coordinate_tendsto (hinner a i hi) 0
    simpa only [← heq, Matrix.cons_val_zero] using ht
  have hV : Tendsto (fun ν => innerV (h ν)) atTop (nhds (innerV seed)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    let a : BlockIndex d := blockOf d i
    have hi : i ∈ datumBlock d a := label_mem_blockOf d i
    have heq (ν : ℕ) : innerV (h ν) i =
        internalVectorCoordinate m d (e ν) (q ν) a i 1 := by
      exact congrArg (fun p : Point => p 1) ((hc ν).2.2.2 a i hi)
    have ht := point_coordinate_tendsto (hinner a i hi) 1
    simpa only [← heq, Matrix.cons_val_one, Matrix.cons_val_zero, hs.2.1 i] using ht
  apply tendsto_subtype_rng.mpr
  exact (hH.prodMk_nhds hY).prodMk_nhds (hU.prodMk_nhds hV)

theorem seed_eq_canonical {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d}
    (hs : IsSeed m d seed) : seed = seedCoordinates hm d :=
  (seed_existsUnique hm d).unique hs (seedCoordinates_isSeed hm d)

end FourBody.Global

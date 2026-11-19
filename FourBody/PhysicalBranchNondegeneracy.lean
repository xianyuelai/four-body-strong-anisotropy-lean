import FourBody.LocalBranchAnalytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
The actual positive-epsilon physical branch and its original W derivative.
Q maps coordinates to physical configurations; T maps residuals in the opposite
direction and is a different CLE. The local chain rule uses the true equation
F = T R Q on an open positive-distance neighborhood. STATIC proof candidate.
-/

noncomputable section
open Filter Set Topology
namespace FourBody.LocalBranch

open BlowupAnalytic

theorem physicalCoordinates_collisionFree_of_distances {m : Masses}
    {d : OrderedClusterDatum} {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (h : BlowupCoordinates m d) (hb : UniformDistanceBound δ (ε, h)) :
    CollisionFree (physicalCoordinates ε h) := by
  have hsep := separated_of_uniformDistanceBound hδ hb
  intro i j hij heq
  by_cases hblock : blockOf d i = blockOf d j
  · have hzero : physicalCoordinates ε h i - physicalCoordinates ε h j = 0 :=
      sub_eq_zero.mpr heq
    rw [physicalCoordinates_difference_sameBlock ε h i j hblock] at hzero
    have hinner : internalCoordinates h i - internalCoordinates h j = 0 :=
      (smul_eq_zero.mp hzero).resolve_left (ne_of_gt hε)
    exact hsep.1 i j hblock hij (sub_eq_zero.mp hinner)
  · apply hsep.2 i j hblock
    rw [crossDifference_eq_sub, heq, sub_self]

theorem positive_parameter_mem {m : Masses} {hm : PositiveMasses m}
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d}
    (r : ZeroRectangle hm d seed) {ε : ℝ} (hε : 0 < ε) (hη : ε < r.eta) :
    ε ∈ Ioo (-r.eta) r.eta :=
  ⟨(neg_lt_zero.mpr r.eta_pos).trans hε, hη⟩

theorem physical_solution_of_zeroRectangle {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d}
    (r : ZeroRectangle hm d seed) {ε : ℝ} (hε : 0 < ε) (hη : ε < r.eta)
    (h : BlowupCoordinates m d) (hh : h ∈ r.neighborhood)
    (hF : blowupResidual hm ε h = 0) :
    IsSolution m (parameterFromEpsilon ε) (physicalCoordinates ε h) := by
  have hparam := positive_parameter_mem r hε hη
  have hb := r.distances ε hparam h hh
  have hsep := (separated_of_uniformDistanceBound r.delta_pos hb).1
  have hR := (blowupResidual_zero_iff_restrictedResidual_zero hm hε h hsep).mp hF
  have hval : residual m (parameterFromEpsilon ε) (physicalCoordinates ε h) = 0 :=
    congrArg Subtype.val hR
  refine ⟨physicalCoordinates_collisionFree_of_distances hε r.delta_pos h hb, ?_⟩
  intro i
  have hi := congr_fun hval i
  change force m (physicalCoordinates ε h) i -
    anisotropy (parameterFromEpsilon ε) (physicalCoordinates ε h i) = 0 at hi
  exact sub_eq_zero.mp hi

/-- Actual full chain-rule equation, with two different CLEs. The input
point need not be a zero. Positive distances throughout the SAME fixed open
neighborhood justify the local equality of the functions being differentiated. -/
theorem derivative_physical_identity_on_rectangle {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d}
    (r : ZeroRectangle hm d seed) {ε : ℝ} (hε : 0 < ε) (hη : ε < r.eta)
    (h : BlowupCoordinates m d) (hh : h ∈ r.neighborhood) :
    let Q := coordinateContinuousEquivalence hm d (ne_of_gt hε)
    let T := residualTContinuousEquivalence hm d (ne_of_gt hε)
    Reuse.Implicit.jacobian (blowupResidual hm) ε h =
      T.toContinuousLinearMap.comp
        ((fderiv ℝ (restrictedResidual m (parameterFromEpsilon ε)) (Q h)).comp
          Q.toContinuousLinearMap) := by
  let Q := coordinateContinuousEquivalence hm d (ne_of_gt hε)
  let T := residualTContinuousEquivalence hm d (ne_of_gt hε)
  let R := restrictedResidual m (parameterFromEpsilon ε)
  let J := fderiv ℝ R (Q h)
  have hparam := positive_parameter_mem r hε hη
  have hb := r.distances ε hparam h hh
  have hCF : CollisionFree ((Q h : W m) : Configuration) :=
    physicalCoordinates_collisionFree_of_distances hε r.delta_pos h hb
  have hdR : HasFDerivAt R J (Q h) :=
    ((contDiffAt_restrictedResidual m hm (parameterFromEpsilon ε) 1 hCF).differentiableAt
      (by norm_num)).hasFDerivAt
  have hd := T.hasFDerivAt.comp h (hdR.comp h Q.hasFDerivAt)
  have heq : (fun z : BlowupCoordinates m d => blowupResidual hm ε z) =ᶠ[𝓝 h]
      (fun z : BlowupCoordinates m d => T (R (Q z))) := by
    have hnear : ∀ᶠ z in 𝓝 h, z ∈ r.neighborhood := by
      change r.neighborhood ∈ 𝓝 h
      exact r.neighborhood_open.mem_nhds hh
    apply hnear.mono
    intro z hz
    have hsep := (separated_of_uniformDistanceBound r.delta_pos
      (r.distances ε hparam z hz)).1
    exact blowupResidual_eq_transformed_physical hm hε z hsep
  exact (hd.congr_of_eventuallyEq heq).fderiv

theorem originalNondegenerate_of_zeroRectangle {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d}
    (r : ZeroRectangle hm d seed) {ε : ℝ} (hε : 0 < ε) (hη : ε < r.eta)
    (h : BlowupCoordinates m d) (hh : h ∈ r.neighborhood) :
    OriginalNondegenerate m (parameterFromEpsilon ε) (physicalCoordinates ε h) := by
  let Q := coordinateContinuousEquivalence hm d (ne_of_gt hε)
  let T := residualTContinuousEquivalence hm d (ne_of_gt hε)
  let R := restrictedResidual m (parameterFromEpsilon ε)
  let J := fderiv ℝ R (Q h)
  have hparam := positive_parameter_mem r hε hη
  have hb := r.distances ε hparam h hh
  have hCF : CollisionFree ((Q h : W m) : Configuration) :=
    physicalCoordinates_collisionFree_of_distances hε r.delta_pos h hb
  have hdR : DifferentiableAt ℝ R (Q h) :=
    (contDiffAt_restrictedResidual m hm (parameterFromEpsilon ε) 1 hCF).differentiableAt
      (by norm_num)
  have hJ := r.derivative_invertible ε hparam h hh
  have hmap := derivative_physical_identity_on_rectangle hm r hε hη h hh
  rw [hmap] at hJ
  have hRinv : J.IsInvertible := by
    exact ContinuousLinearMap.isInvertible_comp_equiv.mp
      (ContinuousLinearMap.isInvertible_equiv_comp.mp hJ)
  refine ⟨physicalCoordinates_mem_W ε h, ?_⟩
  change Nondegenerate m (parameterFromEpsilon ε) (Q h)
  exact ⟨hdR, hRinv.bijective⟩

end FourBody.LocalBranch

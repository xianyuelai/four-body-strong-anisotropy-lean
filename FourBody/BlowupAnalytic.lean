import FourBody.BlowupPhysicalBridge
import FourBody.BlowupZero
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Tactic.FinCases

/-!
Joint real analyticity of the actual four components of the v2 residual F.
Frozen manuscript SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

The source point is (0, seed), with seed satisfying the concrete IsSeed.
Internal separation is derived from its literal ordered scalar solutions.
Cross-block separation at zero is derived from its ordered outer Y values.
A common positive distance margin and a genuine product rectangle are
obtained from all sixteen actual label pairs. No analytic, implicit-function,
seed existence, or seed Jacobian conclusion occurs as an input hypothesis.

The order n below is in ℕ∞ω. The analytic conclusion uses n=ω, not n=∞.
Subtype-valued regularity is obtained by an actual continuous linear
projection along a proved complement of the finite-dimensional kernel.

Static candidate only: this file has not yet been checked by Lean.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace FourBody.BlowupAnalytic

abbrev Variables (m : Masses) (d : OrderedClusterDatum) :=
  ℝ × BlowupCoordinates m d

def pointPairLM : (ℝ × ℝ) →ₗ[ℝ] Point where
  toFun v := !₂[v.1, v.2]
  map_add' v w := by
    ext k
    fin_cases k <;> simp [PiLp.add_apply]
  map_smul' a v := by
    ext k
    fin_cases k <;> simp [PiLp.smul_apply, smul_eq_mul]

def pointPairCLM : (ℝ × ℝ) →L[ℝ] Point :=
  pointPairLM.toContinuousLinearMap

@[simp] theorem pointPairCLM_apply (v : ℝ × ℝ) :
    pointPairCLM v = !₂[v.1, v.2] := rfl

theorem ambientCoordinates_joint_contDiff (n : ℕ∞ω)
    (m : Masses) (d : OrderedClusterDatum) :
    ContDiff ℝ n (fun p : Variables m d => p.2.val) :=
  (coordinateSpace m d).subtypeL.contDiff.comp contDiff_snd

theorem outerH_joint_contDiff (n : ℕ∞ω) (m : Masses)
    (d : OrderedClusterDatum) (a : BlockIndex d) :
    ContDiff ℝ n (fun p : Variables m d => outerH p.2 a) :=
  (contDiff_apply ℝ ℝ a).comp
    (ambientCoordinates_joint_contDiff n m d).fst.fst

theorem outerY_joint_contDiff (n : ℕ∞ω) (m : Masses)
    (d : OrderedClusterDatum) (a : BlockIndex d) :
    ContDiff ℝ n (fun p : Variables m d => outerY p.2 a) :=
  (contDiff_apply ℝ ℝ a).comp
    (ambientCoordinates_joint_contDiff n m d).fst.snd

theorem innerU_joint_contDiff (n : ℕ∞ω) (m : Masses)
    (d : OrderedClusterDatum) (i : Label) :
    ContDiff ℝ n (fun p : Variables m d => innerU p.2 i) :=
  (contDiff_apply ℝ ℝ i).comp
    (ambientCoordinates_joint_contDiff n m d).snd.fst

theorem innerV_joint_contDiff (n : ℕ∞ω) (m : Masses)
    (d : OrderedClusterDatum) (i : Label) :
    ContDiff ℝ n (fun p : Variables m d => innerV p.2 i) :=
  (contDiff_apply ℝ ℝ i).comp
    (ambientCoordinates_joint_contDiff n m d).snd.snd

theorem internalCoordinates_joint_contDiff (n : ℕ∞ω)
    (m : Masses) (d : OrderedClusterDatum) (i : Label) :
    ContDiff ℝ n (fun p : Variables m d => internalCoordinates p.2 i) :=
  pointPairCLM.contDiff.comp
    ((innerU_joint_contDiff n m d i).prodMk (innerV_joint_contDiff n m d i))

theorem physicalCoordinates_joint_contDiff (n : ℕ∞ω)
    (m : Masses) (d : OrderedClusterDatum) (i : Label) :
    ContDiff ℝ n (fun p : Variables m d => physicalCoordinates p.1 p.2 i) := by
  have hx : ContDiff ℝ n (fun p : Variables m d =>
      p.1 * outerH p.2 (blockOf d i) + p.1 * innerU p.2 i) :=
    (contDiff_fst.mul (outerH_joint_contDiff n m d (blockOf d i))).add
      (contDiff_fst.mul (innerU_joint_contDiff n m d i))
  have hy : ContDiff ℝ n (fun p : Variables m d =>
      outerY p.2 (blockOf d i) + p.1 * innerV p.2 i) :=
    (outerY_joint_contDiff n m d (blockOf d i)).add
      (contDiff_fst.mul (innerV_joint_contDiff n m d i))
  exact pointPairCLM.contDiff.comp (hx.prodMk hy)

theorem crossDifference_joint_contDiff (n : ℕ∞ω)
    (m : Masses) (d : OrderedClusterDatum) (i j : Label) :
    ContDiff ℝ n (fun p : Variables m d => crossDifference p.1 p.2 i j) := by
  have hd := (physicalCoordinates_joint_contDiff n m d i).sub
    (physicalCoordinates_joint_contDiff n m d j)
  have he : (fun p : Variables m d => crossDifference p.1 p.2 i j) =
      (fun p : Variables m d =>
        physicalCoordinates p.1 p.2 i - physicalCoordinates p.1 p.2 j) :=
    funext (fun p => crossDifference_eq_sub p.1 p.2 i j)
  rw [he]
  exact hd

theorem internalRho_joint_continuous (m : Masses)
    (d : OrderedClusterDatum) (i j : Label) :
    Continuous (fun p : Variables m d => internalRho p.2 i j) :=
  (internalCoordinates_joint_contDiff 0 m d i).continuous.dist
    (internalCoordinates_joint_contDiff 0 m d j).continuous

theorem crossNorm_joint_continuous (m : Masses)
    (d : OrderedClusterDatum) (i j : Label) :
    Continuous (fun p : Variables m d => ‖crossDifference p.1 p.2 i j‖) :=
  (crossDifference_joint_contDiff 0 m d i j).continuous.norm

/-- Two distinct actual labels in a seed's actual block have different U. -/
theorem seed_innerU_ne {m : Masses} {d : OrderedClusterDatum}
    {seed : BlowupCoordinates m d} (hs : IsSeed m d seed)
    (i j : Label) (hblock : blockOf d i = blockOf d j) (hij : i ≠ j) :
    innerU seed i ≠ innerU seed j := by
  let a : BlockIndex d := blockOf d i
  have hi : i ∈ datumBlock d a := label_mem_blockOf d i
  have hj : j ∈ datumBlock d a := by
    simpa only [a, hblock] using label_mem_blockOf d j
  obtain ⟨ki, hki⟩ := (List.exists_mem_iff_get (l := datumBlock d a)
    (p := fun k => k = i)).mp ⟨i, hi, rfl⟩
  obtain ⟨kj, hkj⟩ := (List.exists_mem_iff_get (l := datumBlock d a)
    (p := fun k => k = j)).mp ⟨j, hj, rfl⟩
  have hindex : ki ≠ kj := by
    intro heq
    apply hij
    rw [← hki, ← hkj, heq]
  have hdistinct := (hs.2.2.2.2 a).2.1 ki kj hindex
  simpa only [internalLabel, hki, hkj] using hdistinct

theorem seed_internallySeparated {m : Masses} {d : OrderedClusterDatum}
    {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) :
    InternallySeparated seed := by
  intro i j hblock hij heq
  apply seed_innerU_ne hs i j hblock hij
  simpa [internalCoordinates] using congrArg (fun q : Point => q 0) heq

theorem seed_internalRho_pos {m : Masses} {d : OrderedClusterDatum}
    {seed : BlowupCoordinates m d} (hs : IsSeed m d seed)
    (i j : Label) (hblock : blockOf d i = blockOf d j) (hij : i ≠ j) :
    0 < internalRho seed i j :=
  dist_pos.mpr (seed_internallySeparated hs i j hblock hij)

/-- Cross-block zero-scale displacement is the actual nonzero ordered Y gap. -/
theorem seed_crossDifference_ne_zero {m : Masses} {d : OrderedClusterDatum}
    {seed : BlowupCoordinates m d} (hs : IsSeed m d seed)
    (i j : Label) (hblock : blockOf d i ≠ blockOf d j) :
    crossDifference 0 seed i j ≠ 0 := by
  intro heq
  have hy : outerY seed (blockOf d i) - outerY seed (blockOf d j) = 0 := by
    simpa [crossDifference] using congrArg (fun q : Point => q 1) heq
  exact hblock (hs.2.2.1.injective (sub_eq_zero.mp hy))

def CrossSeparated {m : Masses} {d : OrderedClusterDatum}
    (p : Variables m d) : Prop :=
  ∀ i j, blockOf d i ≠ blockOf d j → crossDifference p.1 p.2 i j ≠ 0

/-- A continuous positive gap for every label pair. The diagonal is 1 so
the minimum is well-defined even when a required pair family is empty. -/
def pairGap {m : Masses} {d : OrderedClusterDatum}
    (p : Variables m d) (i j : Label) : ℝ :=
  if blockOf d i = blockOf d j then
    if i = j then 1 else internalRho p.2 i j
  else ‖crossDifference p.1 p.2 i j‖

theorem pairGap_continuous (m : Masses) (d : OrderedClusterDatum)
    (i j : Label) : Continuous (fun p : Variables m d => pairGap p i j) := by
  by_cases hb : blockOf d i = blockOf d j
  · by_cases hij : i = j
    · simpa [pairGap, hb, hij] using
        (continuous_const : Continuous (fun _ : Variables m d => (1 : ℝ)))
    · simpa [pairGap, hb, hij] using internalRho_joint_continuous m d i j
  · simpa [pairGap, hb] using crossNorm_joint_continuous m d i j

theorem pairGap_seed_pos {m : Masses} {d : OrderedClusterDatum}
    {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) (i j : Label) :
    0 < pairGap (0, seed) i j := by
  by_cases hb : blockOf d i = blockOf d j
  · by_cases hij : i = j
    · simp [pairGap, hij]
    · simpa [pairGap, hb, hij] using seed_internalRho_pos hs i j hb hij
  · simpa [pairGap, hb] using norm_pos_iff.mpr (seed_crossDifference_ne_zero hs i j hb)

/-- Elementary finite minimum argument, also valid for the empty type. -/
theorem finite_positive_lower_bound {κ : Type*} [Fintype κ]
    (f : κ → ℝ) (hf : ∀ k, 0 < f k) : ∃ δ : ℝ, 0 < δ ∧ ∀ k, δ < f k := by
  classical
  have hfin : ∀ S : Finset κ, ∃ δ : ℝ, 0 < δ ∧ ∀ k ∈ S, δ < f k := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert a S _ha ih =>
      obtain ⟨δ, hδ, hS⟩ := ih
      refine ⟨min δ (f a / 2), lt_min hδ (half_pos (hf a)), ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with hka | hkS
      · subst k
        exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self (hf a))
      · exact lt_of_le_of_lt (min_le_left _ _) (hS k hkS)
  obtain ⟨δ, hδ, hall⟩ := hfin Finset.univ
  exact ⟨δ, hδ, fun k => hall k (Finset.mem_univ k)⟩

def UniformDistanceBound {m : Masses} {d : OrderedClusterDatum}
    (δ : ℝ) (p : Variables m d) : Prop :=
  (∀ i j, blockOf d i = blockOf d j → i ≠ j → δ < internalRho p.2 i j) ∧
  ∀ i j, blockOf d i ≠ blockOf d j → δ < ‖crossDifference p.1 p.2 i j‖

theorem uniformDistanceBound_of_pairGap {m : Masses} {d : OrderedClusterDatum}
    {δ : ℝ} {p : Variables m d} (h : ∀ i j, δ < pairGap p i j) :
    UniformDistanceBound δ p := by
  constructor
  · intro i j hb hij
    simpa only [pairGap, if_pos hb, if_neg hij] using h i j
  · intro i j hb
    simpa only [pairGap, if_neg hb] using h i j

theorem separated_of_uniformDistanceBound {m : Masses} {d : OrderedClusterDatum}
    {δ : ℝ} (hδ : 0 < δ) {p : Variables m d} (hp : UniformDistanceBound δ p) :
    InternallySeparated p.2 ∧ CrossSeparated p := by
  constructor
  · intro i j hb hij
    exact dist_pos.mp (hδ.trans (hp.1 i j hb hij))
  · intro i j hb
    exact norm_pos_iff.mp (hδ.trans (hp.2 i j hb))

/-- The actual interval times an actual open ball, with fixed distance margin. -/
theorem seed_positive_distance_rectangle {m : Masses} {d : OrderedClusterDatum}
    {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) :
    ∃ η δ : ℝ, 0 < η ∧ 0 < δ ∧
      ∀ ε ∈ Ioo (-η) η, ∀ h ∈ Metric.ball seed η,
        UniformDistanceBound δ (ε, h) := by
  obtain ⟨δ, hδ, hgap⟩ := finite_positive_lower_bound
    (fun k : Label × Label => pairGap (0, seed) k.1 k.2)
    (fun k => pairGap_seed_pos hs k.1 k.2)
  have he : ∀ᶠ p : Variables m d in 𝓝 (0, seed), ∀ i j, δ < pairGap p i j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact continuousAt_const.eventually_lt (pairGap_continuous m d i j).continuousAt
      (hgap (i, j))
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff_ball.mp he
  refine ⟨η, δ, hη, hδ, ?_⟩
  intro ε hε h hh
  have hεball : ε ∈ Metric.ball (0 : ℝ) η := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using abs_lt.mpr hε
  have hp : (ε, h) ∈ Metric.ball (0, seed) η := by
    rw [← ball_prod_same]
    exact ⟨hεball, hh⟩
  exact uniformDistanceBound_of_pairGap (hball (ε, h) hp)

/-- The physical sign bridge preserves joint C^n and, in particular, C^ω. -/
theorem physicalNewtonForce_joint_contDiffAt (n : ℕ∞ω) (mass : ℝ)
    (v : Point × Point) (hsep : v.1 ≠ v.2) :
    ContDiffAt ℝ n (fun w : Point × Point =>
      Reuse.physicalNewtonForce mass w.1 w.2) v := by
  have hd := (Reuse.newtonTargetField_joint_contDiffAt n v hsep).const_smul mass
  have he : (fun w : Point × Point => Reuse.physicalNewtonForce mass w.1 w.2) =
      (fun w : Point × Point => -(mass • Reuse.newtonTargetField w.1 w.2)) :=
    funext (fun w => Reuse.physicalNewtonForce_eq_neg_legacy mass w.1 w.2)
  rw [he]
  exact hd.neg

theorem innerField_joint_contDiffAt (n : ℕ∞ω)
    {m : Masses} {d : OrderedClusterDatum} (p : Variables m d)
    (hsep : InternallySeparated p.2) (i : Label) :
    ContDiffAt ℝ n (fun w : Variables m d => innerField w.2 i) p := by
  classical
  unfold innerField internalFieldOn
  apply ContDiffAt.sum
  intro j hj
  have hjmem := (Finset.mem_erase.mp hj).2
  have hb : blockOf d j = blockOf d i :=
    blockOf_eq_of_mem d (by simpa [datumBlockLabels] using hjmem)
  have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
  have hd := (physicalNewtonForce_joint_contDiffAt n (m j)
    (internalCoordinates p.2 j, internalCoordinates p.2 i)
    (hsep i j hb.symm hij).symm).comp p
      ((internalCoordinates_joint_contDiff n m d j).contDiffAt.prodMk
        (internalCoordinates_joint_contDiff n m d i).contDiffAt)
  simpa only [Function.comp_def] using hd

theorem externalField_joint_contDiffAt (n : ℕ∞ω)
    {m : Masses} {d : OrderedClusterDatum} (p : Variables m d)
    (hsep : CrossSeparated p) (i : Label) :
    ContDiffAt ℝ n (fun w : Variables m d => externalField w.1 w.2 i) p := by
  classical
  unfold externalField
  apply ContDiffAt.sum
  intro j _hj
  by_cases hb : blockOf d j ≠ blockOf d i
  · have hp : physicalCoordinates p.1 p.2 j ≠ physicalCoordinates p.1 p.2 i := by
      intro heq
      apply hsep i j hb.symm
      rw [crossDifference_eq_sub, heq, sub_self]
    have hd := (physicalNewtonForce_joint_contDiffAt n (m j)
      (physicalCoordinates p.1 p.2 j, physicalCoordinates p.1 p.2 i) hp).comp p
        ((physicalCoordinates_joint_contDiff n m d j).contDiffAt.prodMk
          (physicalCoordinates_joint_contDiff n m d i).contDiffAt)
    simpa only [if_pos hb, Function.comp_def] using hd
  · simpa only [if_neg hb] using
      (contDiffAt_const : ContDiffAt ℝ n (fun _ : Variables m d => (0 : Point)) p)

theorem externalMean_joint_contDiffAt (n : ℕ∞ω)
    {m : Masses} {d : OrderedClusterDatum} (p : Variables m d)
    (hsep : CrossSeparated p) (a : BlockIndex d) :
    ContDiffAt ℝ n (fun w : Variables m d => externalMean w.1 w.2 a) p := by
  unfold externalMean datumBlockMean
  exact (ContDiffAt.sum (fun i _ =>
    (externalField_joint_contDiffAt n p hsep i).const_smul (m i))).const_smul
      (datumBlockMass m d a)⁻¹

theorem pointCoordinate_contDiffAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → Point} {p : E} {n : ℕ∞ω}
    (hf : ContDiffAt ℝ n f p) (k : Axis) :
    ContDiffAt ℝ n (fun w => f w k) p :=
  (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.contDiffAt.comp p hf

/-- All four literal residual components, with the powers ε² and ε³ retained. -/
theorem blowupResidualAmbient_joint_contDiffAt (n : ℕ∞ω)
    {m : Masses} {d : OrderedClusterDatum} (p : Variables m d)
    (hinner : InternallySeparated p.2) (hcross : CrossSeparated p) :
    ContDiffAt ℝ n (fun w : Variables m d => blowupResidualAmbient w.1 w.2) p := by
  have hi (i : Label) (k : Axis) :=
    pointCoordinate_contDiffAt (innerField_joint_contDiffAt n p hinner i) k
  have he (i : Label) (k : Axis) :=
    pointCoordinate_contDiffAt (externalField_joint_contDiffAt n p hcross i) k
  have hm (a : BlockIndex d) (k : Axis) :=
    pointCoordinate_contDiffAt (externalMean_joint_contDiffAt n p hcross a) k
  have hH (a : BlockIndex d) := (outerH_joint_contDiff n m d a).contDiffAt (x := p)
  have hY (a : BlockIndex d) := (outerY_joint_contDiff n m d a).contDiffAt (x := p)
  have hU (i : Label) := (innerU_joint_contDiff n m d i).contDiffAt (x := p)
  have hV (i : Label) := (innerV_joint_contDiff n m d i).contDiffAt (x := p)
  have hε : ContDiffAt ℝ n (fun w : Variables m d => w.1) p := contDiffAt_fst
  unfold blowupResidualAmbient
  apply ContDiffAt.prodMk
  · apply ContDiffAt.prodMk
    · apply contDiffAt_pi'
      intro a
      exact ((hε.pow 2).mul (hm a 0)).sub (hH a)
    · apply contDiffAt_pi'
      intro a
      exact (hm a 1).sub (hY a)
  · apply ContDiffAt.prodMk
    · apply contDiffAt_pi'
      intro i
      exact ((hi i 0).add ((hε.pow 2).mul ((he i 0).sub (hm (blockOf d i) 0)))).sub
        (hU i)
    · apply contDiffAt_pi'
      intro i
      exact ((hi i 1).add ((hε.pow 2).mul ((he i 1).sub (hm (blockOf d i) 1)))).sub
        ((hε.pow 3).mul (hV i))

/-- Subtype regularity is proved using a genuine finite-dimensional retraction;
the residual's already proved membership makes the projection exactly F. -/
theorem blowupResidual_joint_contDiffAt (n : ℕ∞ω)
    {m : Masses} (hm : PositiveMasses m) {d : OrderedClusterDatum}
    (p : Variables m d) (hinner : InternallySeparated p.2) (hcross : CrossSeparated p) :
    ContDiffAt ℝ n (fun w : Variables m d => blowupResidual hm w.1 w.2) p := by
  obtain ⟨Q, hQ⟩ := (coordinateSpace m d).exists_isCompl
  let P : CoordinateAmbient d →L[ℝ] BlowupCoordinates m d :=
    ((coordinateSpace m d).projectionOnto Q hQ).toContinuousLinearMap
  have hP (w : Variables m d) : P (blowupResidualAmbient w.1 w.2) =
      blowupResidual hm w.1 w.2 := by
    exact Submodule.projectionOnto_apply_of_mem_left hQ
      (blowupResidualAmbient_mem hm w.1 w.2)
  have hEq : (fun w : Variables m d => blowupResidual hm w.1 w.2) =
      (fun w : Variables m d => P (blowupResidualAmbient w.1 w.2)) :=
    funext (fun w => (hP w).symm)
  rw [hEq]
  exact P.contDiff.contDiffAt.comp p
    (blowupResidualAmbient_joint_contDiffAt n p hinner hcross)

theorem blowupResidual_joint_analyticAt {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (p : Variables m d)
    (hinner : InternallySeparated p.2) (hcross : CrossSeparated p) :
    AnalyticAt ℝ (fun w : Variables m d => blowupResidual hm w.1 w.2) p :=
  (blowupResidual_joint_contDiffAt ω hm p hinner hcross).analyticAt

theorem blowupResidual_seed_joint_analyticAt {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) :
    AnalyticAt ℝ (fun w : Variables m d => blowupResidual hm w.1 w.2) (0, seed) :=
  blowupResidual_joint_analyticAt hm (0, seed) (seed_internallySeparated hs)
    (seed_crossDifference_ne_zero hs)

/-- Fixed η, N and positive distance margin for the actual F on both signs
of ε. Positive ε will only be required by the physical force bridge. -/
theorem blowupResidual_seed_analytic_rectangle {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) :
    ∃ η δ : ℝ, ∃ N : Set (BlowupCoordinates m d),
      0 < η ∧ 0 < δ ∧ IsOpen N ∧ seed ∈ N ∧
      IsOpen (Ioo (-η) η ×ˢ N) ∧ (0, seed) ∈ (Ioo (-η) η ×ˢ N) ∧
      (∀ ε ∈ Ioo (-η) η, ∀ h ∈ N, UniformDistanceBound δ (ε, h)) ∧
      AnalyticOnNhd ℝ (fun w : Variables m d => blowupResidual hm w.1 w.2)
        (Ioo (-η) η ×ˢ N) := by
  obtain ⟨η, δ, hη, hδ, hbound⟩ := seed_positive_distance_rectangle hs
  refine ⟨η, δ, Metric.ball seed η, hη, hδ, Metric.isOpen_ball,
    Metric.mem_ball_self hη, isOpen_Ioo.prod Metric.isOpen_ball,
    ⟨⟨neg_lt_zero.mpr hη, hη⟩, Metric.mem_ball_self hη⟩, hbound, ?_⟩
  intro p hp
  have hsep := separated_of_uniformDistanceBound hδ
    (hbound p.1 hp.1 p.2 hp.2)
  exact blowupResidual_joint_analyticAt hm p hsep.1 hsep.2

end FourBody.BlowupAnalytic

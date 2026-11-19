import FourBody.Diameter
import FourBody.StatementDefinitions
import Mathlib.Topology.Sequences
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The starting subsequence in Proposition 3.2

Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
The source proof starts with Lemma 2.1 and an arbitrary original solution
sequence sν → +∞. This file retains arbitrary real sν at EVERY input index:
positivity is eventual, and sφν > 1 is a conclusion of the tail selection.

The compact set is the concrete closed cube in Label → ℝ. Its compactness
is proved from isCompact_Icc and the product theorem, rather than assumed
as a compactness interface. ONE strictly increasing subsequence makes the
whole vector of four vertical coordinates converge.

This is only the initial unscaled limit. It asserts no seed equations,
scaled internal compactness, H = O(ε³), branch membership or completeness.
Compilation status is recorded outside this file; proof text is not itself
a checked result.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace FourBody.SequenceStart

/-- The mass-dependent bound coming from the actual vertical diameter. -/
def verticalBound (m : Masses) : ℝ :=
  3 * (totalMass m) ^ ((1 : ℝ) / 3)

/-- The simultaneous tuple of the four physical vertical coordinates. -/
def verticalCoordinates (q : Configuration) : Label → ℝ :=
  fun i => q i 1

/-- Concrete cube, in the actual product topology on the four coordinates. -/
def verticalCube (m : Masses) : Set (Label → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (-verticalBound m) (verticalBound m))

theorem verticalBound_pos {m : Masses} (hm : PositiveMasses m) :
    0 < verticalBound m := by
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (totalMass_pos hm) _)

theorem epsilon_pos {s : ℝ} (hs : 0 < s) : 0 < epsilon s := by
  exact Real.rpow_pos_of_pos hs _

theorem epsilon_eq_inv {s : ℝ} (hs : 0 < s) :
    epsilon s = (s ^ ((1 : ℝ) / 3))⁻¹ := by
  have he : -(1 : ℝ) / 3 = -((1 : ℝ) / 3) := by ring
  change s ^ (-(1 : ℝ) / 3) = (s ^ ((1 : ℝ) / 3))⁻¹
  rw [he, Real.rpow_neg hs.le]

theorem epsilon_cube {s : ℝ} (hs : 0 < s) : epsilon s ^ 3 = s⁻¹ := by
  have hroot : (s ^ ((1 : ℝ) / 3)) ^ 3 = s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    norm_num
  rw [epsilon_eq_inv hs, inv_pow, hroot]

/-- The positive-tail physical parameter is the literal inverse cube used
in the branch specification, not an independently chosen parameter. -/
theorem parameterFromEpsilon_epsilon {s : ℝ} (hs : 0 < s) :
    parameterFromEpsilon (epsilon s) = s := by
  rw [parameterFromEpsilon, epsilon_cube hs, inv_inv]

/-- The negative power tends to zero for every real sequence going to +∞. -/
theorem epsilon_tendsto_zero {s : ℕ → ℝ}
    (hs : Tendsto s atTop atTop) :
    Tendsto (fun ν => epsilon (s ν)) atTop (nhds 0) := by
  have he : -(1 : ℝ) / 3 = -((1 : ℝ) / 3) := by ring
  change Tendsto (fun ν => s ν ^ (-(1 : ℝ) / 3)) atTop (nhds 0)
  simpa only [he, Function.comp_def] using
    (_root_.tendsto_rpow_neg_atTop (by norm_num : 0 < (1 : ℝ) / 3)).comp hs

/-- Exact factorization of Lemma 2.1's horizontal root bound. -/
theorem horizontal_root_factor {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) :
    3 * (totalMass m / s) ^ ((1 : ℝ) / 3) =
      verticalBound m * epsilon s := by
  rw [Real.div_rpow (totalMass_pos hm).le hs.le, epsilon_eq_inv hs]
  unfold verticalBound
  ring

/-- Every physical horizontal coordinate converges to zero on the original
sequence. No positivity premise is imposed on its finite initial segment. -/
theorem horizontal_tendsto_zero {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration}
    (hs : Tendsto s atTop atTop)
    (hq : ∀ ν, IsSolution m (s ν) (q ν)) (i : Label) :
    Tendsto (fun ν => q ν i 0) atTop (nhds 0) := by
  have hbound : ∀ᶠ ν in atTop, ‖q ν i 0‖ ≤ verticalBound m * epsilon (s ν) := by
    filter_upwards [hs.eventually (eventually_gt_atTop (0 : ℝ))] with ν hν
    simpa only [Real.norm_eq_abs, horizontal_root_factor hm hν] using
      (solution_coordinate_abs_bounds hm hν (hq ν) i).1
  have hzero : Tendsto (fun ν => verticalBound m * epsilon (s ν))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (epsilon_tendsto_zero hs))
  exact squeeze_zero_norm' hbound hzero

theorem isCompact_verticalCube (m : Masses) : IsCompact (verticalCube m) := by
  exact isCompact_univ_pi (fun _ : Label => isCompact_Icc)

/-- All four vertical coordinates lie in the same fixed concrete cube
eventually, derived from the original equations and their exact centering. -/
theorem eventually_vertical_mem_cube {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration}
    (hs : Tendsto s atTop atTop) (hq : ∀ ν, IsSolution m (s ν) (q ν)) :
    ∀ᶠ ν in atTop, verticalCoordinates (q ν) ∈ verticalCube m := by
  filter_upwards [hs.eventually (eventually_gt_atTop (0 : ℝ))] with ν hν
  intro i _hi
  exact abs_le.mp (solution_coordinate_abs_bounds hm hν (hq ν) i).2

/-- Concrete simultaneous compactness extraction, before removing a prefix. -/
theorem exists_vertical_subsequence {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration}
    (hs : Tendsto s atTop atTop) (hq : ∀ ν, IsSolution m (s ν) (q ν)) :
    ∃ y : Label → ℝ, y ∈ verticalCube m ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Tendsto (fun ν => verticalCoordinates (q (ψ ν))) atTop (nhds y) := by
  simpa only [Function.comp_def] using
    (isCompact_verticalCube m).tendsto_subseq'
      (eventually_vertical_mem_cube hm hs hq).frequently

/-- The limit inherits the actual weighted vertical center, proved by taking
the finite sum limit of the original centered solution sequence. -/
theorem vertical_limit_center_zero {m : Masses}
    {s : ℕ → ℝ} {q : ℕ → Configuration}
    (hs : Tendsto s atTop atTop) (hq : ∀ ν, IsSolution m (s ν) (q ν))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {y : Label → ℝ}
    (hy : Tendsto (fun ν => verticalCoordinates (q (φ ν))) atTop (nhds y)) :
    (∑ i, m i * y i) = 0 := by
  have hlim : Tendsto (fun ν => ∑ i, m i * q (φ ν) i 1) atTop
      (nhds (∑ i, m i * y i)) := by
    apply tendsto_finsetSum
    intro i _hi
    exact tendsto_const_nhds.mul (tendsto_pi_nhds.mp hy i)
  have hcenter : ∀ᶠ ν in atTop, (∑ i, m i * q (φ ν) i 1) = 0 := by
    filter_upwards [(hs.comp hφ.tendsto_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))] with ν hν
    exact center_coordinate_zero (solution_center_zero m hν (hq (φ ν))) 1
  have hlim0 : Tendsto (fun ν => ∑ i, m i * q (φ ν) i 1)
      atTop (nhds 0) := by
    exact tendsto_const_nhds.congr' (hcenter.mono fun _ h => h.symm)
  exact tendsto_nhds_unique hlim hlim0

/-- The honest initial conclusion of Proposition 3.2, before scaled internal
extraction. The SAME φ witnesses all the parameter and coordinate claims. -/
def InitialVerticalLimit (m : Masses) (s : ℕ → ℝ) (q : ℕ → Configuration)
    (φ : ℕ → ℕ) (y : Label → ℝ) : Prop :=
  StrictMono φ ∧
  (∀ ν, 1 < s (φ ν)) ∧
  Tendsto (fun ν => s (φ ν)) atTop atTop ∧
  (∀ ν, 0 < epsilon (s (φ ν))) ∧
  Tendsto (fun ν => epsilon (s (φ ν))) atTop (nhds 0) ∧
  Tendsto (fun ν => verticalCoordinates (q (φ ν))) atTop (nhds y) ∧
  (∀ i : Label, Tendsto (fun ν => q (φ ν) i 0) atTop (nhds 0)) ∧
  (∀ i : Label, |y i| ≤ verticalBound m) ∧
  (∑ i, m i * y i) = 0

/-- Discarding one finite prefix AFTER joint extraction imposes sφν > 1
without strengthening the arbitrary input sequence hypothesis. -/
theorem exists_initial_vertical_limit {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration}
    (hs : Tendsto s atTop atTop) (hq : ∀ ν, IsSolution m (s ν) (q ν)) :
    ∃ φ : ℕ → ℕ, ∃ y : Label → ℝ, InitialVerticalLimit m s q φ y := by
  obtain ⟨y, hyCube, ψ, hψ, hy⟩ := exists_vertical_subsequence hm hs hq
  have hsψ : Tendsto (fun ν => s (ψ ν)) atTop atTop := hs.comp hψ.tendsto_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hsψ.eventually (eventually_gt_atTop (1 : ℝ)))
  let shift : ℕ → ℕ := fun ν => ν + N
  have hshift : StrictMono shift := by
    intro a b hab
    exact Nat.add_lt_add_right hab N
  let φ : ℕ → ℕ := fun ν => ψ (shift ν)
  have hφ : StrictMono φ := hψ.comp hshift
  have hsφ : Tendsto (fun ν => s (φ ν)) atTop atTop := hs.comp hφ.tendsto_atTop
  have hyφ : Tendsto (fun ν => verticalCoordinates (q (φ ν))) atTop (nhds y) :=
    hy.comp hshift.tendsto_atTop
  have hgt : ∀ ν, 1 < s (φ ν) := by
    intro ν
    exact hN (shift ν) (by dsimp [shift]; omega)
  refine ⟨φ, y, hφ, hgt, hsφ, ?_, epsilon_tendsto_zero hsφ, hyφ, ?_, ?_, ?_⟩
  · intro ν
    exact epsilon_pos (lt_trans (by norm_num) (hgt ν))
  · intro i
    exact (horizontal_tendsto_zero hm hs hq i).comp hφ.tendsto_atTop
  · intro i
    exact abs_le.mpr (hyCube i (Set.mem_univ i))
  · exact vertical_limit_center_zero hs hq hφ hyφ

end FourBody.SequenceStart


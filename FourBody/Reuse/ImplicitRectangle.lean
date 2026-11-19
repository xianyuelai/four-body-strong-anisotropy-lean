import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-! Minimal migration of CompactImplicit's actual partial-derivative and
fixed-rectangle proof. Unknown is generalized from Fin n -> Real to a
Banach space W, and smoothness from infinity to arbitrary nonzero n,
including analytic omega. No finite-dimensional reduction is required.
The actual four-body blow-up residual, analyticity and invertible seed
Jacobian are still separate obligations; this is not the paper's branch
theorem and supplies none of those hypotheses automatically.
-/
noncomputable section
open scoped ContDiff
open Filter Set Topology
namespace FourBody.Reuse.Implicit
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

def jacobian (F : P → W → W) (p : P) (y : W) : W →L[ℝ] W :=
  fderiv ℝ (F p) y

omit [CompleteSpace P] [CompleteSpace W] in
theorem jacobian_eq_partial (F : P → W → W) (p : P) (y : W)
    (hf : ContDiffAt ℝ 1 (Function.uncurry F) (p, y)) :
    jacobian F p y = (fderiv ℝ (Function.uncurry F) (p, y)).comp
      (ContinuousLinearMap.inr ℝ P (W)) := by
  have hd := hf.differentiableAt (by norm_num)
  have hh : HasFDerivAt (fun z : W => (p, z))
      (ContinuousLinearMap.inr ℝ P (W)) y := by
    convert! (hasFDerivAt_const p y).prodMk (hasFDerivAt_id y) using 1
  exact (hd.hasFDerivAt.comp y hh).fderiv

omit [CompleteSpace P] [CompleteSpace W] in
theorem jacobian_joint_continuousAt (F : P → W → W) (p : P)
    (y : W) (hf : ContDiffAt ℝ 1 (Function.uncurry F) (p, y)) :
    ContinuousAt (fun a : P × W => jacobian F a.1 a.2) (p, y) := by
  let f : (P × W) → W → W := fun z v => F z.1 v
  have hp : ContDiff ℝ 1 (fun z : (P × W) × W => (z.1.1, z.2)) := by
    fun_prop
  have h : ContDiffAt ℝ 1 (Function.uncurry f) ((p, y), y) := by
    convert! hf.comp ((p, y), y) hp.contDiffAt using 1
  exact (h.fderiv (contDiffAt_snd : ContDiffAt ℝ 0
    (fun z : P × W => z.2) (p, y)) (by norm_num)).continuousAt


theorem local_implicitFunction (n : ℕ∞ω) (hn : 1 ≤ n)
    (F : P → W → W) (p : P) (y : W)
    (hf : ContDiffAt ℝ n (Function.uncurry F) (p, y)) (hroot : F p y = 0)
    (hJ : (jacobian F p y).IsInvertible) :
    ∃ ψ : P → W, ψ p = y ∧ ContDiffAt ℝ n ψ p ∧
      (∀ᶠ q in 𝓝 p, F q (ψ q) = 0) ∧
      (∀ᶠ a : P × W in 𝓝 (p, y), F a.1 a.2 = 0 ↔ ψ a.1 = a.2) := by
  have hn0 : n ≠ 0 := ne_of_gt ((zero_lt_one : (0 : ℕ∞ω) < 1).trans_le hn)
  have hpartial : (fderiv ℝ (Function.uncurry F) (p, y) ∘L
      ContinuousLinearMap.inr ℝ P W).IsInvertible := by
    rwa [← jacobian_eq_partial F p y (hf.of_le hn)]
  let ψ := hf.implicitFunction hn0 hpartial
  refine ⟨ψ, hf.implicitFunction_apply_self hn0 hpartial,
    hf.contDiffAt_implicitFunction hn0 hpartial, ?_, ?_⟩
  · simpa only [Function.uncurry, hroot] using hf.eventually_apply_implicitFunction hn0 hpartial
  · simpa only [Function.uncurry, hroot] using hf.eventually_apply_eq_iff_implicitFunction hn0 hpartial

theorem local_rectangle (n : ℕ∞ω) (hn : 1 ≤ n)
    (F : P → W → W) (p : P) (y : W)
    (hf : ContDiffAt ℝ n (Function.uncurry F) (p, y)) (hroot : F p y = 0)
    (hJ : (jacobian F p y).IsInvertible) :
    ∃ ψ : P → W, ∃ η ζ : ℝ, 0 < η ∧ 0 < ζ ∧ ψ p = y ∧
      ContDiffAt ℝ n ψ p ∧ ∀ q, dist q p < η →
        dist (ψ q) y < ζ ∧ F q (ψ q) = 0 ∧
        (∀ z, dist z y < ζ → (F q z = 0 ↔ ψ q = z)) := by
  obtain ⟨ψ, hbase, hsmooth, hroots, huniq⟩ := local_implicitFunction n hn F p y hf hroot hJ
  obtain ⟨a, ha, hrootNear⟩ := Metric.eventually_nhds_iff.mp hroots
  obtain ⟨b, hb, huniqNear⟩ := Metric.eventually_nhds_iff.mp huniq
  have hψnear : ∀ᶠ q in 𝓝 p, dist (ψ q) y < b := by
    have h := hsmooth.continuousAt.tendsto.eventually (Metric.ball_mem_nhds (ψ p) hb)
    simpa only [Metric.mem_ball, hbase] using h
  obtain ⟨c, hc, hψNear⟩ := Metric.eventually_nhds_iff.mp hψnear
  refine ⟨ψ, min a (min b c), b, lt_min ha (lt_min hb hc), hb, hbase, hsmooth, ?_⟩
  intro q hq
  refine ⟨hψNear (lt_of_lt_of_le hq ((min_le_right _ _).trans (min_le_right _ _))),
    hrootNear (lt_of_lt_of_le hq (min_le_left _ _)), ?_⟩
  intro z hz
  apply huniqNear (y := (q, z))
  simpa only [Prod.dist_eq] using
    (max_lt (lt_of_lt_of_le hq ((min_le_right _ _).trans (min_le_left _ _))) hz)

theorem local_analytic_rectangle (F : P → W → W) (p : P) (y : W)
    (hf : AnalyticAt ℝ (Function.uncurry F) (p, y)) (hroot : F p y = 0)
    (hJ : (jacobian F p y).IsInvertible) :
    ∃ ψ : P → W, ∃ η ζ : ℝ, 0 < η ∧ 0 < ζ ∧ ψ p = y ∧
      AnalyticAt ℝ ψ p ∧ ∀ q, dist q p < η →
        dist (ψ q) y < ζ ∧ F q (ψ q) = 0 ∧
        (∀ z, dist z y < ζ → (F q z = 0 ↔ ψ q = z)) := by
  obtain ⟨ψ,η,ζ,hη,hζ,hbase,hsmooth,hgraph⟩ :=
    local_rectangle ω (by simp) F p y hf.contDiffAt hroot hJ
  exact ⟨ψ,η,ζ,hη,hζ,hbase,hsmooth.analyticAt,hgraph⟩

/-- Analyticity holds throughout the same parameter ball, after a
permitted shrinking. The fixed root-neighborhood and exact zero graph
are retained, so this is usable for signed epsilon intervals. -/
theorem local_analytic_rectangle_on_ball (F : P → W → W) (p : P) (y : W)
    (hf : AnalyticAt ℝ (Function.uncurry F) (p, y)) (hroot : F p y = 0)
    (hJ : (jacobian F p y).IsInvertible) :
    ∃ ψ : P → W, ∃ η ζ : ℝ, 0 < η ∧ 0 < ζ ∧ ψ p = y ∧
      AnalyticOnNhd ℝ ψ (Metric.ball p η) ∧ ∀ q, dist q p < η →
        dist (ψ q) y < ζ ∧ F q (ψ q) = 0 ∧
        (∀ z, dist z y < ζ → (F q z = 0 ↔ ψ q = z)) := by
  obtain ⟨ψ,η₀,ζ,hη₀,hζ,hbase,hanalytic,hgraph⟩ :=
    local_analytic_rectangle F p y hf hroot hJ
  obtain ⟨ρ,hρ,hball⟩ := hanalytic.exists_ball_analyticOnNhd
  refine ⟨ψ,min η₀ ρ,ζ,lt_min hη₀ hρ,hζ,hbase,?_,?_⟩
  · intro q hq
    apply hball q
    rw [Metric.mem_ball] at hq ⊢
    exact lt_of_lt_of_le hq (min_le_right _ _)
  · intro q hq
    exact hgraph q (lt_of_lt_of_le hq (min_le_left _ _))

end FourBody.Reuse.Implicit

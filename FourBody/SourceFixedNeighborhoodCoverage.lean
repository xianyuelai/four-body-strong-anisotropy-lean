import FourBody.GenuineSourceCountersequence
import FourBody.GlobalExhaustion
import FourBody.SourceCommonThreshold
import Mathlib.Algebra.Order.Ring.Basic

/-!
# Literal fixed-neighborhood coverage in frozen Pro v2 Section 5

Frozen manuscript raw SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
Source lines 665--676 and 701--706; S5-U03/U06/U16.

STATIC OWN-PREP CANDIDATE ONLY. This file has not been staged into the
formal project, elaborated, compiled, axiom-audited, or leanchecker checked.
The already frozen 38-item independent review is not changed by this file.

The countersequence is instantiated with the actual represented-coordinate
family in the SAME fixed N for every datum. The eventual epsilon coverage
is derived from Global's proved coverage and genuine local branches; it
does not accept eventual coverage as an input. Its local-family inputs are
discharged in the unconditional corollary by allDataLocalBranches.

The final common-range epsilon statement is a one-way corollary of the
already proved sourceCommonThreshold statement. It retains its same
seed/N/h and is never fed back into Main or GlobalExhaustion. It asserts
classification only in the original sufficiently-small epsilon range.
-/

noncomputable section
open Filter

namespace FourBody.SourceFixedNeighborhoodCoverage

/-- Configurations represented by genuine coordinates in any of the actual
fixed datum neighborhoods. It does not assume an equation or branch value. -/
def fixedNeighborhoodFamily (m : Masses)
    (N : ∀ d : OrderedClusterDatum, Set (BlowupCoordinates m d))
    (s : ℝ) : Set Configuration :=
  {q | ∃ d : OrderedClusterDatum, ∃ z : BlowupCoordinates m d,
    z ∈ N d ∧ RepresentsCoordinates m d (epsilon s) z q}

theorem mem_fixedNeighborhoodFamily_iff {m : Masses}
    (N : ∀ d : OrderedClusterDatum, Set (BlowupCoordinates m d))
    (s : ℝ) (q : Configuration) :
    q ∈ fixedNeighborhoodFamily m N s ↔
      ∃ d : OrderedClusterDatum, ∃ z : BlowupCoordinates m d,
        z ∈ N d ∧ RepresentsCoordinates m d (epsilon s) z q := Iff.rfl

/-- Missing this actual family means that EVERY true representing coordinate
for EVERY datum lies outside its fixed N, not merely that a branch value is missing. -/
theorem not_mem_fixedNeighborhoodFamily_iff_all_coordinates_outside {m : Masses}
    (N : ∀ d : OrderedClusterDatum, Set (BlowupCoordinates m d))
    (s : ℝ) (q : Configuration) :
    q ∉ fixedNeighborhoodFamily m N s ↔
      ∀ d : OrderedClusterDatum, ∀ z : BlowupCoordinates m d,
        RepresentsCoordinates m d (epsilon s) z q → z ∉ N d := by
  constructor
  · intro h d z hrep hz
    exact h ⟨d, z, hz, hrep⟩
  · intro h hmem
    obtain ⟨d, z, hz, hrep⟩ := hmem
    exact h d z hrep hz

/-- The source countersequence, with genuine original equations and literal
fixed-N nonmembership for all actual representing coordinates.
Index zero uses 1/(nu+1); at every nu>=1 the source 1/nu bound also holds. -/
theorem genuine_fixed_neighborhood_countersequence (m : Masses)
    (N : ∀ d : OrderedClusterDatum, Set (BlowupCoordinates m d))
    (η₁ : ℝ) (hη₁ : 0 < η₁)
    (hnot : ¬ CoverageSequence.EventuallyCovered m (fixedNeighborhoodFamily m N)) :
    ∃ s : ℕ → ℝ, ∃ q : ℕ → Configuration,
      (∀ ν : ℕ, GenuineSourceCountersequence.sourceCutoff η₁ ν < s ν) ∧
      Tendsto s atTop atTop ∧
      Tendsto (fun ν => epsilon (s ν)) atTop (nhds 0) ∧
      (∀ ν : ℕ,
        1 < s ν ∧ IsSolution m (s ν) (q ν) ∧
        parameterFromEpsilon (epsilon (s ν)) = s ν ∧
        0 < epsilon (s ν) ∧
        epsilon (s ν) < min η₁ (((ν : ℝ) + 1)⁻¹) ∧
        ∀ d : OrderedClusterDatum, ∀ z : BlowupCoordinates m d,
          RepresentsCoordinates m d (epsilon (s ν)) z (q ν) → z ∉ N d) ∧
      (∀ ν : ℕ, 1 ≤ ν → epsilon (s ν) < min η₁ ((ν : ℝ)⁻¹)) := by
  obtain ⟨s, q, hcut, hs, hεzero, hall, hsource⟩ :=
    GenuineSourceCountersequence.genuineSourceCountersequence
      m (fixedNeighborhoodFamily m N) η₁ hη₁ hnot
  refine ⟨s, q, hcut, hs, hεzero, ?_, hsource⟩
  intro ν
  obtain ⟨hsone, hsol, hmissing, hparameter, hεpos, hsmall⟩ := hall ν
  exact ⟨hsone, hsol, hparameter, hεpos, hsmall,
    (not_mem_fixedNeighborhoodFamily_iff_all_coordinates_outside N (s ν) (q ν)).mp hmissing⟩

/-- Strict inverse-cube monotonicity on actual positive epsilons. -/
theorem parameterFromEpsilon_lt_of_lt {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    parameterFromEpsilon b < parameterFromEpsilon a := by
  have hb : 0 < b := ha.trans hab
  have hcube : a ^ 3 < b ^ 3 :=
    pow_lt_pow_left₀ hab ha.le (by decide : (3 : ℕ) ≠ 0)
  exact (inv_lt_inv₀ (pow_pos hb 3) (pow_pos ha 3)).mpr hcube

/-- This inverse is proved from the actual epsilon cube identity; no
independent epsilon/parameter identification is assumed. -/
theorem epsilon_parameterFromEpsilon {ε : ℝ} (hε : 0 < ε) :
    epsilon (parameterFromEpsilon ε) = ε := by
  have hp : 0 < parameterFromEpsilon ε := inv_pos.mpr (pow_pos hε 3)
  have hc := TwoScale.epsilon_cube hp
  have hc' : epsilon (parameterFromEpsilon ε) ^ 3 = ε ^ 3 := by
    simpa only [parameterFromEpsilon, inv_inv] using hc
  exact (by decide : Odd 3).pow_injective hc'

/-- Literal eta2<=eta1 epsilon-form coverage, derived from the actual
Global exhaustion theorem and the same local family. This does NOT take
any coverage, limiting seed, count or datum-equivalence conclusion as input. -/
theorem eventual_fixed_neighborhood_epsilon_coverage {m : Masses}
    (hm : PositiveMasses m)
    (seed : ∀ d : OrderedClusterDatum, BlowupCoordinates m d)
    (eta : OrderedClusterDatum → ℝ)
    (N : ∀ d : OrderedClusterDatum, Set (BlowupCoordinates m d))
    (h : ∀ d : OrderedClusterDatum, ℝ → BlowupCoordinates m d)
    (hlocal : ∀ d, AnalyticLocalBranch m d (seed d) (eta d) (N d) (h d))
    (η₁ : ℝ) (hη₁ : 0 < η₁) :
    ∃ η₂ : ℝ, 0 < η₂ ∧ η₂ ≤ η₁ ∧ η₂ < 1 ∧
      (∀ d : OrderedClusterDatum, η₂ < eta d) ∧
      ∀ ε : ℝ, 0 < ε → ε < η₂ →
        ∀ q : Configuration, IsSolution m (parameterFromEpsilon ε) q →
          ∃ d : OrderedClusterDatum, ∃ z : BlowupCoordinates m d,
            z ∈ N d ∧ RepresentsCoordinates m d ε z q := by
  obtain ⟨r, hr, hrone, hreta⟩ :=
    finitePositiveCommonRange eta (fun d => (hlocal d).1)
  obtain ⟨S, hcovered⟩ :=
    Global.eventually_all_solutions_are_branch_values hm seed eta N h hlocal
  let T : ℝ := max 2 (S + 1)
  have hTpos : 0 < T :=
    (by norm_num : (0 : ℝ) < 2).trans_le (le_max_left _ _)
  have hST : S < T :=
    (by linarith : S < S + 1).trans_le (le_max_right _ _)
  have hεT : 0 < epsilon T := TwoScale.epsilon_pos hTpos
  let η₂ : ℝ := min η₁ (min r (epsilon T))
  have hη₂ : 0 < η₂ := lt_min hη₁ (lt_min hr hεT)
  have hη₂r : η₂ ≤ r := (min_le_right _ _).trans (min_le_left _ _)
  have hη₂T : η₂ ≤ epsilon T := (min_le_right _ _).trans (min_le_right _ _)
  have hη₂eta (d : OrderedClusterDatum) : η₂ < eta d := hη₂r.trans_lt (hreta d)
  refine ⟨η₂, hη₂, min_le_left _ _, hη₂r.trans_lt hrone, hη₂eta, ?_⟩
  intro ε hε hsmall q hsol
  have hεeta (d : OrderedClusterDatum) : ε < eta d := hsmall.trans (hη₂eta d)
  have hεltT : ε < epsilon T := hsmall.trans_le hη₂T
  have hTlarge : T < parameterFromEpsilon ε := by
    have hlarge := parameterFromEpsilon_lt_of_lt hε hεltT
    rw [parameterFromEpsilon_epsilon hTpos] at hlarge
    exact hlarge
  have hmember := hcovered (parameterFromEpsilon ε) (hST.trans hTlarge) q hsol
  obtain ⟨d, hrep⟩ := hmember
  have hinverse := epsilon_parameterFromEpsilon hε
  rw [hinverse] at hrep
  rcases hlocal d with ⟨_heta, _hN, _hseedN, _hseed, _hanalytic, _hzero, hphysical⟩
  exact ⟨d, h d ε, (hphysical ε hε (hεeta d)).1, hrep⟩

/-- Unconditional discharge of all local-family assumptions in the
preceding literal epsilon-coverage theorem, retaining its same seed/N/h. -/
theorem source_fixed_neighborhood_epsilon_coverage (m : Masses)
    (hm : PositiveMasses m) (η₁ : ℝ) (hη₁ : 0 < η₁) :
    ∃ seed : ∀ d : OrderedClusterDatum, BlowupCoordinates m d,
    ∃ eta : OrderedClusterDatum → ℝ,
    ∃ N : ∀ d : OrderedClusterDatum, Set (BlowupCoordinates m d),
    ∃ h : ∀ d : OrderedClusterDatum, ℝ → BlowupCoordinates m d,
      (∀ d, AnalyticLocalBranch m d (seed d) (eta d) (N d) (h d)) ∧
      ∃ η₂ : ℝ, 0 < η₂ ∧ η₂ ≤ η₁ ∧ η₂ < 1 ∧
        (∀ d : OrderedClusterDatum, η₂ < eta d) ∧
        ∀ ε : ℝ, 0 < ε → ε < η₂ →
          ∀ q : Configuration, IsSolution m (parameterFromEpsilon ε) q →
            ∃ d : OrderedClusterDatum, ∃ z : BlowupCoordinates m d,
              z ∈ N d ∧ RepresentsCoordinates m d ε z q := by
  classical
  choose seed eta N h hlocal using (LocalBranch.allDataLocalBranches m hm)
  exact ⟨seed, eta, N, h, hlocal,
    eventual_fixed_neighborhood_epsilon_coverage hm seed eta N h hlocal η₁ hη₁⟩

/-- The source's exact common eta and s0=eta^(-3), now in literal epsilon
form. The SAME seed/N/h supplies analyticity, physical uniqueness, every
actual original solution, exact counts and genuine geometric strata. -/
theorem source_literal_common_neighborhood_classification :
    ∀ m : Masses, PositiveMasses m →
      ∃ η : ℝ, 0 < η ∧ η < 1 ∧ 1 < parameterFromEpsilon η ∧
        Module.finrank ℝ (W m) = 6 ∧
        ∃ seed : ∀ d : OrderedClusterDatum, BlowupCoordinates m d,
        ∃ N : ∀ d : OrderedClusterDatum, Set (BlowupCoordinates m d),
        ∃ h : ∀ d : OrderedClusterDatum, ℝ → BlowupCoordinates m d,
          (∀ d, AnalyticLocalBranch m d (seed d) η (N d) (h d)) ∧
          ∀ ε : ℝ, 0 < ε → ε < η →
            ExactSolutionCounts m (parameterFromEpsilon ε) ∧
            AllSolutionsNondegenerate m (parameterFromEpsilon ε) ∧
            (∃ e : OrderedClusterDatum ≃ SolutionSpace m (parameterFromEpsilon ε),
              ∀ d : OrderedClusterDatum,
                RepresentsCoordinates m d ε (h d ε) (e d).val ∧
                DatumSolutionStrata d (e d).val) ∧
            (∀ q : Configuration, IsSolution m (parameterFromEpsilon ε) q →
              ∃ d : OrderedClusterDatum, ∃ z : BlowupCoordinates m d,
                z ∈ N d ∧ RepresentsCoordinates m d ε z q) := by
  intro m hm
  obtain ⟨η, hη, hηone, hs₀, hW, seed, N, h, hlocal, hmain⟩ :=
    sourceCommonThreshold m hm
  refine ⟨η, hη, hηone, hs₀, hW, seed, N, h, hlocal, ?_⟩
  intro ε hε hsmall
  have hs : parameterFromEpsilon η < parameterFromEpsilon ε :=
    parameterFromEpsilon_lt_of_lt hε hsmall
  obtain ⟨hcount, hND, e, he⟩ := hmain (parameterFromEpsilon ε) hs
  have hinverse := epsilon_parameterFromEpsilon hε
  have hrep (d : OrderedClusterDatum) :
      RepresentsCoordinates m d ε (h d ε) (e d).val := by
    simpa only [hinverse] using (he d).2.2.1
  have hstrata (d : OrderedClusterDatum) : DatumSolutionStrata d (e d).val :=
    (he d).2.2.2
  refine ⟨hcount, hND, ⟨e, fun d => ⟨hrep d, hstrata d⟩⟩, ?_⟩
  intro q hq
  obtain ⟨d, hd⟩ := e.surjective (⟨q, hq⟩ : SolutionSpace m (parameterFromEpsilon ε))
  have hqeq : (e d).val = q := congrArg Subtype.val hd
  rcases hlocal d with ⟨_heta, _hN, _hseedN, _hseed, _hanalytic, _hzero, hphysical⟩
  refine ⟨d, h d ε, (hphysical ε hε hsmall).1, ?_⟩
  rw [← hqeq]
  exact hrep d

end FourBody.SourceFixedNeighborhoodCoverage

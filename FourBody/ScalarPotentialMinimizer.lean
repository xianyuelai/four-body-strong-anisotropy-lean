import FourBody.ScalarPotentialProper
import FourBody.ScalarPotentialGradient
import FourBody.ScalarPotentialConstraint
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.AffineMap

/-!
Actual existence/uniqueness via the scalar potential, not a seed certificate.
Arbitrary finite positive masses are used with coefficient 1. The singleton
case is covered explicitly and all minimizing points are proved centered.
No statement in this module assumes an unproved minimizer or analysis API.
-/
noncomputable section
open scoped BigOperators
open Set Filter Topology

namespace FourBody.ScalarMinimizer

theorem scalarPotential_exists_minimizer {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) :
    ∃ z : ScalarVector n, z ∈ ambientChamber n ∧
      IsMinOn (scalarPotential μ) (ambientChamber n) z := by
  obtain ⟨z0, hz0⟩ := ambientChamber_nonempty n
  let S : Set (ScalarVector n) :=
    {z | z ∈ ambientChamber n ∧ scalarPotential μ z ≤ scalarPotential μ z0}
  have hcompact : IsCompact S := scalarPotential_compact_sublevel μ hμ _
  have hnonempty : S.Nonempty := ⟨z0, hz0, le_rfl⟩
  have hcontinuous : ContinuousOn (scalarPotential μ) S :=
    fun z hz => (scalarPotential_continuousAt μ z hz.1).continuousWithinAt
  obtain ⟨z, hz, hmin⟩ := hcompact.exists_isMinOn hnonempty hcontinuous
  refine ⟨z, hz.1, ?_⟩
  intro y hy
  by_cases hv : scalarPotential μ y ≤ scalarPotential μ z0
  · exact hmin ⟨hy, hv⟩
  · exact hz.2.trans (le_of_lt (lt_of_not_ge hv))

theorem scalarPotential_existsUnique_minimizer {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) :
    ∃! z : ScalarVector n, z ∈ ambientChamber n ∧
      IsMinOn (scalarPotential μ) (ambientChamber n) z := by
  obtain ⟨z, hz, hmin⟩ := scalarPotential_exists_minimizer μ hμ
  refine ⟨z, ⟨hz, hmin⟩, ?_⟩
  intro y hy
  exact (scalarPotential_strictConvexOn μ hμ).eq_of_isMinOn hy.2 hmin hy.1 hz

/-- Minimizing the literal energy forces the original weighted center to zero,
by translation invariance of pair distances and a genuine quadratic identity. -/
theorem scalarPotential_minimizer_centered {n : ℕ} (μ z : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (hz : z ∈ ambientChamber n)
    (hmin : IsMinOn (scalarPotential μ) (ambientChamber n) z) :
    z ∈ FourBody.ScalarGeometry.ScalarW μ := by
  by_cases hn : n = 0
  · subst n
    change (∑ i, μ i * z i) = 0
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let M : ℝ := ∑ i, μ i
    let S : ℝ := ∑ i, μ i * z i
    let a : ℝ := S / M
    have hM : 0 < M := FourBody.ScalarGeometry.totalMass_pos hnpos μ hμ
    have hSa : S = M * a := by
      dsimp [a]
      field_simp [ne_of_gt hM]
    have hshift := translate_mem_ambientChamber z hz a
    have hvalue : scalarPotential μ z ≤ scalarPotential μ (fun i => z i - a) :=
      hmin hshift
    have hidentity : scalarPotential μ (fun i => z i - a) =
        scalarPotential μ z - a * S + (a ^ 2 / 2) * M :=
      scalarPotential_translate μ z a
    have ha0 : a = 0 := by
      by_contra hane
      have hp : 0 < (M / 2) * a ^ 2 :=
        mul_pos (div_pos hM (by norm_num)) (sq_pos_of_ne_zero hane)
      rw [hSa] at hidentity
      nlinarith
    change S = 0
    rw [hSa, ha0, mul_zero]

theorem scalarPotential_existsUnique_centered_minimizer {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) :
    ∃! z : FourBody.ScalarGeometry.ScalarW μ,
      z ∈ FourBody.ScalarGeometry.chamber μ ∧
      IsMinOn (fun w : FourBody.ScalarGeometry.ScalarW μ => scalarPotential μ w.val)
        (FourBody.ScalarGeometry.chamber μ) z := by
  obtain ⟨x, hx, hmin⟩ := scalarPotential_exists_minimizer μ hμ
  let z : FourBody.ScalarGeometry.ScalarW μ :=
    ⟨x, scalarPotential_minimizer_centered μ x hμ hx hmin⟩
  have hz : z ∈ FourBody.ScalarGeometry.chamber μ := hx
  have hminz :
      IsMinOn (fun w : FourBody.ScalarGeometry.ScalarW μ => scalarPotential μ w.val)
        (FourBody.ScalarGeometry.chamber μ) z := by
    intro w hw
    exact hmin hw
  refine ⟨z, ⟨hz, hminz⟩, ?_⟩
  intro y hy
  have hminy : IsMinOn (scalarPotential μ) (ambientChamber n) y.val := by
    intro w hw
    have hyz : scalarPotential μ y.val ≤ scalarPotential μ z.val := hy.2 hz
    have hzw : scalarPotential μ z.val ≤ scalarPotential μ w := hmin hw
    exact hyz.trans hzw
  apply Subtype.ext
  exact (scalarPotential_strictConvexOn μ hμ).eq_of_isMinOn hminy hmin hy.1 hx

theorem scalarPotential_one_minimizer_eq_zero (μ z : ScalarVector 1)
    (hμ : ∀ i, 0 < μ i)
    (hmin : IsMinOn (scalarPotential μ) (ambientChamber 1) z) : z = 0 := by
  have hzero : (0 : ScalarVector 1) ∈ ambientChamber 1 := by
    intro i j hij
    have he : i = j := Subsingleton.elim _ _
    exact False.elim ((ne_of_lt hij) he)
  have hvalue : scalarPotential μ z ≤ scalarPotential μ (0 : ScalarVector 1) := hmin hzero
  rw [scalarPotential_one_formula, scalarPotential_one_formula] at hvalue
  have hz0 : z 0 = 0 := by
    have hpos := hμ 0
    by_contra hz0
    have hp : 0 < μ 0 * z 0 ^ 2 := mul_pos hpos (sq_pos_of_ne_zero hz0)
    norm_num at hvalue
    linarith
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact hz0

theorem scalarPotential_critical_isMinOn {n : ℕ} (μ z : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (hz : z ∈ ambientChamber n)
    (hcritical : fderiv ℝ (scalarPotential μ) z = 0) :
    IsMinOn (scalarPotential μ) (ambientChamber n) z := by
  intro y hy
  let L : ℝ →ᵃ[ℝ] ScalarVector n := AffineMap.lineMap z y
  have hconv := ((scalarPotential_strictConvexOn μ hμ).convexOn.comp_affineMap L).subset
    ((ambientChamber_convex n).mapsTo_lineMap hz hy) (convex_Icc (0 : ℝ) 1)
  have hd0 : HasFDerivAt (scalarPotential μ) (0 : ScalarVector n →L[ℝ] ℝ) z := by
    simpa only [hcritical] using (scalarPotential_hasFDerivAt μ z hz).differentiableAt.hasFDerivAt
  have hd : HasDerivAt ((scalarPotential μ) ∘ L) 0 0 := by
    have hbase : HasFDerivAt (scalarPotential μ) (0 : ScalarVector n →L[ℝ] ℝ) (L 0) := by
      simpa only [L, AffineMap.lineMap_apply_zero] using hd0
    simpa only [zero_apply] using hbase.comp_hasDerivAt 0
      (AffineMap.hasDerivAt_lineMap (a := z) (b := y) (x := (0 : ℝ)))
  have hs := hconv.le_slope_of_hasDerivAt (x := (0 : ℝ)) (y := (1 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hd
  have hvalue : 0 ≤ scalarPotential μ y - scalarPotential μ z := by
    simpa [slope, L] using hs
  exact sub_nonneg.mp hvalue

/-- Arbitrary Fin n, positive masses: the literal normalized one-dimensional
force equations have exactly one root in the prescribed increasing chamber. -/
theorem scalar_potential_root_existsUnique {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) :
    ∃! z : ScalarVector n, z ∈ ambientChamber n ∧
      ∀ i, FourBody.ScalarGeometry.scalarForce μ z i = z i := by
  obtain ⟨z, hz, hmin⟩ := scalarPotential_exists_minimizer μ hμ
  have hcritical : fderiv ℝ (scalarPotential μ) z = 0 :=
    (hmin.isLocalMin ((ambientChamber_isOpen n).mem_nhds hz)).fderiv_eq_zero
  have hroot := (scalarPotential_critical_iff_root μ z hμ hz).mp hcritical
  refine ⟨z, ⟨hz, hroot⟩, ?_⟩
  intro y hy
  have hminy := scalarPotential_critical_isMinOn μ y hμ hy.1
    ((scalarPotential_critical_iff_root μ y hμ hy.1).mpr hy.2)
  exact (scalarPotential_strictConvexOn μ hμ).eq_of_isMinOn hminy hmin hy.1 hz

theorem scalar_potential_root_existsUnique_centered {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) :
    ∃! z : ScalarVector n, z ∈ ambientChamber n ∧
      (∀ i, FourBody.ScalarGeometry.scalarForce μ z i = z i) ∧
      z ∈ FourBody.ScalarGeometry.ScalarW μ := by
  obtain ⟨z, hz, hmin⟩ := scalarPotential_exists_minimizer μ hμ
  have hcritical : fderiv ℝ (scalarPotential μ) z = 0 :=
    (hmin.isLocalMin ((ambientChamber_isOpen n).mem_nhds hz)).fderiv_eq_zero
  have hroot := (scalarPotential_critical_iff_root μ z hμ hz).mp hcritical
  refine ⟨z, ⟨hz, hroot, scalarPotential_minimizer_centered μ z hμ hz hmin⟩, ?_⟩
  intro y hy
  have hminy := scalarPotential_critical_isMinOn μ y hμ hy.1
    ((scalarPotential_critical_iff_root μ y hμ hy.1).mpr hy.2.1)
  exact (scalarPotential_strictConvexOn μ hμ).eq_of_isMinOn hminy hmin hy.1 hz

theorem scalar_chamber_solution_existsUnique {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) :
    ∃! z : FourBody.ScalarGeometry.ScalarW μ,
      z ∈ FourBody.ScalarGeometry.chamber μ ∧
      FourBody.ScalarGeometry.IsScalarSolution μ z.val := by
  obtain ⟨x, hx, huniq⟩ := scalar_potential_root_existsUnique_centered μ hμ
  let z : FourBody.ScalarGeometry.ScalarW μ := ⟨x, hx.2.2⟩
  refine ⟨z, ⟨hx.1, hx.1.injective, hx.2.1⟩, ?_⟩
  intro y hy
  apply Subtype.ext
  exact huniq y.val ⟨hy.1, hy.2.2, y.property⟩

/-- The original centered minimization route: compact sublevels in ScalarW,
Fermat in ScalarW, the weighted annihilator, and common-residual cancellation.
The uniqueness uses the already proved literal convexity/gradient chain. -/
theorem scalar_chamber_solution_existsUnique_original_route {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) :
    ∃! z : FourBody.ScalarGeometry.ScalarW μ,
      z ∈ FourBody.ScalarGeometry.chamber μ ∧
      FourBody.ScalarGeometry.IsScalarSolution μ z.val := by
  obtain ⟨z, hz, hmin⟩ := scalarPotential_centered_exists_minimizer μ hμ
  have hroot := scalarPotential_centered_minimizer_root μ hμ z hz hmin
  obtain ⟨x, hx, huniq⟩ := scalar_potential_root_existsUnique μ hμ
  refine ⟨z, ⟨hz, hz.injective, hroot⟩, ?_⟩
  intro y hy
  apply Subtype.ext
  exact (huniq y.val ⟨hy.1, hy.2.2⟩).trans (huniq z.val ⟨hz, hroot⟩).symm

/-- The paper's unique constrained critical point, with the actual restricted
first derivative rather than an independently defined stationarity predicate. -/
theorem scalarPotential_centered_critical_existsUnique {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) :
    ∃! z : FourBody.ScalarGeometry.ScalarW μ,
      z ∈ FourBody.ScalarGeometry.chamber μ ∧
      ∀ h : FourBody.ScalarGeometry.ScalarW μ, scalarPotentialDerivative μ z.val h.val = 0 := by
  obtain ⟨z, hz, huniq⟩ := scalar_chamber_solution_existsUnique_original_route μ hμ
  refine ⟨z, ⟨hz.1, (scalarPotential_constraint_critical_iff_root μ z.val hμ hz.1
    z.property).mpr hz.2.2⟩, ?_⟩
  intro y hy
  have hroot := (scalarPotential_constraint_critical_iff_root μ y.val hμ hy.1
    y.property).mp hy.2
  exact huniq y ⟨hy.1, hy.1.injective, hroot⟩

end FourBody.ScalarMinimizer

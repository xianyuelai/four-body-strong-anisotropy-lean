import FourBody.ScalarPotentialProper
import FourBody.ScalarGeometry
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
The genuine derivative calculation used in v2 Lemma 3.1.  The index set
is `Fin n`, including the empty and singleton cases.  Each interaction
occurs once in `scalarPairs n`.  The row and column summation identities
below replace the former three-coordinate expansion.

This source is staged for serial compilation by the parent task.  It has
not been compiled in this worker; source proof bodies are not a claim of
machine verification or of completion of the paper's main theorem.
-/

noncomputable section
open scoped BigOperators
open Filter Set Topology

namespace FourBody.ScalarMinimizer

/-- Coordinate evaluation of the actual finite-support coordinate vector. -/
theorem scalarSingle_apply {n : ℕ} (i j : Fin n) (a : ℝ) :
    (Pi.single i a : ScalarVector n) j = if j = i then a else 0 := by
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- No dimension-specific expansion is used to isolate a row of the pair sum. -/
theorem scalarPairs_sum_first {n : ℕ} (f : Fin n × Fin n → ℝ) (i : Fin n) :
    (∑ p ∈ scalarPairs n, if p.1 = i then f p else 0) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), f (i, j) := by
  rw [Finset.sum_finset_product (scalarPairs n) Finset.univ
    (fun a : Fin n => Finset.univ.filter (fun b => a < b))
    (by intro p; simp [scalarPairs])]
  have hrow (a : Fin n) :
      (∑ b ∈ Finset.univ.filter (fun b : Fin n => a < b),
        if a = i then f (a, b) else 0) =
        if a = i then
          ∑ b ∈ Finset.univ.filter (fun b : Fin n => i < b), f (i, b)
        else 0 := by
    by_cases hai : a = i
    · subst a
      simp
    · simp [hai]
  simp_rw [hrow]
  simp

/-- The analogous column identity, using the second coordinate as outer index. -/
theorem scalarPairs_sum_second {n : ℕ} (f : Fin n × Fin n → ℝ) (i : Fin n) :
    (∑ p ∈ scalarPairs n, if p.2 = i then f p else 0) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), f (j, i) := by
  rw [Finset.sum_finset_product_right (scalarPairs n) Finset.univ
    (fun b : Fin n => Finset.univ.filter (fun a => a < b))
    (by intro p; simp [scalarPairs])]
  have hcol (b : Fin n) :
      (∑ a ∈ Finset.univ.filter (fun a : Fin n => a < b),
        if b = i then f (a, b) else 0) =
        if b = i then
          ∑ a ∈ Finset.univ.filter (fun a : Fin n => a < i), f (a, i)
        else 0 := by
    by_cases hbi : b = i
    · subst b
      simp
    · simp [hbi]
  simp_rw [hcol]
  simp

/-- Every label other than `i` lies on exactly one side of `i`. -/
theorem scalar_erase_eq_lower_union_upper {n : ℕ} (i : Fin n) :
    Finset.univ.erase i =
      Finset.univ.filter (fun j : Fin n => j < i) ∪
        Finset.univ.filter (fun j : Fin n => i < j) := by
  ext j
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union,
    Finset.mem_filter, true_and]
  constructor
  · exact lt_or_gt_of_ne
  · intro hj
    rcases hj with hj | hj
    · exact ne_of_lt hj
    · exact Ne.symm (ne_of_lt hj)

theorem scalar_lower_upper_disjoint {n : ℕ} (i : Fin n) :
    Disjoint (Finset.univ.filter (fun j : Fin n => j < i))
      (Finset.univ.filter (fun j : Fin n => i < j)) := by
  apply Finset.disjoint_left.mpr
  intro j hjlo hjhi
  exact (not_lt_of_ge (Finset.mem_filter.mp hjlo).2.le)
    (Finset.mem_filter.mp hjhi).2

/-- Positive signed inverse cube becomes an inverse square on the lower side. -/
theorem scalarForce_term_lower {n : ℕ} (μ z : ScalarVector n)
    (hz : z ∈ ambientChamber n) {i j : Fin n} (hji : j < i) :
    μ j * (z i - z j) / |z i - z j| ^ 3 =
      μ j * ((z i - z j) ^ 2)⁻¹ := by
  have hgap : 0 < z i - z j := sub_pos.mpr (hz hji)
  rw [abs_of_pos hgap]
  field_simp [hgap.ne']

/-- The upper side has the negative sign required by the original force. -/
theorem scalarForce_term_upper {n : ℕ} (μ z : ScalarVector n)
    (hz : z ∈ ambientChamber n) {i j : Fin n} (hij : i < j) :
    μ j * (z i - z j) / |z i - z j| ^ 3 =
      -(μ j * ((z j - z i) ^ 2)⁻¹) := by
  have hgap : 0 < z j - z i := sub_pos.mpr (hz hij)
  rw [abs_sub_comm (z i) (z j), abs_of_pos hgap]
  field_simp [hgap.ne']
  ring

/-- This is an identity for the original `ScalarGeometry.scalarForce`,
not a separately assumed formula for a surrogate force. -/
theorem scalarForce_ordered_split {n : ℕ} (μ z : ScalarVector n)
    (hz : z ∈ ambientChamber n) (i : Fin n) :
    FourBody.ScalarGeometry.scalarForce μ z i =
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i),
        μ j * ((z i - z j) ^ 2)⁻¹) -
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
        μ j * ((z j - z i) ^ 2)⁻¹ := by
  unfold FourBody.ScalarGeometry.scalarForce
  rw [scalar_erase_eq_lower_union_upper, Finset.sum_union (scalar_lower_upper_disjoint i)]
  have hlo :
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i),
        μ j * (z i - z j) / |z i - z j| ^ 3) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i),
        μ j * ((z i - z j) ^ 2)⁻¹ := by
    apply Finset.sum_congr rfl
    intro j hj
    exact scalarForce_term_lower μ z hz (Finset.mem_filter.mp hj).2
  have hhi :
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
        μ j * (z i - z j) / |z i - z j| ^ 3) =
      -(∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
        μ j * ((z j - z i) ^ 2)⁻¹) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact scalarForce_term_upper μ z hz (Finset.mem_filter.mp hj).2
  rw [hlo, hhi]
  exact (sub_eq_add_neg _ _).symm

def scalarPairDerivativeCoefficient {n : ℕ} (μ z : ScalarVector n)
    (p : Fin n × Fin n) : ℝ :=
  μ p.1 * μ p.2 * (-((z p.2 - z p.1) ^ 2)⁻¹)

def scalarQuadraticPotentialDerivative {n : ℕ} (μ z : ScalarVector n) :
    ScalarVector n →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ∑ i, (μ i * (2 * z i)) •
    (ContinuousLinearMap.proj i : ScalarVector n →L[ℝ] ℝ)

/-- The derivative obtained by differentiating the ordered potential term by term. -/
def orderedScalarPotentialDerivative {n : ℕ} (μ z : ScalarVector n) :
    ScalarVector n →L[ℝ] ℝ :=
  scalarQuadraticPotentialDerivative μ z +
    ∑ p ∈ scalarPairs n, scalarPairDerivativeCoefficient μ z p •
      ((ContinuousLinearMap.proj p.2 : ScalarVector n →L[ℝ] ℝ) -
        ContinuousLinearMap.proj p.1)

/-- The same derivative in the original mass-divided force coordinates. -/
def scalarPotentialDerivative {n : ℕ} (μ z : ScalarVector n) :
    ScalarVector n →L[ℝ] ℝ :=
  ∑ i, (μ i * (z i - FourBody.ScalarGeometry.scalarForce μ z i)) •
    (ContinuousLinearMap.proj i : ScalarVector n →L[ℝ] ℝ)

theorem scalarWeightedProjections_single {n : ℕ} (a : ScalarVector n) (i : Fin n) :
    (∑ j, a j • (ContinuousLinearMap.proj j : ScalarVector n →L[ℝ] ℝ))
      (Pi.single i 1) = a i := by
  simp only [sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  simp_rw [scalarSingle_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem scalarQuadraticPotentialDerivative_single {n : ℕ} (μ z : ScalarVector n)
    (i : Fin n) :
    scalarQuadraticPotentialDerivative μ z (Pi.single i 1) = μ i * z i := by
  unfold scalarQuadraticPotentialDerivative
  rw [smul_apply, scalarWeightedProjections_single]
  simp only [smul_eq_mul]
  ring

theorem scalarPairDerivativeCoefficient_sum_lower {n : ℕ} (μ z : ScalarVector n)
    (i : Fin n) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i),
      scalarPairDerivativeCoefficient μ z (j, i)) =
    -μ i * ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i),
      μ j * ((z i - z j) ^ 2)⁻¹ := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold scalarPairDerivativeCoefficient
  ring

theorem scalarPairDerivativeCoefficient_sum_upper {n : ℕ} (μ z : ScalarVector n)
    (i : Fin n) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
      scalarPairDerivativeCoefficient μ z (i, j)) =
    -μ i * ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
      μ j * ((z j - z i) ^ 2)⁻¹ := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold scalarPairDerivativeCoefficient
  ring

/-- Finite-pair incidence converts the derivative into its literal coordinate row. -/
theorem orderedScalarPotentialDerivative_single {n : ℕ} (μ z : ScalarVector n)
    (hz : z ∈ ambientChamber n) (i : Fin n) :
    orderedScalarPotentialDerivative μ z (Pi.single i 1) =
      μ i * (z i - FourBody.ScalarGeometry.scalarForce μ z i) := by
  have hinc :
      (∑ p ∈ scalarPairs n, scalarPairDerivativeCoefficient μ z p *
        ((Pi.single i 1 : ScalarVector n) p.2 - (Pi.single i 1 : ScalarVector n) p.1)) =
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i),
        scalarPairDerivativeCoefficient μ z (j, i)) -
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
        scalarPairDerivativeCoefficient μ z (i, j) := by
    calc
      _ = ∑ p ∈ scalarPairs n,
          ((if p.2 = i then scalarPairDerivativeCoefficient μ z p else 0) -
            (if p.1 = i then scalarPairDerivativeCoefficient μ z p else 0)) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [scalarSingle_apply, scalarSingle_apply]
        by_cases h2 : p.2 = i <;> by_cases h1 : p.1 = i <;> simp [h2, h1]
      _ = _ := by
        rw [Finset.sum_sub_distrib, scalarPairs_sum_second, scalarPairs_sum_first]
  unfold orderedScalarPotentialDerivative
  simp only [add_apply, sum_apply,
    smul_apply, sub_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [scalarQuadraticPotentialDerivative_single, hinc,
    scalarPairDerivativeCoefficient_sum_lower, scalarPairDerivativeCoefficient_sum_upper,
    scalarForce_ordered_split μ z hz i]
  ring

theorem scalarPotentialDerivative_apply {n : ℕ} (μ z v : ScalarVector n) :
    scalarPotentialDerivative μ z v =
      ∑ i, μ i * (z i - FourBody.ScalarGeometry.scalarForce μ z i) * v i := by
  simp only [scalarPotentialDerivative, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

theorem scalarPotentialDerivative_single {n : ℕ} (μ z : ScalarVector n) (i : Fin n) :
    scalarPotentialDerivative μ z (Pi.single i 1) =
      μ i * (z i - FourBody.ScalarGeometry.scalarForce μ z i) := by
  exact scalarWeightedProjections_single _ i

theorem scalarSingle_smul_one {n : ℕ} (i : Fin n) (a : ℝ) :
    (Pi.single i a : ScalarVector n) = a • Pi.single i 1 := by
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, scalarSingle_apply]
  by_cases hji : j = i <;> simp [hji]

/-- Equality on the coordinate vectors is extended by the finite expansion of a vector. -/
theorem orderedScalarPotentialDerivative_eq {n : ℕ} (μ z : ScalarVector n)
    (hz : z ∈ ambientChamber n) :
    orderedScalarPotentialDerivative μ z = scalarPotentialDerivative μ z := by
  apply ContinuousLinearMap.ext
  intro v
  rw [← Finset.univ_sum_single v]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [scalarSingle_smul_one i (v i)]
  simp only [map_smul, smul_eq_mul]
  rw [orderedScalarPotentialDerivative_single μ z hz,
    scalarPotentialDerivative_single]

/-- Actual Frechet differentiation of the potential, using the open chamber
only to replace absolute gaps by positive ordered gaps in a neighborhood. -/
theorem scalarPotential_hasFDerivAt {n : ℕ} (μ z : ScalarVector n)
    (hz : z ∈ ambientChamber n) :
    HasFDerivAt (scalarPotential μ) (scalarPotentialDerivative μ z) z := by
  let p := fun i : Fin n =>
    (ContinuousLinearMap.proj i : ScalarVector n →L[ℝ] ℝ)
  have hQ : HasFDerivAt (scalarQuadraticPotential μ)
      (scalarQuadraticPotentialDerivative μ z) z := by
    unfold scalarQuadraticPotential FourBody.Reuse.quadraticPotential
      scalarQuadraticPotentialDerivative
    apply HasFDerivAt.const_mul
    apply HasFDerivAt.fun_sum
    intro i _
    simpa [p, smul_smul] using
      ((hasFDerivAt_apply (𝕜 := ℝ) i z).pow 2).const_mul (μ i)
  have hpair (q : Fin n × Fin n) (hq : q ∈ scalarPairs n) :
      HasFDerivAt (fun w : ScalarVector n => μ q.1 * μ q.2 / (w q.2 - w q.1))
        (scalarPairDerivativeCoefficient μ z q • (p q.2 - p q.1)) z := by
    have hgap : 0 < z q.2 - z q.1 :=
      sub_pos.mpr (hz (Finset.mem_filter.mp hq).2)
    simpa only [scalarPairDerivativeCoefficient, div_eq_mul_inv, smul_smul,
      Function.comp_def, Pi.sub_apply, p] using
      ((hasDerivAt_inv hgap.ne').comp_hasFDerivAt z
        ((hasFDerivAt_apply (𝕜 := ℝ) q.2 z).sub
          (hasFDerivAt_apply (𝕜 := ℝ) q.1 z))).const_mul (μ q.1 * μ q.2)
  have hd : HasFDerivAt
      (fun w : ScalarVector n => scalarQuadraticPotential μ w +
        ∑ q ∈ scalarPairs n, μ q.1 * μ q.2 / (w q.2 - w q.1))
      (orderedScalarPotentialDerivative μ z) z := by
    simpa only [orderedScalarPotentialDerivative, p, Pi.add_apply] using
      hQ.fun_add (HasFDerivAt.fun_sum hpair)
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ ambientChamber n :=
    (ambientChamber_isOpen n).mem_nhds hz
  have heq : scalarPotential μ =ᶠ[𝓝 z]
      (fun w : ScalarVector n => scalarQuadraticPotential μ w +
        ∑ q ∈ scalarPairs n, μ q.1 * μ q.2 / (w q.2 - w q.1)) :=
    hnear.mono (fun w hw => scalarPotential_ordered_formula μ w hw)
  rw [← orderedScalarPotentialDerivative_eq μ z hz]
  exact hd.congr_of_eventuallyEq heq

theorem scalarPotential_fderiv_apply {n : ℕ} (μ z v : ScalarVector n)
    (hz : z ∈ ambientChamber n) :
    fderiv ℝ (scalarPotential μ) z v =
      ∑ i, μ i * (z i - FourBody.ScalarGeometry.scalarForce μ z i) * v i := by
  rw [(scalarPotential_hasFDerivAt μ z hz).fderiv]
  exact scalarPotentialDerivative_apply μ z v

theorem scalarPotential_divided_gradient {n : ℕ} (μ z : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (hz : z ∈ ambientChamber n) (i : Fin n) :
    fderiv ℝ (scalarPotential μ) z (Pi.single i 1) / μ i =
      z i - FourBody.ScalarGeometry.scalarForce μ z i := by
  rw [(scalarPotential_hasFDerivAt μ z hz).fderiv, scalarPotentialDerivative_single]
  exact mul_div_cancel_left₀ _ (hμ i).ne'

/-- Critical points are exactly roots of the original scalar equations. -/
theorem scalarPotential_critical_iff_root {n : ℕ} (μ z : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (hz : z ∈ ambientChamber n) :
    fderiv ℝ (scalarPotential μ) z = 0 ↔
      ∀ i, FourBody.ScalarGeometry.scalarForce μ z i = z i := by
  constructor
  · intro h i
    have hi : z i - FourBody.ScalarGeometry.scalarForce μ z i = 0 := by
      rw [← scalarPotential_divided_gradient μ z hμ hz i, h,
        zero_apply, zero_div]
    exact (sub_eq_zero.mp hi).symm
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    rw [scalarPotential_fderiv_apply μ z v hz]
    simp only [h, sub_self, mul_zero, zero_mul, Finset.sum_const_zero,
      zero_apply]

end FourBody.ScalarMinimizer

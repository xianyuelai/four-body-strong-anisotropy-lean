import FourBody.ScalarPotentialGradient
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
The literal second Frechet derivative claimed in v2 Lemma 3.1.
The coefficient 2 belongs to D²Phi, unlike the L bilinear identity.
This file differentiates the actual already calculated first derivative;
it does not define a Hessian formula and assume that it is a derivative.
Staged proof bodies, not yet a compiler or kernel-verification result.
-/

noncomputable section
open scoped BigOperators
open Set Filter Topology

namespace FourBody.ScalarMinimizer

def scalarGapProjection {n : ℕ} (p : Fin n × Fin n) :
    ScalarVector n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj p.2 : ScalarVector n →L[ℝ] ℝ) -
    (ContinuousLinearMap.proj p.1 : ScalarVector n →L[ℝ] ℝ)

def scalarQuadraticHessian {n : ℕ} (μ : ScalarVector n) :
    ScalarVector n →L[ℝ] ScalarVector n →L[ℝ] ℝ :=
  ∑ i, μ i • (ContinuousLinearMap.proj i : ScalarVector n →L[ℝ] ℝ).smulRight
    (ContinuousLinearMap.proj i : ScalarVector n →L[ℝ] ℝ)

def scalarPairHessianCoefficient {n : ℕ} (μ z : ScalarVector n)
    (p : Fin n × Fin n) : ℝ := 2 * μ p.1 * μ p.2 / (z p.2 - z p.1) ^ 3

def scalarPotentialHessian {n : ℕ} (μ z : ScalarVector n) :
    ScalarVector n →L[ℝ] ScalarVector n →L[ℝ] ℝ :=
  scalarQuadraticHessian μ + ∑ p ∈ scalarPairs n,
    scalarPairHessianCoefficient μ z p •
      (scalarGapProjection p).smulRight (scalarGapProjection p)

theorem scalarQuadraticPotentialDerivative_eq {n : ℕ} (μ z : ScalarVector n) :
    scalarQuadraticPotentialDerivative μ z =
      ∑ i, (μ i * z i) • (ContinuousLinearMap.proj i : ScalarVector n →L[ℝ] ℝ) := by
  ext h
  simp only [scalarQuadraticPotentialDerivative, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem scalarQuadraticPotentialDerivative_hasFDerivAt {n : ℕ} (μ z : ScalarVector n) :
    HasFDerivAt (scalarQuadraticPotentialDerivative μ) (scalarQuadraticHessian μ) z := by
  have hd : HasFDerivAt
      (fun w : ScalarVector n => ∑ i, (μ i * w i) •
        (ContinuousLinearMap.proj i : ScalarVector n →L[ℝ] ℝ))
      (∑ i, ((μ i • (ContinuousLinearMap.proj i : ScalarVector n →L[ℝ] ℝ)).smulRight
        (ContinuousLinearMap.proj i : ScalarVector n →L[ℝ] ℝ))) z := by
    apply HasFDerivAt.fun_sum
    intro i _
    exact ((hasFDerivAt_apply (𝕜 := ℝ) i z).const_mul (μ i)).smul_const
      (ContinuousLinearMap.proj i : ScalarVector n →L[ℝ] ℝ)
  have he : (∑ i, ((μ i • (ContinuousLinearMap.proj i : ScalarVector n →L[ℝ] ℝ)).smulRight
        (ContinuousLinearMap.proj i : ScalarVector n →L[ℝ] ℝ))) = scalarQuadraticHessian μ := by
    ext h v
    simp only [scalarQuadraticHessian, sum_apply,
      ContinuousLinearMap.smulRight_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hd
  have hf : scalarQuadraticPotentialDerivative μ =
      (fun w : ScalarVector n => ∑ i, (μ i * w i) •
        (ContinuousLinearMap.proj i : ScalarVector n →L[ℝ] ℝ)) :=
    funext (fun w => scalarQuadraticPotentialDerivative_eq μ w)
  rw [hf]
  exact hd

theorem scalarPairDerivativeCoefficient_hasFDerivAt {n : ℕ} (μ z : ScalarVector n)
    (hz : z ∈ ambientChamber n) (p : Fin n × Fin n) (hp : p ∈ scalarPairs n) :
    HasFDerivAt (fun w : ScalarVector n => scalarPairDerivativeCoefficient μ w p)
      (scalarPairHessianCoefficient μ z p • scalarGapProjection p) z := by
  have hgap : 0 < z p.2 - z p.1 := sub_pos.mpr (hz (Finset.mem_filter.mp hp).2)
  have hd := (((hasDerivAt_inv (pow_ne_zero 2 hgap.ne')).comp_hasFDerivAt z
    (((hasFDerivAt_apply (𝕜 := ℝ) p.2 z).sub
      (hasFDerivAt_apply (𝕜 := ℝ) p.1 z)).pow 2)).neg).const_mul (μ p.1 * μ p.2)
  apply hd.congr_fderiv
  ext h
  simp only [scalarPairHessianCoefficient, scalarGapProjection,
    smul_apply, sub_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, neg_apply,
    two_nsmul, Pi.sub_apply]
  field_simp [hgap.ne']
  ring

theorem orderedScalarPotentialDerivative_hasFDerivAt {n : ℕ} (μ z : ScalarVector n)
    (hz : z ∈ ambientChamber n) :
    HasFDerivAt (orderedScalarPotentialDerivative μ) (scalarPotentialHessian μ z) z := by
  have hpair (p : Fin n × Fin n) (hp : p ∈ scalarPairs n) :
      HasFDerivAt (fun w : ScalarVector n =>
        scalarPairDerivativeCoefficient μ w p • scalarGapProjection p)
        (scalarPairHessianCoefficient μ z p •
          (scalarGapProjection p).smulRight (scalarGapProjection p)) z := by
    have hd := (scalarPairDerivativeCoefficient_hasFDerivAt μ z hz p hp).smul_const
      (scalarGapProjection p)
    apply hd.congr_fderiv
    ext h v
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply,
      smul_eq_mul]
    ring
  unfold orderedScalarPotentialDerivative scalarPotentialHessian
  simpa only [scalarGapProjection] using
    (scalarQuadraticPotentialDerivative_hasFDerivAt μ z).fun_add (HasFDerivAt.fun_sum hpair)

/-- Actual derivative of the actual first Frechet derivative of Phi. -/
theorem scalarPotential_second_hasFDerivAt {n : ℕ} (μ z : ScalarVector n)
    (hz : z ∈ ambientChamber n) :
    HasFDerivAt (fun w : ScalarVector n => fderiv ℝ (scalarPotential μ) w)
      (scalarPotentialHessian μ z) z := by
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ ambientChamber n :=
    (ambientChamber_isOpen n).mem_nhds hz
  have heq : (fun w : ScalarVector n => fderiv ℝ (scalarPotential μ) w) =ᶠ[𝓝 z]
      orderedScalarPotentialDerivative μ := by
    apply hnear.mono
    intro w hw
    exact (scalarPotential_hasFDerivAt μ w hw).fderiv.trans
      (orderedScalarPotentialDerivative_eq μ w hw).symm
  exact (orderedScalarPotentialDerivative_hasFDerivAt μ z hz).congr_of_eventuallyEq heq

theorem scalarPotentialHessian_apply {n : ℕ} (μ z h v : ScalarVector n)
    (hz : z ∈ ambientChamber n) :
    scalarPotentialHessian μ z h v =
      (∑ i, μ i * h i * v i) + 2 * ∑ p ∈ scalarPairs n,
        μ p.1 * μ p.2 * (h p.1 - h p.2) * (v p.1 - v p.2) /
          |z p.1 - z p.2| ^ 3 := by
  have hQ : scalarQuadraticHessian μ h v = ∑ i, μ i * h i * v i := by
    simp only [scalarQuadraticHessian, sum_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold scalarPotentialHessian
  rw [add_apply, add_apply, hQ]
  congr 1
  simp only [scalarPairHessianCoefficient, scalarGapProjection,
    sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, sub_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hgap : 0 < z p.2 - z p.1 := sub_pos.mpr (hz (Finset.mem_filter.mp hp).2)
  rw [abs_sub_comm, abs_of_pos hgap]
  ring

/-- Exactly the displayed Hessian in the manuscript, with its factor 2. -/
theorem scalarPotential_second_fderiv_diagonal {n : ℕ} (μ z h : ScalarVector n)
    (hz : z ∈ ambientChamber n) :
    fderiv ℝ (fun w : ScalarVector n => fderiv ℝ (scalarPotential μ) w) z h h =
      (∑ i, μ i * h i ^ 2) + 2 * ∑ p ∈ scalarPairs n,
        μ p.1 * μ p.2 * (h p.1 - h p.2) ^ 2 / |z p.1 - z p.2| ^ 3 := by
  rw [(scalarPotential_second_hasFDerivAt μ z hz).fderiv,
    scalarPotentialHessian_apply μ z h h hz]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · congr 1
    apply Finset.sum_congr rfl
    intro p _
    ring

theorem scalarPotential_second_fderiv_diagonal_pos {n : ℕ} (μ z h : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (hz : z ∈ ambientChamber n) (hne : h ≠ 0) :
    0 < fderiv ℝ (fun w : ScalarVector n => fderiv ℝ (scalarPotential μ) w) z h h := by
  obtain ⟨i, hi⟩ : ∃ i, h i ≠ 0 := by
    by_contra hall
    apply hne
    funext i
    exact Classical.byContradiction (fun hi => hall ⟨i, hi⟩)
  have hQ : 0 < ∑ i, μ i * h i ^ 2 :=
    Finset.sum_pos' (fun j _ => mul_nonneg (hμ j).le (sq_nonneg _))
      ⟨i, Finset.mem_univ i, mul_pos (hμ i) (sq_pos_of_ne_zero hi)⟩
  have hP : 0 ≤ ∑ p ∈ scalarPairs n,
      μ p.1 * μ p.2 * (h p.1 - h p.2) ^ 2 / |z p.1 - z p.2| ^ 3 := by
    apply Finset.sum_nonneg
    intro p _
    exact div_nonneg (mul_nonneg (mul_nonneg (hμ p.1).le (hμ p.2).le) (sq_nonneg _))
      (pow_nonneg (abs_nonneg _) _)
  rw [scalarPotential_second_fderiv_diagonal μ z h hz]
  exact add_pos_of_pos_of_nonneg hQ (mul_nonneg (by norm_num) hP)

end FourBody.ScalarMinimizer

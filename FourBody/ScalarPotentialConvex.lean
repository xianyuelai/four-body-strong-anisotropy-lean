import FourBody.ScalarPotential

/-! The finite-pair inverse-gap convexity and positive quadratic Jensen
proofs are exactly the original variational mechanism of Lemma 3.1. -/
noncomputable section
open scoped BigOperators
open Set

namespace FourBody.ScalarMinimizer

theorem scalarPotential_strictConvexOn {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) :
    StrictConvexOn ℝ (ambientChamber n) (scalarPotential μ) := by
  refine ⟨ambientChamber_convex n, ?_⟩
  intro x hx y hy hxy a b ha0 hb0 hab
  have hmix : a • x + b • y ∈ ambientChamber n :=
    ambientChamber_convex n hx hy ha0.le hb0.le hab
  have hQ : scalarQuadraticPotential μ (a • x + b • y) <
      a * scalarQuadraticPotential μ x + b * scalarQuadraticPotential μ y :=
    FourBody.Reuse.quadraticPotential_strictJensen 1 μ x y (by norm_num)
      hμ hxy a b ha0 hb0 hab
  have hpair (p : Fin n × Fin n) (hp : p ∈ scalarPairs n) :
      μ p.1 * μ p.2 / ((a • x + b • y) p.2 - (a • x + b • y) p.1) ≤
        a * (μ p.1 * μ p.2 / (x p.2 - x p.1)) +
        b * (μ p.1 * μ p.2 / (y p.2 - y p.1)) := by
    have hij : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    have hc := FourBody.Reuse.inverse_positive_gap_convex
      (x p.2 - x p.1) (y p.2 - y p.1) a b
      (sub_pos.mpr (hx hij)) (sub_pos.mpr (hy hij)) ha0.le hb0.le hab
    have hm := mul_le_mul_of_nonneg_left hc
      (mul_nonneg (hμ p.1).le (hμ p.2).le)
    have he : (a • x + b • y) p.2 - (a • x + b • y) p.1 =
        a * (x p.2 - x p.1) + b * (y p.2 - y p.1) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he]
    simp only [div_eq_mul_inv] at *
    nlinarith
  have hP :
      (∑ p ∈ scalarPairs n,
        μ p.1 * μ p.2 / ((a • x + b • y) p.2 - (a • x + b • y) p.1)) ≤
      a * (∑ p ∈ scalarPairs n, μ p.1 * μ p.2 / (x p.2 - x p.1)) +
      b * (∑ p ∈ scalarPairs n, μ p.1 * μ p.2 / (y p.2 - y p.1)) := by
    calc
      _ ≤ ∑ p ∈ scalarPairs n,
          (a * (μ p.1 * μ p.2 / (x p.2 - x p.1)) +
           b * (μ p.1 * μ p.2 / (y p.2 - y p.1))) :=
        Finset.sum_le_sum hpair
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [scalarPotential_ordered_formula μ _ hmix,
    scalarPotential_ordered_formula μ x hx, scalarPotential_ordered_formula μ y hy]
  simp only [smul_eq_mul]
  linarith

end FourBody.ScalarMinimizer

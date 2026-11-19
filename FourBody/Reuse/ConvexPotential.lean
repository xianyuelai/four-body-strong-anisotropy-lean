import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The reciprocal-gap convexity proof is unchanged from the old scalar
potential module. The strict quadratic Jensen proof below minimally
generalizes its Fin 3 and fixed 9/4 coefficient to arbitrary finite
dimension and a positive coefficient. The algebra identity is proved
pointwise before summing, replacing the old three-coordinate expansion.
This has not by itself proved existence of a one-dimensional solution.
-/
noncomputable section
open scoped BigOperators
open Set
namespace FourBody.Reuse

theorem inverse_positive_gap_convex (x y a b : ℝ) (hx : 0<x) (hy : 0<y)
    (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) :
    (a*x+b*y)⁻¹≤a*x⁻¹+b*y⁻¹ := by
  have hc : ConvexOn ℝ (Ioi (0 : ℝ)) (fun t : ℝ => t⁻¹) := by
    simpa only [zpow_neg_one] using
      (strictConvexOn_zpow (m := (-1 : ℤ)) (by norm_num) (by norm_num)).convexOn
  simpa only [smul_eq_mul] using hc.2 hx hy ha hb hab


def quadraticPotential {n : ℕ} (D : ℝ) (alpha z : Fin n → ℝ) : ℝ :=
  D/2*(∑ i,alpha i*z i^2)

theorem quadraticPotential_strictJensen {n : ℕ} (D : ℝ)
    (alpha x y : Fin n → ℝ) (hD : 0<D)
    (ha : ∀ i,0<alpha i) (hxy : x≠y) (a b : ℝ)
    (ha0 : 0<a) (hb0 : 0<b) (hab : a+b=1) :
    quadraticPotential D alpha (a • x+b • y)<
      a*quadraticPotential D alpha x+b*quadraticPotential D alpha y := by
  obtain ⟨i,hi⟩ : ∃ i,x i≠y i := by
    by_contra hn
    apply hxy
    funext i
    exact Classical.byContradiction (fun hi => hn ⟨i,hi⟩)
  have hS : 0<∑ j,alpha j*(x j-y j)^2 :=
    Finset.sum_pos' (fun j _ => mul_nonneg (ha j).le (sq_nonneg _))
      ⟨i,Finset.mem_univ i,mul_pos (ha i) (sq_pos_of_ne_zero (sub_ne_zero.mpr hi))⟩
  have hb : b=1-a := by linarith
  have he : a*quadraticPotential D alpha x+b*quadraticPotential D alpha y-
      quadraticPotential D alpha (a • x+b • y)=
      (D/2)*a*b*(∑ j,alpha j*(x j-y j)^2) := by
    unfold quadraticPotential
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hb]
    ring
  have hp : 0<(D/2)*a*b*(∑ j,alpha j*(x j-y j)^2) :=
    mul_pos (mul_pos (mul_pos (div_pos hD (by norm_num)) ha0) hb0) hS
  linarith

end FourBody.Reuse

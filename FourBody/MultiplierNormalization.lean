import FourBody.Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
The literal unique positive dilation in v2 lines 62--66.
Translation, similarity quotients, or changes of the fixed axes are absent.
Static candidate; strict compilation and type/axiom review remain pending.
The positive homogeneity proof is the already checked physical four-body one.
-/

noncomputable section
namespace FourBody

def IsMultiplierSolution (m : Masses) (s lam : ℝ) (q : Configuration) : Prop :=
  CollisionFree q ∧ ∀ i, force m q i = lam • anisotropy s (q i)

theorem multiplier_solution_normalized_dilation {m : Masses} {s lam a : ℝ}
    {q : Configuration} (hq : IsMultiplierSolution m s lam q)
    (ha : 0 < a) (hcube : a ^ 3 = lam) : IsSolution m s (a • q) := by
  refine ⟨collisionFree_positive_dilation hq.1 ha, ?_⟩
  intro i
  have hc : (a ^ 2)⁻¹ * lam = a := by
    rw [← hcube]
    field_simp [ne_of_gt ha]
  rw [force_positive_dilation m hq.1 ha, hq.2 i, smul_smul, hc]
  simpa only [Pi.smul_apply] using ((anisotropy s).map_smul a (q i)).symm

theorem collisionFree_has_nonzero_point {q : Configuration} (hq : CollisionFree q) :
    ∃ i : Label, q i ≠ 0 := by
  by_contra hnone
  push Not at hnone
  exact hq (0 : Label) (1 : Label) (by decide) (by rw [hnone 0, hnone 1])

theorem normalized_multiplier_dilation_cube {m : Masses} {s lam a : ℝ}
    {q : Configuration} (hs : s ≠ 0) (hq : IsMultiplierSolution m s lam q)
    (ha : 0 < a) (hnorm : IsSolution m s (a • q)) : a ^ 3 = lam := by
  obtain ⟨i, hi⟩ := collisionFree_has_nonzero_point hq.1
  have hv : anisotropy s (q i) ≠ 0 := by
    intro hz
    apply hi
    exact anisotropy_injective hs (hz.trans (map_zero _).symm)
  have hk : ∃ k : Axis, anisotropy s (q i) k ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hv
    ext k
    exact hnone k
  obtain ⟨k, hk⟩ := hk
  have heq : ((a ^ 2)⁻¹ * lam) • anisotropy s (q i) = a • anisotropy s (q i) := by
    calc
      _ = force m (a • q) i := by
        rw [force_positive_dilation m hq.1 ha, hq.2 i, smul_smul]
      _ = anisotropy s ((a • q) i) := hnorm.2 i
      _ = _ := by simp only [Pi.smul_apply, map_smul]
  have hc : (a ^ 2)⁻¹ * lam = a := by
    apply mul_right_cancel₀ hk
    simpa only [PiLp.smul_apply, smul_eq_mul] using congrArg (fun p : Point => p k) heq
  field_simp [ne_of_gt ha] at hc
  nlinarith only [hc]

/-- Only the original s≠0 and positive multiplier are needed. In particular
the source's s>1 solutions admit exactly one positive scale. -/
theorem multiplier_solution_unique_positive_dilation {m : Masses} {s lam : ℝ}
    {q : Configuration} (hs : s ≠ 0) (hlam : 0 < lam)
    (hq : IsMultiplierSolution m s lam q) :
    ∃! a : ℝ, 0 < a ∧ IsSolution m s (a • q) := by
  let a : ℝ := lam ^ (1 / (3 : ℝ))
  have ha : 0 < a := Real.rpow_pos_of_pos hlam _
  have hc : a ^ 3 = lam := by
    simpa only [a, one_div, Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hlam.le (by decide : (3 : ℕ) ≠ 0)
  refine ⟨a, ⟨ha, multiplier_solution_normalized_dilation hq ha hc⟩, ?_⟩
  intro b hb
  have hbc := normalized_multiplier_dilation_cube hs hq hb.1 hb.2
  apply le_antisymm
  · exact le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) ha.le
      (by rw [hbc, hc])
  · exact le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) hb.1.le
      (by rw [hbc, hc])

end FourBody

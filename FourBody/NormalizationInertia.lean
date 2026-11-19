import FourBody.ClusterVirial
import FourBody.MultiplierNormalization
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

/-!
Literal v2 lines 148--164, S1-D17/S1-U07/S1-U08/S1-B03.
The anisotropic inertia is the original sum Σ m_i (s x_i² + y_i²).
The potential is the actual Newtonian increasing-pair sum. The raw virial
is derived without assuming centering or a positive multiplier; positivity
of the physical potential and inertia then proves the multiplier positive.

STATIC candidate only. No Lean or Lake invocation has been made here.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace FourBody.Normalization

def anisotropicInertia (m : Masses) (s : ℝ) (q : Configuration) : ℝ :=
  ∑ i, m i * (s * (q i 0) ^ 2 + (q i 1) ^ 2)

def newtonPotential (m : Masses) (q : Configuration) : ℝ :=
  ClusterVirial.potential m q Finset.univ

theorem newtonPotential_formula (m : Masses) (q : Configuration) :
    newtonPotential m q = ∑ p ∈
      ((Finset.univ : Finset Label) ×ˢ Finset.univ).filter (fun p => p.1 < p.2),
        m p.1 * m p.2 / dist (q p.1) (q p.2) := rfl

theorem anisotropy_inner_formula (s : ℝ) (p : Point) :
    inner ℝ p (anisotropy s p) = s * (p 0) ^ 2 + (p 1) ^ 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, anisotropy]
  ring

theorem anisotropicInertia_eq_pairing (m : Masses) (s : ℝ) (q : Configuration) :
    anisotropicInertia m s q = ∑ i, m i * inner ℝ (q i) (anisotropy s (q i)) := by
  simp only [anisotropicInertia, anisotropy_inner_formula]

theorem point_anisotropic_quadratic_nonneg {s : ℝ} (hs : 0 < s) (p : Point) :
    0 ≤ s * (p 0) ^ 2 + (p 1) ^ 2 :=
  add_nonneg (mul_nonneg hs.le (sq_nonneg _)) (sq_nonneg _)

theorem point_anisotropic_quadratic_pos {s : ℝ} (hs : 0 < s)
    (p : Point) (hp : p ≠ 0) : 0 < s * (p 0) ^ 2 + (p 1) ^ 2 := by
  by_cases hx : p 0 = 0
  · have hy : p 1 ≠ 0 := by
      intro h
      apply hp
      ext k
      fin_cases k
      · exact hx
      · exact h
    have hypos := sq_pos_of_ne_zero hy
    rw [hx, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add]
    exact hypos
  · exact add_pos_of_pos_of_nonneg (mul_pos hs (sq_pos_of_ne_zero hx))
      (sq_nonneg _)

theorem anisotropicInertia_nonneg {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) (q : Configuration) : 0 ≤ anisotropicInertia m s q := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hm i).le (point_anisotropic_quadratic_nonneg hs (q i))

theorem anisotropicInertia_pos {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : CollisionFree q) :
    0 < anisotropicInertia m s q := by
  obtain ⟨i, hi⟩ := collisionFree_has_nonzero_point hq
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (hm j).le (point_anisotropic_quadratic_nonneg hs (q j))
  · exact ⟨i, Finset.mem_univ i,
      mul_pos (hm i) (point_anisotropic_quadratic_pos hs (q i) hi)⟩

theorem newtonPotential_pos {m : Masses} (hm : PositiveMasses m)
    {q : Configuration} (hq : CollisionFree q) : 0 < newtonPotential m q := by
  unfold newtonPotential ClusterVirial.potential
  apply Finset.sum_pos
  · intro p hp
    have hlt : p.1 < p.2 := ((ClusterVirial.mem_pairs Finset.univ p.1 p.2).mp hp).2.2
    exact div_pos (mul_pos (hm p.1) (hm p.2))
      (collisionFree_dist_pos hq (ne_of_lt hlt))
  · refine ⟨((0 : Label), (1 : Label)), ?_⟩
    exact (ClusterVirial.mem_pairs Finset.univ 0 1).mpr
      ⟨Finset.mem_univ 0, Finset.mem_univ 1, by decide⟩

theorem weighted_constant_force_pairing_zero (m : Masses) (q : Configuration)
    (p : Point) : (∑ i, m i * inner ℝ p (force m q i)) = 0 := by
  have h : (∑ i, m i • force m q i) = 0 := pairCancellation m q
  have heq : (∑ i, m i * inner ℝ p (force m q i)) =
      inner ℝ p (∑ i, m i • force m q i) := by
    simp only [inner_sum, real_inner_smul_right]
  rw [heq, h, inner_zero_right]

/-- The centering in the checked cluster virial disappears by actual
weighted force cancellation, even before any balanced equation is used. -/
theorem newton_virial (m : Masses) {q : Configuration} (hq : CollisionFree q) :
    newtonPotential m q = ∑ i, m i * inner ℝ (q i) (force m q i) := by
  have h := ClusterVirial.internal_virial m q hq Finset.univ
  change (∑ i, m i * inner ℝ
    (q i - ClusterVirial.centroid m q Finset.univ) (force m q i)) =
      newtonPotential m q at h
  simp only [inner_sub_left, mul_sub, Finset.sum_sub_distrib] at h
  rw [weighted_constant_force_pairing_zero, sub_zero] at h
  exact h.symm

/-- The source U = λ I holds for a genuine physical balanced configuration.
Neither λ > 0 nor a centering/virial certificate is an added premise. -/
theorem multiplier_solution_virial {m : Masses} {s lam : ℝ}
    {q : Configuration} (hq : IsMultiplierSolution m s lam q) :
    newtonPotential m q = lam * anisotropicInertia m s q := by
  rw [newton_virial m hq.1, anisotropicInertia_eq_pairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hq.2 i, real_inner_smul_right]
  ring

theorem multiplier_solution_multiplier_pos {m : Masses} (hm : PositiveMasses m)
    {s lam : ℝ} (hs : 0 < s) {q : Configuration}
    (hq : IsMultiplierSolution m s lam q) : 0 < lam := by
  have hU := newtonPotential_pos hm hq.1
  have hI := anisotropicInertia_pos hm hs hq.1
  by_contra h
  have hlam : lam ≤ 0 := le_of_not_gt h
  have hprod := mul_nonpos_of_nonpos_of_nonneg hlam hI.le
  rw [← multiplier_solution_virial hq] at hprod
  exact (not_le_of_gt hU) hprod

theorem multiplier_solution_center_zero {m : Masses} (hm : PositiveMasses m)
    {s lam : ℝ} (hs : 0 < s) {q : Configuration}
    (hq : IsMultiplierSolution m s lam q) : centerLM m q = 0 := by
  have hlam := multiplier_solution_multiplier_pos hm hs hq
  have hforce : force m q = lam • (fun i => anisotropy s (q i)) := funext hq.2
  have h : centerLM m (force m q) = 0 := pairCancellation m q
  rw [hforce, map_smul, center_anisotropy] at h
  have ha : anisotropy s (centerLM m q) = 0 :=
    (smul_eq_zero.mp h).resolve_left (ne_of_gt hlam)
  exact anisotropy_injective (ne_of_gt hs) (ha.trans (map_zero _).symm)

theorem solution_potential_eq_inertia {m : Masses} {s : ℝ} {q : Configuration}
    (hq : IsSolution m s q) : newtonPotential m q = anisotropicInertia m s q := by
  have hmult : IsMultiplierSolution m s 1 q :=
    ⟨hq.1, fun i => by simpa only [one_smul] using hq.2 i⟩
  simpa only [one_mul] using multiplier_solution_virial hmult

theorem fixed_inertia_multiplier_eq_potential {m : Masses} {s lam : ℝ}
    {q : Configuration} (hq : IsMultiplierSolution m s lam q)
    (hI : anisotropicInertia m s q = 1) : lam = newtonPotential m q := by
  have h := multiplier_solution_virial hq
  rw [hI, mul_one] at h
  exact h.symm

theorem anisotropicInertia_dilation (m : Masses) (s a : ℝ) (q : Configuration) :
    anisotropicInertia m s (a • q) = a ^ 2 * anisotropicInertia m s q := by
  unfold anisotropicInertia
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem newtonPotential_positive_dilation (m : Masses) {q : Configuration}
    (hq : CollisionFree q) {a : ℝ} (ha : 0 < a) :
    newtonPotential m (a • q) = a⁻¹ * newtonPotential m q := by
  unfold newtonPotential ClusterVirial.potential
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hlt : p.1 < p.2 := ((ClusterVirial.mem_pairs Finset.univ p.1 p.2).mp hp).2.2
  have hd : dist (q p.1) (q p.2) ≠ 0 :=
    ne_of_gt (collisionFree_dist_pos hq (ne_of_lt hlt))
  simp only [Pi.smul_apply, dist_positive_dilation ha]
  field_simp [ne_of_gt ha, hd]

theorem multiplier_solution_positive_dilation {m : Masses} {s lam a : ℝ}
    {q : Configuration} (hq : IsMultiplierSolution m s lam q) (ha : 0 < a) :
    IsMultiplierSolution m s (lam / a ^ 3) (a • q) := by
  refine ⟨collisionFree_positive_dilation hq.1 ha, ?_⟩
  intro i
  calc
    force m (a • q) i = ((a ^ 2)⁻¹ * lam) • anisotropy s (q i) := by
      rw [force_positive_dilation m hq.1 ha, hq.2 i, smul_smul]
    _ = (lam / a ^ 3) • anisotropy s ((a • q) i) := by
      rw [Pi.smul_apply, map_smul, smul_smul]
      congr 1
      field_simp [ne_of_gt ha]

theorem sqrt_cube_eq_rpow_three_halves {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x) ^ 3 = x ^ ((3 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  norm_num

theorem rpow_three_halves_one_third {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((3 : ℝ) / 2)) ^ ((1 : ℝ) / 3) = Real.sqrt x := by
  rw [← Real.rpow_mul hx, Real.sqrt_eq_rpow]
  congr 1
  norm_num

end FourBody.Normalization

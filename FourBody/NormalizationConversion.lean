import FourBody.NormalizationInertia

/-!
Literal fixed-inertia ↔ multiplier-one conversion, v2 eq:normalization.
The maps act on actual labeled configurations; their two-sided inverse
equalities retain the original masses, s, coordinate axes, and labels.
All scale and multiplier positivity used below is proved from physical
collision freedom and positive masses, rather than assumed as a conclusion.

STATIC candidate only. Strict compilation and full trust audit remain pending.
-/

set_option autoImplicit false
noncomputable section
namespace FourBody.Normalization

def fixedInertiaNormalization (m : Masses) (s : ℝ) (q : Configuration) : Configuration :=
  (Real.sqrt (anisotropicInertia m s q))⁻¹ • q

def IsFixedInertiaSolution (m : Masses) (s : ℝ) (q : Configuration) : Prop :=
  anisotropicInertia m s q = 1 ∧ IsMultiplierSolution m s (newtonPotential m q) q

def multiplierOneFromFixed (m : Masses) (q : Configuration) : Configuration :=
  (newtonPotential m q) ^ ((1 : ℝ) / 3) • q

theorem fixedInertiaNormalization_coordinate (m : Masses) (s : ℝ)
    (q : Configuration) (i : Label) (k : Axis) :
    fixedInertiaNormalization m s q i k = q i k / Real.sqrt (anisotropicInertia m s q) := by
  simp only [fixedInertiaNormalization, Pi.smul_apply, PiLp.smul_apply,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem fixedInertiaNormalization_scale_pos {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : IsSolution m s q) :
    0 < (Real.sqrt (anisotropicInertia m s q))⁻¹ :=
  inv_pos.mpr (Real.sqrt_pos.mpr (anisotropicInertia_pos hm hs hq.1))

theorem fixedInertiaNormalization_inertia_eq_one {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : IsSolution m s q) :
    anisotropicInertia m s (fixedInertiaNormalization m s q) = 1 := by
  have hI := anisotropicInertia_pos hm hs hq.1
  rw [fixedInertiaNormalization, anisotropicInertia_dilation, inv_pow,
    Real.sq_sqrt hI.le, inv_mul_cancel₀ (ne_of_gt hI)]

theorem fixedInertiaNormalization_isMultiplierSolution {m : Masses}
    (hm : PositiveMasses m) {s : ℝ} (hs : 0 < s) {q : Configuration}
    (hq : IsSolution m s q) :
    IsMultiplierSolution m s (anisotropicInertia m s q ^ ((3 : ℝ) / 2))
      (fixedInertiaNormalization m s q) := by
  have hI := anisotropicInertia_pos hm hs hq.1
  have hmult : IsMultiplierSolution m s 1 q :=
    ⟨hq.1, fun i => by simpa only [one_smul] using hq.2 i⟩
  have hscale := fixedInertiaNormalization_scale_pos hm hs hq
  have hscaled := multiplier_solution_positive_dilation hmult hscale
  have hlam : 1 / ((Real.sqrt (anisotropicInertia m s q))⁻¹) ^ 3 =
      anisotropicInertia m s q ^ ((3 : ℝ) / 2) := by
    rw [inv_pow, one_div, inv_inv]
    exact sqrt_cube_eq_rpow_three_halves hI.le
  change IsMultiplierSolution m s (anisotropicInertia m s q ^ ((3 : ℝ) / 2))
    ((Real.sqrt (anisotropicInertia m s q))⁻¹ • q)
  rw [← hlam]
  exact hscaled

theorem fixedInertiaNormalization_multiplier_pos {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : IsSolution m s q) :
    0 < anisotropicInertia m s q ^ ((3 : ℝ) / 2) :=
  Real.rpow_pos_of_pos (anisotropicInertia_pos hm hs hq.1) _

theorem fixedInertiaNormalization_multiplier_eq_potential {m : Masses}
    (hm : PositiveMasses m) {s : ℝ} (hs : 0 < s) {q : Configuration}
    (hq : IsSolution m s q) :
    anisotropicInertia m s q ^ ((3 : ℝ) / 2) =
      newtonPotential m (fixedInertiaNormalization m s q) :=
  fixed_inertia_multiplier_eq_potential
    (fixedInertiaNormalization_isMultiplierSolution hm hs hq)
    (fixedInertiaNormalization_inertia_eq_one hm hs hq)

theorem fixedInertiaNormalization_reconstruction {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : IsSolution m s q) :
    Real.sqrt (anisotropicInertia m s q) • fixedInertiaNormalization m s q = q := by
  have hroot : Real.sqrt (anisotropicInertia m s q) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (anisotropicInertia_pos hm hs hq.1))
  rw [fixedInertiaNormalization, smul_smul, mul_inv_cancel₀ hroot, one_smul]

theorem fixedInertiaNormalization_original_conversion {m : Masses}
    (hm : PositiveMasses m) {s : ℝ} (hs : 0 < s) {q : Configuration}
    (hq : IsSolution m s q) :
    q = (anisotropicInertia m s q ^ ((3 : ℝ) / 2)) ^ ((1 : ℝ) / 3) •
      fixedInertiaNormalization m s q := by
  rw [rpow_three_halves_one_third (anisotropicInertia_pos hm hs hq.1).le]
  exact (fixedInertiaNormalization_reconstruction hm hs hq).symm

theorem fixedInertiaNormalization_center_zero {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : IsSolution m s q) :
    centerLM m (fixedInertiaNormalization m s q) = 0 := by
  exact multiplier_solution_center_zero hm hs
    (fixedInertiaNormalization_isMultiplierSolution hm hs hq)

theorem fixed_inertia_solution_iff_exists_multiplier (m : Masses) (s : ℝ)
    (q : Configuration) : IsFixedInertiaSolution m s q ↔
      anisotropicInertia m s q = 1 ∧ ∃ lam : ℝ, IsMultiplierSolution m s lam q := by
  constructor
  · intro hq
    exact ⟨hq.1, newtonPotential m q, hq.2⟩
  · rintro ⟨hI, lam, hq⟩
    have hlam := fixed_inertia_multiplier_eq_potential hq hI
    exact ⟨hI, by simpa only [hlam] using hq⟩

theorem solution_to_fixed_inertia {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : IsSolution m s q) :
    IsFixedInertiaSolution m s (fixedInertiaNormalization m s q) := by
  refine ⟨fixedInertiaNormalization_inertia_eq_one hm hs hq, ?_⟩
  rw [← fixedInertiaNormalization_multiplier_eq_potential hm hs hq]
  exact fixedInertiaNormalization_isMultiplierSolution hm hs hq

theorem multiplierOneFromFixed_scale_pos {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} {q : Configuration} (hq : IsFixedInertiaSolution m s q) :
    0 < newtonPotential m q ^ ((1 : ℝ) / 3) :=
  Real.rpow_pos_of_pos (newtonPotential_pos hm hq.2.1) _

theorem multiplierOneFromFixed_scale_cube {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} {q : Configuration} (hq : IsFixedInertiaSolution m s q) :
    (newtonPotential m q ^ ((1 : ℝ) / 3)) ^ 3 = newtonPotential m q := by
  simpa only [one_div, Nat.cast_ofNat] using
    Real.rpow_inv_natCast_pow (newtonPotential_pos hm hq.2.1).le
      (by decide : (3 : ℕ) ≠ 0)

theorem fixed_inertia_to_solution {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} {q : Configuration} (hq : IsFixedInertiaSolution m s q) :
    IsSolution m s (multiplierOneFromFixed m q) :=
  multiplier_solution_normalized_dilation hq.2
    (multiplierOneFromFixed_scale_pos hm hq) (multiplierOneFromFixed_scale_cube hm hq)

theorem multiplierOneFromFixed_inertia {m : Masses} {s : ℝ} {q : Configuration}
    (hq : IsFixedInertiaSolution m s q) :
    anisotropicInertia m s (multiplierOneFromFixed m q) =
      (newtonPotential m q ^ ((1 : ℝ) / 3)) ^ 2 := by
  rw [multiplierOneFromFixed, anisotropicInertia_dilation, hq.1, mul_one]

theorem multiplierOneFromFixed_sqrt_inertia {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} {q : Configuration} (hq : IsFixedInertiaSolution m s q) :
    Real.sqrt (anisotropicInertia m s (multiplierOneFromFixed m q)) =
      newtonPotential m q ^ ((1 : ℝ) / 3) := by
  rw [multiplierOneFromFixed_inertia hq]
  exact Real.sqrt_sq (multiplierOneFromFixed_scale_pos hm hq).le

theorem fixed_inertia_multiplier_original_formula {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} {q : Configuration} (hq : IsFixedInertiaSolution m s q) :
    newtonPotential m q =
      anisotropicInertia m s (multiplierOneFromFixed m q) ^ ((3 : ℝ) / 2) := by
  have hnonneg : 0 ≤ anisotropicInertia m s (multiplierOneFromFixed m q) := by
    rw [multiplierOneFromFixed_inertia hq]
    exact sq_nonneg _
  calc
    newtonPotential m q =
        (Real.sqrt (anisotropicInertia m s (multiplierOneFromFixed m q))) ^ 3 := by
      rw [multiplierOneFromFixed_sqrt_inertia hm hq]
      exact (multiplierOneFromFixed_scale_cube hm hq).symm
    _ = _ := sqrt_cube_eq_rpow_three_halves hnonneg

theorem fixed_inertia_normalization_left_inverse {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} {q : Configuration} (hq : IsFixedInertiaSolution m s q) :
    fixedInertiaNormalization m s (multiplierOneFromFixed m q) = q := by
  rw [fixedInertiaNormalization, multiplierOneFromFixed_sqrt_inertia hm hq,
    multiplierOneFromFixed, smul_smul,
    inv_mul_cancel₀ (ne_of_gt (multiplierOneFromFixed_scale_pos hm hq)), one_smul]

theorem fixed_inertia_normalization_right_inverse {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : IsSolution m s q) :
    multiplierOneFromFixed m (fixedInertiaNormalization m s q) = q := by
  rw [multiplierOneFromFixed,
    ← fixedInertiaNormalization_multiplier_eq_potential hm hs hq,
    rpow_three_halves_one_third (anisotropicInertia_pos hm hs hq.1).le]
  exact fixedInertiaNormalization_reconstruction hm hs hq

theorem unique_positive_fixed_inertia_scale {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : IsSolution m s q) :
    ∃! a : ℝ, 0 < a ∧ anisotropicInertia m s (a • q) = 1 := by
  let a : ℝ := (Real.sqrt (anisotropicInertia m s q))⁻¹
  have ha : 0 < a := fixedInertiaNormalization_scale_pos hm hs hq
  have haI : a ^ 2 * anisotropicInertia m s q = 1 := by
    rw [← anisotropicInertia_dilation]
    exact fixedInertiaNormalization_inertia_eq_one hm hs hq
  refine ⟨a, ⟨ha, ?_⟩, ?_⟩
  · rw [anisotropicInertia_dilation]
    exact haI
  · intro b hb
    have hbI : b ^ 2 * anisotropicInertia m s q = 1 := by
      rw [← anisotropicInertia_dilation]
      exact hb.2
    have hpow : b ^ 2 = a ^ 2 :=
      mul_right_cancel₀ (ne_of_gt (anisotropicInertia_pos hm hs hq.1))
        (hbI.trans haI.symm)
    apply le_antisymm
    · exact le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) ha.le hpow.le
    · exact le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) hb.1.le hpow.symm.le

theorem unique_positive_multiplier_one_scale {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : IsFixedInertiaSolution m s q) :
    ∃! a : ℝ, 0 < a ∧ IsSolution m s (a • q) :=
  multiplier_solution_unique_positive_dilation (ne_of_gt hs)
    (newtonPotential_pos hm hq.2.1) hq.2

/-- The full source bridge is a literal bijection of labeled physical tuples;
it is not an equivalence relation identifying different scalings. -/
def fixedInertiaSolutionEquivalence (m : Masses) (hm : PositiveMasses m)
    (s : ℝ) (hs : 0 < s) :
    {q : Configuration // IsSolution m s q} ≃
      {q : Configuration // IsFixedInertiaSolution m s q} where
  toFun q := ⟨fixedInertiaNormalization m s q.val, solution_to_fixed_inertia hm hs q.property⟩
  invFun q := ⟨multiplierOneFromFixed m q.val, fixed_inertia_to_solution hm q.property⟩
  left_inv q := by
    apply Subtype.ext
    exact fixed_inertia_normalization_right_inverse hm hs q.property
  right_inv q := by
    apply Subtype.ext
    exact fixed_inertia_normalization_left_inverse hm q.property

/-- Closed source-facing conjunction: the multiplier, fixed inertia,
conversion scale and inverse are conclusions of the actual physical equation. -/
theorem multiplier_one_fixed_inertia_conversion {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : IsSolution m s q) :
    ∃ qhat : Configuration, ∃ lam : ℝ,
      0 < lam ∧ anisotropicInertia m s qhat = 1 ∧
      IsMultiplierSolution m s lam qhat ∧ lam = newtonPotential m qhat ∧
      q = lam ^ ((1 : ℝ) / 3) • qhat ∧
      qhat = fixedInertiaNormalization m s q ∧
      lam = anisotropicInertia m s q ^ ((3 : ℝ) / 2) := by
  refine ⟨fixedInertiaNormalization m s q, anisotropicInertia m s q ^ ((3 : ℝ) / 2),
    fixedInertiaNormalization_multiplier_pos hm hs hq,
    fixedInertiaNormalization_inertia_eq_one hm hs hq,
    fixedInertiaNormalization_isMultiplierSolution hm hs hq,
    fixedInertiaNormalization_multiplier_eq_potential hm hs hq,
    fixedInertiaNormalization_original_conversion hm hs hq, rfl, rfl⟩

end FourBody.Normalization

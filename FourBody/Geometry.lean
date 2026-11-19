import FourBody.Labels
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
Draft geometry module for the actual v2 manuscript, read via the full
780-line Library text evidence and then compared with the frozen original:
four_body_strong_anisotropy_pro_v2.tex, 32604 bytes, SHA256
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
The only Library-text reconstruction is insertion of the split-boundary
and final newlines; it is not the preserved raw manuscript. This file
proves only its named geometry obligations, not the classification theorem.

Coordinates are genuine two-dimensional Euclidean vectors. Configurations
remain labeled four-tuples: no permutation, reflection, or scaling quotient.
The force is totalized by Lean's inverse convention outside the manuscript's
collision-free domain. `IsSolution` explicitly excludes that domain.
-/

noncomputable section

open scoped BigOperators

namespace FourBody

abbrev Axis := Fin 2
abbrev Point := EuclideanSpace ℝ Axis
abbrev Configuration := Label → Point
abbrev Masses := Label → ℝ

def PositiveMasses (m : Masses) : Prop := ∀ i, 0 < m i

def totalMass (m : Masses) : ℝ := ∑ i, m i

def CollisionFree (q : Configuration) : Prop :=
  ∀ i j, i ≠ j → q i ≠ q j

def force (m : Masses) (q : Configuration) (i : Label) : Point :=
  ∑ j ∈ Finset.univ.erase i,
    (m j / dist (q i) (q j) ^ 3) • (q i - q j)

def anisotropy (s : ℝ) : Point →ₗ[ℝ] Point where
  toFun p := !₂[s * p 0, p 1]
  map_add' p t := by
    ext k
    fin_cases k <;> simp [mul_add]
  map_smul' a p := by
    ext k
    fin_cases k <;> simp [mul_left_comm]

@[simp] theorem anisotropy_x (s : ℝ) (p : Point) :
    anisotropy s p 0 = s * p 0 := by
  simp [anisotropy]

@[simp] theorem anisotropy_y (s : ℝ) (p : Point) :
    anisotropy s p 1 = p 1 := by
  simp [anisotropy]

def centerLM (m : Masses) : Configuration →ₗ[ℝ] Point where
  toFun q := ∑ i, m i • q i
  map_add' q t := by
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' a q := by
    simp [Finset.smul_sum, smul_smul, mul_comm]

@[simp] theorem centerLM_apply (m : Masses) (q : Configuration) :
    centerLM m q = ∑ i, m i • q i := rfl

def W (m : Masses) : Submodule ℝ Configuration := (centerLM m).ker

def residual (m : Masses) (s : ℝ) (q : Configuration) : Configuration :=
  fun i => force m q i - anisotropy s (q i)

def IsSolution (m : Masses) (s : ℝ) (q : Configuration) : Prop :=
  CollisionFree q ∧ ∀ i, force m q i = anisotropy s (q i)

/- v2 lines 91--100, equation `eq:center-space`: cancellation and W.
   The pair sum includes the diagonal, whose vector contribution is zero.
   No assertion about a singular physical force at a collision is used. -/

private def weightedPair (m : Masses) (q : Configuration) (i j : Label) : Point :=
  (m i * m j / dist (q i) (q j) ^ 3) • (q i - q j)

private theorem weightedPair_self (m : Masses) (q : Configuration) (i : Label) :
    weightedPair m q i i = 0 := by
  simp [weightedPair]

private theorem weightedPair_swap (m : Masses) (q : Configuration) (i j : Label) :
    weightedPair m q j i = -weightedPair m q i j := by
  simp only [weightedPair, dist_comm (q j) (q i), mul_comm (m j) (m i)]
  rw [show q j - q i = -(q i - q j) by abel, smul_neg]

private theorem weighted_force_eq_sum (m : Masses) (q : Configuration) (i : Label) :
    m i • force m q i = ∑ j, weightedPair m q i j := by
  have h := Finset.sum_erase_add Finset.univ (weightedPair m q i) (Finset.mem_univ i)
  rw [weightedPair_self, add_zero] at h
  rw [← h]
  simp only [force, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [weightedPair, smul_smul]
  congr 1
  ring

theorem pairCancellation (m : Masses) (q : Configuration) :
    centerLM m (force m q) = 0 := by
  change (∑ i, m i • force m q i) = 0
  simp_rw [weighted_force_eq_sum]
  have hswap :
      (∑ i, ∑ j, weightedPair m q i j) =
        -(∑ i, ∑ j, weightedPair m q i j) := by
    calc
      (∑ i, ∑ j, weightedPair m q i j) =
          ∑ i, ∑ j, weightedPair m q j i := Finset.sum_comm
      _ = ∑ i, ∑ j, -weightedPair m q i j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact weightedPair_swap m q i j
      _ = -(∑ i, ∑ j, weightedPair m q i j) := by
        simp only [Finset.sum_neg_distrib]
  ext k
  have hk := congrArg (fun p : Point => p k) hswap
  change (∑ i, ∑ j, weightedPair m q i j) k =
    -((∑ i, ∑ j, weightedPair m q i j) k) at hk
  change (∑ i, ∑ j, weightedPair m q i j) k = 0
  linarith

theorem center_anisotropy (m : Masses) (s : ℝ) (q : Configuration) :
    centerLM m (fun i => anisotropy s (q i)) = anisotropy s (centerLM m q) := by
  change (∑ i, m i • anisotropy s (q i)) = anisotropy s (∑ i, m i • q i)
  simp only [map_sum, map_smul]

theorem center_residual (m : Masses) (s : ℝ) (q : Configuration) :
    centerLM m (residual m s q) = -anisotropy s (centerLM m q) := by
  change (∑ i, m i • (force m q i - anisotropy s (q i))) =
    -anisotropy s (centerLM m q)
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [show (∑ i, m i • force m q i) = 0 from pairCancellation m q]
  rw [show (∑ i, m i • anisotropy s (q i)) =
    anisotropy s (centerLM m q) from center_anisotropy m s q]
  simp

theorem anisotropy_injective {s : ℝ} (hs : s ≠ 0) :
    Function.Injective (anisotropy s) := by
  intro p t h
  ext k
  fin_cases k
  · have hx := congrArg (fun p : Point => p 0) h
    simp only [anisotropy_x] at hx
    exact mul_left_cancel₀ hs hx
  · have hy := congrArg (fun p : Point => p 1) h
    simpa using hy

theorem solution_center_zero (m : Masses) {s : ℝ} (hs : 0 < s)
    {q : Configuration} (hq : IsSolution m s q) : centerLM m q = 0 := by
  have hr : residual m s q = 0 := by
    funext i
    exact sub_eq_zero.mpr (hq.2 i)
  have hc := center_residual m s q
  rw [hr, map_zero] at hc
  have ha : anisotropy s (centerLM m q) = anisotropy s 0 := by
    rw [map_zero]
    exact neg_eq_zero.mp hc.symm
  exact anisotropy_injective (ne_of_gt hs) ha

theorem residual_mem_W (m : Masses) (s : ℝ) (q : W m) :
    residual m s (q : Configuration) ∈ W m := by
  change centerLM m (residual m s (q : Configuration)) = 0
  rw [center_residual]
  have hc : centerLM m (q : Configuration) = 0 := q.property
  rw [hc, map_zero, neg_zero]

/-- The actual original residual on the mass-centered vector space. Its
collision-free restriction is the manuscript's smooth residual map. -/
def restrictedResidual (m : Masses) (s : ℝ) : W m → W m :=
  fun q => ⟨residual m s (q : Configuration), residual_mem_W m s q⟩

/-- Derivative on W, with s held fixed. Smoothness on the collision-free
domain must be proved separately before using this in the main theorem. -/
def Nondegenerate (m : Masses) (s : ℝ) (q : W m) : Prop :=
  DifferentiableAt ℝ (restrictedResidual m s) q ∧
    Function.Bijective (fderiv ℝ (restrictedResidual m s) q)

theorem totalMass_pos {m : Masses} (hm : PositiveMasses m) : 0 < totalMass m := by
  apply Finset.sum_pos
  · intro i hi
    exact hm i
  · exact Finset.univ_nonempty

theorem centerLM_surjective {m : Masses} (hm : PositiveMasses m) :
    Function.Surjective (centerLM m) := by
  intro p
  have hM : totalMass m ≠ 0 := ne_of_gt (totalMass_pos hm)
  refine ⟨fun _ => (totalMass m)⁻¹ • p, ?_⟩
  change (∑ i, m i • ((totalMass m)⁻¹ • p)) = p
  rw [← Finset.sum_smul, smul_smul]
  change (totalMass m * (totalMass m)⁻¹) • p = p
  rw [mul_inv_cancel₀ hM, one_smul]

theorem finrank_point : Module.finrank ℝ Point = 2 :=
  finrank_euclideanSpace_fin

theorem finrank_configuration : Module.finrank ℝ Configuration = 8 := by
  change Module.finrank ℝ (Fin 4 → EuclideanSpace ℝ (Fin 2)) = 8
  rw [Module.finrank_pi_fintype]
  simp

/-- v2 eq:center-space. This is the original centered space's dimension;
no rotation or permutation quotient has been taken. -/
theorem finrank_W {m : Masses} (hm : PositiveMasses m) :
    Module.finrank ℝ (W m) = 6 := by
  change Module.finrank ℝ (LinearMap.ker (centerLM m)) = 6
  have h := LinearMap.finrank_range_add_finrank_ker (centerLM m)
  rw [LinearMap.range_eq_top.mpr (centerLM_surjective hm),
    finrank_top, finrank_point, finrank_configuration] at h
  exact Nat.add_left_cancel
    (show 2 + Module.finrank ℝ (LinearMap.ker (centerLM m)) = 2 + 6 from h)

theorem center_const (m : Masses) (p : Point) :
    centerLM m (fun _ => p) = totalMass m • p := by
  change (∑ i, m i • p) = totalMass m • p
  rw [← Finset.sum_smul]
  rfl

/-- Explicit projection to W, used only to transport smoothness into the
actual codomain subspace. It subtracts the physical mass mean. -/
def centeredProjection (m : Masses) (hm : PositiveMasses m) :
    Configuration →ₗ[ℝ] W m where
  toFun q := ⟨q - fun _ => (totalMass m)⁻¹ • centerLM m q, by
    change centerLM m (q - fun _ => (totalMass m)⁻¹ • centerLM m q) = 0
    rw [map_sub, center_const, smul_smul,
      mul_inv_cancel₀ (ne_of_gt (totalMass_pos hm)), one_smul, sub_self]⟩
  map_add' q t := by
    apply Subtype.ext
    funext i
    change q i + t i - (totalMass m)⁻¹ • centerLM m (q + t) =
      (q i - (totalMass m)⁻¹ • centerLM m q) +
        (t i - (totalMass m)⁻¹ • centerLM m t)
    rw [map_add, smul_add]
    abel
  map_smul' a q := by
    apply Subtype.ext
    funext i
    change a • q i - (totalMass m)⁻¹ • centerLM m (a • q) =
      a • (q i - (totalMass m)⁻¹ • centerLM m q)
    rw [map_smul, smul_sub, smul_smul, smul_smul]
    simp only [mul_comm]

theorem centeredProjection_eq_self (m : Masses) (hm : PositiveMasses m) (q : W m) :
    centeredProjection m hm (q : Configuration) = q := by
  apply Subtype.ext
  funext i
  change q.val i - (totalMass m)⁻¹ • centerLM m q.val = q.val i
  have hc : centerLM m q.val = 0 := q.property
  rw [hc, smul_zero, sub_zero]

theorem collisionFree_dist_pos {q : Configuration} (hq : CollisionFree q)
    {i j : Label} (hij : i ≠ j) : 0 < dist (q i) (q j) :=
  dist_pos.mpr (hq i j hij)

theorem collisionFree_iff_dist_pos (q : Configuration) :
    CollisionFree q ↔ ∀ i j, i ≠ j → 0 < dist (q i) (q j) := by
  constructor
  · intro hq i j hij
    exact collisionFree_dist_pos hq hij
  · intro hq i j hij
    exact dist_pos.mp (hq i j hij)

theorem isOpen_collisionFree : IsOpen {q : Configuration | CollisionFree q} := by
  have hset : {q : Configuration | CollisionFree q} =
      ⋂ i : Label, ⋂ j : Label,
        {q : Configuration | i ≠ j → q i ≠ q j} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, CollisionFree]
  rw [hset]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases hij : i = j
  · simp only [hij, ne_eq, not_true_eq_false, false_implies, Set.ofPred_true]
    exact isOpen_univ
  · convert isOpen_ne_fun
      (f := fun q : Configuration => q i) (g := fun q : Configuration => q j)
      (continuous_apply i) (continuous_apply j) using 1
    ext q
    simp [hij]

/- Smoothness is checked on the physical collision-free domain; in particular
the totalized force at collisions cannot justify differentiability claims.
The generic smoothness order permits n = ω (real analyticity), not just ∞. -/
theorem contDiffAt_force (m : Masses) (n : WithTop ℕ∞) {q : Configuration}
    (hq : CollisionFree q) (i : Label) : ContDiffAt ℝ n (fun q => force m q i) q := by
  unfold force
  apply ContDiffAt.sum
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hd : ContDiffAt ℝ n (fun q : Configuration => dist (q i) (q j)) q :=
    (contDiffAt_apply ℝ Point i q).dist ℝ
      (contDiffAt_apply ℝ Point j q) (hq i j hji.symm)
  have hden : dist (q i) (q j) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (ne_of_gt (collisionFree_dist_pos hq hji.symm))
  exact ((contDiffAt_const (c := m j)).div (hd.pow 3) hden).smul
    ((contDiffAt_apply ℝ Point i q).sub (contDiffAt_apply ℝ Point j q))

theorem contDiffAt_residual (m : Masses) (s : ℝ) (n : WithTop ℕ∞)
    {q : Configuration} (hq : CollisionFree q) : ContDiffAt ℝ n (residual m s) q := by
  apply contDiffAt_pi.mpr
  intro i
  exact (contDiffAt_force m n hq i).sub
    ((anisotropy s).toContinuousLinearMap.contDiff.contDiffAt.comp q
      (contDiffAt_apply ℝ Point i q))

theorem contDiffAt_restrictedResidual (m : Masses) (hm : PositiveMasses m)
    (s : ℝ) (n : WithTop ℕ∞) {q : W m} (hq : CollisionFree (q : Configuration)) :
    ContDiffAt ℝ n (restrictedResidual m s) q := by
  have heq : restrictedResidual m s = fun t : W m =>
      centeredProjection m hm (residual m s (t : Configuration)) := by
    funext t
    exact (centeredProjection_eq_self m hm (restrictedResidual m s t)).symm
  rw [heq]
  exact (centeredProjection m hm).toContinuousLinearMap.contDiff.contDiffAt.comp q
    ((contDiffAt_residual m s n hq).comp q (W m).subtypeL.contDiff.contDiffAt)

theorem collisionFree_positive_dilation {q : Configuration} (hq : CollisionFree q)
    {a : ℝ} (ha : 0 < a) : CollisionFree (a • q) := by
  intro i j hij heq
  have hzero : a • (q i - q j) = 0 := by
    simpa only [smul_sub, Pi.smul_apply, sub_eq_zero] using heq
  have hdiff : q i - q j = 0 := (smul_eq_zero.mp hzero).resolve_left (ne_of_gt ha)
  exact hq i j hij (sub_eq_zero.mp hdiff)

theorem dist_positive_dilation {a : ℝ} (ha : 0 < a) (p t : Point) :
    dist (a • p) (a • t) = a * dist p t := by
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ha,
    dist_eq_norm]

/-- The degree -2 physical force homogeneity used in v2 normalization and
in the exact horizontal-axis branches. The scale is strictly positive. -/
theorem force_positive_dilation (m : Masses) {q : Configuration}
    (hq : CollisionFree q) {a : ℝ} (ha : 0 < a) (i : Label) :
    force m (a • q) i = (a ^ 2)⁻¹ • force m q i := by
  simp only [force, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hd : dist (q i) (q j) ≠ 0 := ne_of_gt (collisionFree_dist_pos hq hji.symm)
  simp only [Pi.smul_apply, dist_positive_dilation ha, ← smul_sub, smul_smul]
  congr 1
  field_simp [ne_of_gt ha, hd]

/- v2 lines 726--733: an affine collinear solution has its containing
line through zero, and that line must be a coordinate axis for s > 1.
The parametrization is of the full affine line with a nonzero direction.
No direction normalization or symmetry identification is performed. -/

def Collinear (q : Configuration) : Prop :=
  ∃ c e : Point, e ≠ 0 ∧ ∃ t : Label → ℝ, ∀ i, q i = c + t i • e

def LineThroughOrigin (q : Configuration) : Prop :=
  ∃ e : Point, e ≠ 0 ∧ ∃ t : Label → ℝ, ∀ i, q i = t i • e

def OnXAxis (q : Configuration) : Prop := ∀ i, q i 1 = 0

def OnYAxis (q : Configuration) : Prop := ∀ i, q i 0 = 0

theorem onXAxis_collinear {q : Configuration} (hq : OnXAxis q) : Collinear q := by
  refine ⟨0, !₂[1, 0], ?_, fun i => q i 0, ?_⟩
  · intro h
    have hx := congrArg (fun p : Point => p 0) h
    simp at hx
  · intro i
    ext k
    fin_cases k <;> simp [hq i]

theorem onYAxis_collinear {q : Configuration} (hq : OnYAxis q) : Collinear q := by
  refine ⟨0, !₂[0, 1], ?_, fun i => q i 1, ?_⟩
  · intro h
    have hy := congrArg (fun p : Point => p 1) h
    simp at hy
  · intro i
    ext k
    fin_cases k <;> simp [hq i]

theorem axes_disjoint_of_collisionFree {q : Configuration} (hq : CollisionFree q) :
    ¬(OnXAxis q ∧ OnYAxis q) := by
  rintro ⟨hx, hy⟩
  have hzero : ∀ i, q i = 0 := by
    intro i
    ext k
    fin_cases k
    · exact hy i
    · exact hx i
  exact hq 0 1 (by decide) (by rw [hzero 0, hzero 1])

theorem collinear_centered_through_origin {m : Masses} (hm : PositiveMasses m)
    {q : Configuration} (hc : centerLM m q = 0) (hq : Collinear q) :
    LineThroughOrigin q := by
  rcases hq with ⟨c, e, he, t, ht⟩
  let T : ℝ := ∑ i, m i * t i
  have hM : totalMass m ≠ 0 := ne_of_gt (totalMass_pos hm)
  have hct : totalMass m • c + T • e = 0 := by
    change (∑ i, m i • q i) = 0 at hc
    simpa only [ht, smul_add, smul_smul, Finset.sum_add_distrib,
      ← Finset.sum_smul, totalMass, T] using hc
  have hc' : c = (-T / totalMass m) • e := by
    ext k
    have hk := congrArg (fun p : Point => p k) hct
    change totalMass m * c k + T * e k = 0 at hk
    change c k = (-T / totalMass m) * e k
    field_simp [hM]
    nlinarith
  refine ⟨e, he, fun i => t i - T / totalMass m, ?_⟩
  intro i
  rw [ht i, hc', sub_smul, neg_div, neg_smul]
  abel

theorem force_parallel_of_line {m : Masses} {q : Configuration} {e : Point}
    {t : Label → ℝ} (hq : ∀ i, q i = t i • e) (i : Label) :
    ∃ a : ℝ, force m q i = a • e := by
  refine ⟨∑ j ∈ Finset.univ.erase i,
    m j / dist (q i) (q j) ^ 3 * (t i - t j), ?_⟩
  simp only [force, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hq i, hq j, ← sub_smul, smul_smul]

theorem diagonal_eigenvector_axis {s a : ℝ} (hs : 1 < s) {e : Point}
    (he : anisotropy s e = a • e) : e 0 = 0 ∨ e 1 = 0 := by
  have hx := congrArg (fun p : Point => p 0) he
  have hy := congrArg (fun p : Point => p 1) he
  change s * e 0 = a * e 0 at hx
  change e 1 = a * e 1 at hy
  by_cases hx0 : e 0 = 0
  · exact Or.inl hx0
  · right
    by_contra hy0
    have hsa : s = a := mul_right_cancel₀ hx0 hx
    have h1a : 1 = a := mul_right_cancel₀ hy0 (by simpa only [one_mul] using hy)
    linarith

theorem collinear_solution_axis {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 1 < s) {q : Configuration} (hq : IsSolution m s q)
    (hcol : Collinear q) : OnXAxis q ∨ OnYAxis q := by
  have hc : centerLM m q = 0 := solution_center_zero m (by linarith) hq
  rcases collinear_centered_through_origin hm hc hcol with ⟨e, he, t, ht⟩
  have ht_ne : ∃ i, t i ≠ 0 := by
    by_contra h
    push Not at h
    have h01 : q (0 : Label) = q (1 : Label) := by simp [ht, h]
    exact hq.1 0 1 (by decide) h01
  rcases ht_ne with ⟨i, hi⟩
  rcases force_parallel_of_line ht i with ⟨a, ha⟩
  have hae : t i • anisotropy s e = a • e := by
    rw [← map_smul, ← ht i, ← hq.2 i, ha]
  have heig : anisotropy s e = (a / t i) • e := by
    calc
      anisotropy s e = (t i)⁻¹ • (t i • anisotropy s e) := by
        rw [smul_smul, inv_mul_cancel₀ hi, one_smul]
      _ = (t i)⁻¹ • (a • e) := by rw [hae]
      _ = (a / t i) • e := by rw [smul_smul]; congr 1; ring
  rcases diagonal_eigenvector_axis hs heig with hex | hey
  · right
    intro j
    rw [ht j]
    change t j * e 0 = 0
    rw [hex, mul_zero]
  · left
    intro j
    rw [ht j]
    change t j * e 1 = 0
    rw [hey, mul_zero]

theorem solution_collinear_iff_axes {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 1 < s) {q : Configuration} (hq : IsSolution m s q) :
    Collinear q ↔ OnXAxis q ∨ OnYAxis q := by
  constructor
  · exact collinear_solution_axis hm hs hq
  · rintro (hx | hy)
    · exact onXAxis_collinear hx
    · exact onYAxis_collinear hy

end FourBody

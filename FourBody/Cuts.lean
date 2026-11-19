import FourBody.Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination

/-!
Proof draft for the mass-averaged cut identities in v2 Lemma 2.1.
Baseline TeX SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
This module uses the actual force from `FourBody.Geometry`; no estimate is
assumed as an analytical interface. It adapts the generic finite-sum proofs
read from the explicitly authorized legacy project's ForceBalance.lean
(SHA256 D1B383624140C24EFE3ED16E54DA6AC021F7A825B37B74A93795EE48A9F8A25E)
and CollisionGeometry.lean
(SHA256 F2B7702BB9783E29E2CBC4F0ED9D3CFD553B23D1119F7D6987F6C8E3BB341901).
The source label type is Fin 5; these finite algebra proofs are adapted to
Fin 4, with the force sign reversed and the coordinate multiplier lam retained.
No isotropic five-body conclusion is used as an anisotropic hypothesis.
Actual compilation status is retained in the separate logs and source hashes.
-/

noncomputable section
open scoped BigOperators

namespace FourBody

def coordinateLM (k : Axis) : Point →ₗ[ℝ] ℝ where
  toFun p := p k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cutComplement (A : Finset Label) : Finset Label := Finset.univ \ A

def cutMass (m : Masses) (A : Finset Label) : ℝ := ∑ i ∈ A, m i

def cutMoment (m : Masses) (q : Configuration) (k : Axis) (A : Finset Label) : ℝ :=
  ∑ i ∈ A, m i * q i k

def cutMean (m : Masses) (q : Configuration) (k : Axis) (A : Finset Label) : ℝ :=
  cutMoment m q k A / cutMass m A

def cutCrossForce (m : Masses) (q : Configuration) (k : Axis) (A : Finset Label) : ℝ :=
  ∑ i ∈ A, ∑ j ∈ cutComplement A,
    (m i * m j / dist (q i) (q j) ^ 3) * (q j k - q i k)

def cutCrossGap (m : Masses) (q : Configuration) (k : Axis) (A : Finset Label) : ℝ :=
  ∑ i ∈ A, ∑ j ∈ cutComplement A, m i * m j * (q j k - q i k)

def coordinatePair (m : Masses) (q : Configuration) (k : Axis) (i j : Label) : ℝ :=
  (m i * m j / dist (q i) (q j) ^ 3) * (q i k - q j k)

@[simp] theorem coordinatePair_self (m : Masses) (q : Configuration)
    (k : Axis) (i : Label) : coordinatePair m q k i i = 0 := by
  simp [coordinatePair]

theorem coordinatePair_swap (m : Masses) (q : Configuration)
    (k : Axis) (i j : Label) : coordinatePair m q k j i = -coordinatePair m q k i j := by
  simp only [coordinatePair, dist_comm (q j) (q i)]
  ring

theorem force_coordinate (m : Masses) (q : Configuration) (k : Axis) (i : Label) :
    force m q i k = ∑ j ∈ Finset.univ.erase i,
      (m j / dist (q i) (q j) ^ 3) * (q i k - q j k) := by
  change coordinateLM k (∑ j ∈ Finset.univ.erase i,
    (m j / dist (q i) (q j) ^ 3) • (q i - q j)) = _
  rw [map_sum]
  rfl

theorem weighted_force_coordinate (m : Masses) (q : Configuration)
    (k : Axis) (i : Label) :
    m i * force m q i k = ∑ j, coordinatePair m q k i j := by
  have h := Finset.sum_erase_add Finset.univ
    (coordinatePair m q k i) (Finset.mem_univ i)
  rw [coordinatePair_self, add_zero] at h
  rw [force_coordinate, Finset.mul_sum, ← h]
  apply Finset.sum_congr rfl
  intro j hj
  unfold coordinatePair
  ring

theorem internal_coordinate_pair_sum_zero (m : Masses) (q : Configuration)
    (k : Axis) (A : Finset Label) :
    (∑ i ∈ A, ∑ j ∈ A, coordinatePair m q k i j) = 0 := by
  have hswap :
      (∑ i ∈ A, ∑ j ∈ A, coordinatePair m q k i j) =
      -(∑ i ∈ A, ∑ j ∈ A, coordinatePair m q k i j) := by
    calc
      (∑ i ∈ A, ∑ j ∈ A, coordinatePair m q k i j) =
          ∑ i ∈ A, ∑ j ∈ A, coordinatePair m q k j i := Finset.sum_comm
      _ = ∑ i ∈ A, ∑ j ∈ A, -coordinatePair m q k i j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact coordinatePair_swap m q k i j
      _ = -(∑ i ∈ A, ∑ j ∈ A, coordinatePair m q k i j) := by
        simp only [Finset.sum_neg_distrib]
  linarith

theorem weighted_cut_force (m : Masses) (q : Configuration) (k : Axis)
    (A : Finset Label) :
    (∑ i ∈ A, m i * force m q i k) = -cutCrossForce m q k A := by
  simp_rw [weighted_force_coordinate]
  have hsplit (i : Label) :
      (∑ j, coordinatePair m q k i j) =
        (∑ j ∈ cutComplement A, coordinatePair m q k i j) +
          ∑ j ∈ A, coordinatePair m q k i j :=
    (Finset.sum_sdiff (Finset.subset_univ A)).symm
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, internal_coordinate_pair_sum_zero, add_zero]
  unfold cutCrossForce
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  unfold coordinatePair
  ring

theorem total_force_coordinate_zero (m : Masses) (q : Configuration) (k : Axis) :
    (∑ i, m i * force m q i k) = 0 := by
  have h := congrArg (coordinateLM k) (pairCancellation m q)
  change coordinateLM k (∑ i, m i • force m q i) = coordinateLM k 0 at h
  rw [map_sum, map_zero] at h
  exact h

theorem cutMass_pos {m : Masses} (hm : PositiveMasses m)
    {A : Finset Label} (hA : A.Nonempty) : 0 < cutMass m A :=
  Finset.sum_pos (fun i _ => hm i) hA

theorem cutMass_complement (m : Masses) (A : Finset Label) :
    cutMass m A + cutMass m (cutComplement A) = totalMass m := by
  unfold cutMass cutComplement totalMass
  rw [add_comm]
  exact Finset.sum_sdiff (Finset.subset_univ A)

theorem double_cut_mass (m : Masses) (A B : Finset Label) :
    (∑ i ∈ A, ∑ j ∈ B, m i * m j) = cutMass m A * cutMass m B := by
  unfold cutMass
  rw [← Finset.sum_mul_sum]

theorem weighted_cut_equation {m : Masses} {q : Configuration} {k : Axis}
    {lam : ℝ} (hEq : ∀ i, force m q i k = lam * q i k) (A : Finset Label) :
    lam * cutMoment m q k A = -cutCrossForce m q k A := by
  have hsum : (∑ i ∈ A, m i * force m q i k) = lam * cutMoment m q k A := by
    simp_rw [hEq]
    simp only [cutMoment, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [← hsum]
  exact weighted_cut_force m q k A

theorem weighted_complement_equation {m : Masses} {q : Configuration} {k : Axis}
    {lam : ℝ} (hEq : ∀ i, force m q i k = lam * q i k) (A : Finset Label) :
    lam * cutMoment m q k (cutComplement A) = cutCrossForce m q k A := by
  have hsum : (∑ i ∈ cutComplement A, m i * force m q i k) =
      lam * cutMoment m q k (cutComplement A) := by
    simp_rw [hEq]
    simp only [cutMoment, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have htotal : (∑ i ∈ cutComplement A, m i * force m q i k) +
      (∑ i ∈ A, m i * force m q i k) = 0 := by
    rw [show (∑ i ∈ cutComplement A, m i * force m q i k) +
        (∑ i ∈ A, m i * force m q i k) =
          ∑ i, m i * force m q i k from Finset.sum_sdiff (Finset.subset_univ A)]
    exact total_force_coordinate_zero m q k
  rw [weighted_cut_force m q k A, hsum] at htotal
  linarith

/-- The exact finite mass-averaged cut identity in Lemma 2.1. The coordinate
equations are derived from `IsSolution` by the final diameter theorem. -/
theorem weighted_mean_cut_identity {m : Masses} {q : Configuration} {k : Axis}
    {lam : ℝ} (hEq : ∀ i, force m q i k = lam * q i k) (A : Finset Label) :
    lam * (cutMean m q k (cutComplement A) - cutMean m q k A) =
      (1 / cutMass m A + 1 / cutMass m (cutComplement A)) * cutCrossForce m q k A := by
  unfold cutMean
  calc
    lam * (cutMoment m q k (cutComplement A) / cutMass m (cutComplement A) -
        cutMoment m q k A / cutMass m A) =
        (lam * cutMoment m q k (cutComplement A)) / cutMass m (cutComplement A) -
          (lam * cutMoment m q k A) / cutMass m A := by ring
    _ = cutCrossForce m q k A / cutMass m (cutComplement A) -
          (-cutCrossForce m q k A) / cutMass m A := by
      rw [weighted_complement_equation hEq A, weighted_cut_equation hEq A]
    _ = (1 / cutMass m A + 1 / cutMass m (cutComplement A)) *
          cutCrossForce m q k A := by ring

theorem cutCrossGap_identity (m : Masses) (q : Configuration) (k : Axis)
    (A : Finset Label) :
    cutCrossGap m q k A = cutMass m A * cutMoment m q k (cutComplement A) -
      cutMoment m q k A * cutMass m (cutComplement A) := by
  -- Direct finite-label adaptation of legacy weighted_projection_separation.
  unfold cutCrossGap
  calc
    (∑ i ∈ A, ∑ j ∈ cutComplement A, m i * m j * (q j k - q i k)) =
        ∑ i ∈ A, ∑ j ∈ cutComplement A,
          (m i * (m j * q j k) - (m i * q i k) * m j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ i ∈ A, m i) * (∑ j ∈ cutComplement A, m j * q j k) -
        (∑ i ∈ A, m i * q i k) * (∑ j ∈ cutComplement A, m j) := by
      simp_rw [Finset.sum_sub_distrib]
      rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum]
    _ = _ := rfl

theorem cutMean_difference_identity {m : Masses} (hm : PositiveMasses m)
    (q : Configuration) (k : Axis) {A : Finset Label} (hA : A.Nonempty)
    (hB : (cutComplement A).Nonempty) :
    cutMean m q k (cutComplement A) - cutMean m q k A =
      cutCrossGap m q k A / (cutMass m A * cutMass m (cutComplement A)) := by
  have hMA := ne_of_gt (cutMass_pos hm hA)
  have hMB := ne_of_gt (cutMass_pos hm hB)
  rw [cutCrossGap_identity]
  unfold cutMean
  field_simp [hMA, hMB]

theorem cutMean_gap_lower {m : Masses} (hm : PositiveMasses m)
    (q : Configuration) (k : Axis) {A : Finset Label} (hA : A.Nonempty)
    (hB : (cutComplement A).Nonempty) {g : ℝ}
    (hgap : ∀ i ∈ A, ∀ j ∈ cutComplement A, g ≤ q j k - q i k) :
    g ≤ cutMean m q k (cutComplement A) - cutMean m q k A := by
  have hp : 0 < cutMass m A * cutMass m (cutComplement A) :=
    mul_pos (cutMass_pos hm hA) (cutMass_pos hm hB)
  rw [cutMean_difference_identity hm q k hA hB]
  apply (le_div_iff₀ hp).mpr
  calc
    g * (cutMass m A * cutMass m (cutComplement A)) =
        ∑ i ∈ A, ∑ j ∈ cutComplement A, m i * m j * g := by
      -- Same mass-product distribution as legacy projectedClusterGap bounds.
      rw [mul_comm g]
      unfold cutMass
      rw [Finset.sum_mul_sum]
      simp only [Finset.sum_mul]
    _ ≤ cutCrossGap m q k A := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hgap i hi j hj) (mul_nonneg (hm i).le (hm j).le)

theorem positive_coordinate_gap_le_dist {q : Configuration} {k : Axis}
    {i j : Label} (hgap : 0 < q j k - q i k) :
    q j k - q i k ≤ dist (q i) (q j) := by
  have h := PiLp.dist_apply_le (q i) (q j) k
  simpa only [Real.dist_eq, abs_sub_comm (q i k) (q j k), abs_of_pos hgap] using h

theorem force_factor_gap_upper {r δ g : ℝ} (hg : 0 < g) (hgd : g ≤ δ)
    (hdr : δ ≤ r) : δ / r ^ 3 ≤ 1 / g ^ 2 := by
  have hr : 0 < r := lt_of_lt_of_le hg (hgd.trans hdr)
  have hgr : g ≤ r := hgd.trans hdr
  calc
    δ / r ^ 3 ≤ r / r ^ 3 := div_le_div_of_nonneg_right hdr (pow_pos hr 3).le
    _ = 1 / r ^ 2 := by field_simp [ne_of_gt hr]
    _ ≤ 1 / g ^ 2 := by
      apply one_div_le_one_div_of_le (pow_pos hg 2)
      nlinarith

theorem cutCrossForce_upper {m : Masses} (hm : PositiveMasses m)
    (q : Configuration) (k : Axis) (A : Finset Label) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ i ∈ A, ∀ j ∈ cutComplement A, g ≤ q j k - q i k) :
    cutCrossForce m q k A ≤ cutMass m A * cutMass m (cutComplement A) / g ^ 2 := by
  calc
    cutCrossForce m q k A ≤
        ∑ i ∈ A, ∑ j ∈ cutComplement A, (m i * m j) / g ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hgd := hgap i hi j hj
      have hd := positive_coordinate_gap_le_dist (lt_of_lt_of_le hg hgd)
      have hb := force_factor_gap_upper hg hgd hd
      have hmij : 0 ≤ m i * m j := mul_nonneg (hm i).le (hm j).le
      convert mul_le_mul_of_nonneg_left hb hmij using 1 <;> ring
    _ = cutMass m A * cutMass m (cutComplement A) / g ^ 2 := by
      rw [← double_cut_mass]
      simp only [Finset.sum_div]

theorem cut_gap_cube_bound {m : Masses} (hm : PositiveMasses m)
    (q : Configuration) (k : Axis) {lam : ℝ} (hlam : 0 < lam)
    (hEq : ∀ i, force m q i k = lam * q i k) {A : Finset Label}
    (hA : A.Nonempty) (hB : (cutComplement A).Nonempty) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ i ∈ A, ∀ j ∈ cutComplement A, g ≤ q j k - q i k) :
    lam * g ^ 3 ≤ totalMass m := by
  have hMA : 0 < cutMass m A := cutMass_pos hm hA
  have hMB : 0 < cutMass m (cutComplement A) := cutMass_pos hm hB
  have hp : 0 ≤ 1 / cutMass m A + 1 / cutMass m (cutComplement A) :=
    add_nonneg (one_div_pos.mpr hMA).le (one_div_pos.mpr hMB).le
  have hb : lam * g ≤ totalMass m / g ^ 2 := by
    calc
      lam * g ≤ lam * (cutMean m q k (cutComplement A) - cutMean m q k A) :=
        mul_le_mul_of_nonneg_left (cutMean_gap_lower hm q k hA hB hgap) hlam.le
      _ = (1 / cutMass m A + 1 / cutMass m (cutComplement A)) *
          cutCrossForce m q k A := weighted_mean_cut_identity hEq A
      _ ≤ (1 / cutMass m A + 1 / cutMass m (cutComplement A)) *
          (cutMass m A * cutMass m (cutComplement A) / g ^ 2) :=
        mul_le_mul_of_nonneg_left (cutCrossForce_upper hm q k A hg hgap) hp
      _ = totalMass m / g ^ 2 := by
        rw [← cutMass_complement m A]
        field_simp [ne_of_gt hMA, ne_of_gt hMB, ne_of_gt hg]
        ring
  have h := (le_div_iff₀ (pow_pos hg 2)).mp hb
  calc
    lam * g ^ 3 = (lam * g) * g ^ 2 := by ring
    _ ≤ totalMass m := h

theorem gap_le_mass_cube_root {m : Masses} (hm : PositiveMasses m)
    {lam g : ℝ} (hlam : 0 < lam) (hg : 0 < g)
    (hbound : lam * g ^ 3 ≤ totalMass m) :
    g ≤ (totalMass m / lam) ^ (1 / (3 : ℝ)) := by
  have hM : 0 ≤ totalMass m / lam := (div_pos (totalMass_pos hm) hlam).le
  have hcube : g ^ 3 ≤ totalMass m / lam := (le_div_iff₀ hlam).mpr (by nlinarith)
  have hrpow : g ^ (3 : ℝ) ≤ totalMass m / lam := by
    simpa only [Real.rpow_ofNat] using hcube
  simpa only [one_div] using
    (Real.le_rpow_inv_iff_of_pos hg.le hM (show (0 : ℝ) < 3 by norm_num)).mpr hrpow

end FourBody

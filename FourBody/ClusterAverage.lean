import FourBody.Cuts
import FourBody.ClusterVertical

/-!
The vector-valued external mean estimate in actual v2 Proposition 2.2,
TeX line 289. Baseline manuscript SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

The means here are actual mass-normalized finite vector sums in the
manuscript's `EuclideanSpace ℝ (Fin 2)`. The final bound applies to the
actual Newtonian external field and its proved-on-hull Lipschitz property.
No estimate on weighted means is accepted as a premise. The generic
finite-sum lemmas preceding it prove the required representation and norm
estimate for any vector field, using the actual positive masses.
-/

noncomputable section
open scoped BigOperators

namespace FourBody.ClusterAverage

def weightedVectorSum (m : Masses) (q : Configuration) (E : Point → Point)
    (A : Finset Label) : Point :=
  ∑ i ∈ A, m i • E (q i)

def weightedVectorMean (m : Masses) (q : Configuration) (E : Point → Point)
    (A : Finset Label) : Point :=
  (cutMass m A)⁻¹ • weightedVectorSum m q E A

def doubleWeightedDifference (m : Masses) (q : Configuration) (E : Point → Point)
    (A B : Finset Label) : Point :=
  ∑ i ∈ A, ∑ j ∈ B, (m i * m j) • (E (q j) - E (q i))

/-- Exact finite vector identity before mass normalization. -/
theorem doubleWeightedDifference_eq (m : Masses) (q : Configuration)
    (E : Point → Point) (A B : Finset Label) :
    doubleWeightedDifference m q E A B =
      cutMass m A • weightedVectorSum m q E B -
        cutMass m B • weightedVectorSum m q E A := by
  unfold doubleWeightedDifference
  calc
    (∑ i ∈ A, ∑ j ∈ B, (m i * m j) • (E (q j) - E (q i))) =
        ∑ i ∈ A, (m i • weightedVectorSum m q E B -
          cutMass m B • (m i • E (q i))) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (∑ j ∈ B, (m i * m j) • (E (q j) - E (q i))) =
            (∑ j ∈ B, m i • (m j • E (q j))) -
              ∑ j ∈ B, m j • (m i • E (q i)) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          simp only [smul_sub, smul_smul, mul_comm]
        _ = m i • weightedVectorSum m q E B -
            cutMass m B • (m i • E (q i)) := by
          simp only [weightedVectorSum, cutMass,
            ← Finset.smul_sum, ← Finset.sum_smul]
    _ = cutMass m A • weightedVectorSum m q E B -
        cutMass m B • weightedVectorSum m q E A := by
      simp only [Finset.sum_sub_distrib, weightedVectorSum, cutMass,
        ← Finset.smul_sum, ← Finset.sum_smul]

/-- Difference of the genuine weighted means as a normalized double sum.
Nonempty sides and positive masses justify the inverse cancellations. -/
theorem weightedVectorMean_difference {m : Masses} (hm : PositiveMasses m)
    (q : Configuration) (E : Point → Point) (A B : Finset Label)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    weightedVectorMean m q E B - weightedVectorMean m q E A =
      (cutMass m A * cutMass m B)⁻¹ • doubleWeightedDifference m q E A B := by
  have hMA := ne_of_gt (cutMass_pos hm hA)
  have hMB := ne_of_gt (cutMass_pos hm hB)
  have hcoeffB : (cutMass m A * cutMass m B)⁻¹ * cutMass m A =
      (cutMass m B)⁻¹ := by field_simp [hMA, hMB]
  have hcoeffA : (cutMass m A * cutMass m B)⁻¹ * cutMass m B =
      (cutMass m A)⁻¹ := by field_simp [hMA, hMB]
  rw [doubleWeightedDifference_eq, smul_sub]
  simp only [weightedVectorMean, smul_smul, hcoeffB, hcoeffA]

/-- Positive finite vector weights preserve a uniform pairwise norm bound. -/
theorem doubleWeightedDifference_norm_bound {m : Masses} (hm : PositiveMasses m)
    (q : Configuration) (E : Point → Point) (A B : Finset Label) {C : ℝ}
    (hbound : ∀ i ∈ A, ∀ j ∈ B, ‖E (q j) - E (q i)‖ ≤ C) :
    ‖doubleWeightedDifference m q E A B‖ ≤ cutMass m A * cutMass m B * C := by
  unfold doubleWeightedDifference
  calc
    ‖∑ i ∈ A, ∑ j ∈ B, (m i * m j) • (E (q j) - E (q i))‖ ≤
        ∑ i ∈ A, ‖∑ j ∈ B, (m i * m j) • (E (q j) - E (q i))‖ :=
      norm_sum_le A _
    _ ≤ ∑ i ∈ A, ∑ j ∈ B, m i * m j * C := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ‖∑ j ∈ B, (m i * m j) • (E (q j) - E (q i))‖ ≤
            ∑ j ∈ B, ‖(m i * m j) • (E (q j) - E (q i))‖ :=
          norm_sum_le B _
        _ ≤ ∑ j ∈ B, m i * m j * C := by
          apply Finset.sum_le_sum
          intro j hj
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos (hm i) (hm j))]
          exact mul_le_mul_of_nonneg_left (hbound i hi j hj)
            (mul_nonneg (hm i).le (hm j).le)
    _ = cutMass m A * cutMass m B * C := by
      rw [← double_cut_mass m A B]
      simp only [Finset.sum_mul]

theorem weightedVectorMean_difference_norm_bound {m : Masses} (hm : PositiveMasses m)
    (q : Configuration) (E : Point → Point) (A B : Finset Label)
    (hA : A.Nonempty) (hB : B.Nonempty) {C : ℝ}
    (hbound : ∀ i ∈ A, ∀ j ∈ B, ‖E (q j) - E (q i)‖ ≤ C) :
    ‖weightedVectorMean m q E B - weightedVectorMean m q E A‖ ≤ C := by
  have hmass : 0 < cutMass m A * cutMass m B :=
    mul_pos (cutMass_pos hm hA) (cutMass_pos hm hB)
  rw [weightedVectorMean_difference hm q E A B hA hB,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmass)]
  calc
    (cutMass m A * cutMass m B)⁻¹ * ‖doubleWeightedDifference m q E A B‖ ≤
        (cutMass m A * cutMass m B)⁻¹ * (cutMass m A * cutMass m B * C) :=
      mul_le_mul_of_nonneg_left (doubleWeightedDifference_norm_bound hm q E A B hbound)
        (inv_nonneg.mpr hmass.le)
    _ = C := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hmass), one_mul]

/-- The actual vector norm assertion for the manuscript's averaged
Newtonian complement field, derived from its actual on-hull Lipschitz
estimate and the actual physical cluster diameter bound. -/
theorem external_weightedVectorMean_difference_norm_bound {m : Masses}
    (hm : PositiveMasses m) (q : Configuration) (J A B : Finset Label)
    (hAJ : A ⊆ J) (hBJ : B ⊆ J) (hA : A.Nonempty) (hB : B.Nonempty)
    {L r : ℝ} (hL : 0 ≤ L)
    (hLip : ClusterVertical.LipschitzOnHull m q J L)
    (hdiam : ∀ i ∈ J, ∀ j ∈ J, dist (q i) (q j) ≤ r) :
    ‖weightedVectorMean m q (ClusterVertical.externalField m q J) B -
        weightedVectorMean m q (ClusterVertical.externalField m q J) A‖ ≤ L * r := by
  apply weightedVectorMean_difference_norm_bound hm q _ A B hA hB
  intro i hi j hj
  have hfield := hLip (q j) (ClusterVertical.body_mem_hull q J (hBJ hj))
    (q i) (ClusterVertical.body_mem_hull q J (hAJ hi))
  have hd := mul_le_mul_of_nonneg_left (hdiam j (hBJ hj) i (hAJ hi)) hL
  simpa only [dist_eq_norm] using hfield.trans hd

end FourBody.ClusterAverage

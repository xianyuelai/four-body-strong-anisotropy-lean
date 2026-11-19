import FourBody.BlowupResidual

/-!
Exact positive-ε force decomposition and F=Tε Rε⁻³ Qε.
All fields are concrete definitions from v2. The only separation premise
is the literal noncollision of each internal pair; it will be obtained
from the positive-distance neighborhood of a seed, not assumed as a
theorem about the complete branch.
Static preparation; current compiler checking remains pending.
-/

noncomputable section
open scoped BigOperators
namespace FourBody

def InternallySeparated {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) : Prop :=
  ∀ i j, blockOf d i = blockOf d j → i ≠ j →
    internalCoordinates h i ≠ internalCoordinates h j

theorem physicalCoordinates_difference_sameBlock {m : Masses}
    {d : OrderedClusterDatum} (ε : ℝ) (h : BlowupCoordinates m d)
    (i j : Label) (hblock : blockOf d i = blockOf d j) :
    physicalCoordinates ε h i - physicalCoordinates ε h j =
      ε • (internalCoordinates h i - internalCoordinates h j) := by
  ext k
  fin_cases k <;> simp [physicalCoordinates, internalCoordinates, hblock] <;> ring

theorem internalRho_ne_zero {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (hsep : InternallySeparated h)
    (i j : Label) (hblock : blockOf d i = blockOf d j) (hij : i ≠ j) :
    internalRho h i j ≠ 0 := by
  exact ne_of_gt (dist_pos.mpr (hsep i j hblock hij))

theorem physicalNewtonForce_internal_scale {m : Masses}
    {d : OrderedClusterDatum} {ε : ℝ} (hε : 0 < ε)
    (h : BlowupCoordinates m d) (hsep : InternallySeparated h)
    (i j : Label) (hblock : blockOf d i = blockOf d j) (hij : i ≠ j) :
    Reuse.physicalNewtonForce (m j) (physicalCoordinates ε h j)
      (physicalCoordinates ε h i) =
      (ε ^ 2)⁻¹ • Reuse.physicalNewtonForce (m j)
        (internalCoordinates h j) (internalCoordinates h i) := by
  have hrho := internalRho_ne_zero h hsep i j hblock hij
  have hdist : dist (physicalCoordinates ε h i) (physicalCoordinates ε h j) =
      ε * internalRho h i j := by
    rw [dist_eq_norm, physicalCoordinates_difference_sameBlock ε h i j hblock,
      norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    rfl
  simp only [Reuse.physicalNewtonForce, hdist,
    physicalCoordinates_difference_sameBlock ε h i j hblock, smul_smul]
  change (m j / (ε * internalRho h i j) ^ 3 * ε) •
      (internalCoordinates h i - internalCoordinates h j) =
    ((ε ^ 2)⁻¹ * (m j / internalRho h i j ^ 3)) •
      (internalCoordinates h i - internalCoordinates h j)
  congr 1
  field_simp [ne_of_gt hε, hrho]

theorem innerField_eq_fiber_sum {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (i : Label) :
    innerField h i = ∑ j, if blockOf d j = blockOf d i ∧ j ≠ i then
      Reuse.physicalNewtonForce (m j) (internalCoordinates h j)
        (internalCoordinates h i) else 0 := by
  classical
  have hset : (datumBlockLabels d (blockOf d i)).erase i =
      Finset.univ.filter (fun j => blockOf d j = blockOf d i ∧ j ≠ i) := by
    ext j
    simp [datumBlockLabels_eq_fiber, and_comm]
  rw [innerField, internalFieldOn, hset, Finset.sum_filter]

theorem force_eq_sum_all_physicalNewton (m : Masses) (q : Configuration) (i : Label) :
    force m q i = ∑ j, Reuse.physicalNewtonForce (m j) (q j) (q i) := by
  classical
  have hsum := Finset.sum_erase_add Finset.univ
    (fun j => Reuse.physicalNewtonForce (m j) (q j) (q i)) (Finset.mem_univ i)
  have hself : Reuse.physicalNewtonForce (m i) (q i) (q i) = 0 := by
    simp [Reuse.physicalNewtonForce]
  rw [hself, add_zero] at hsum
  rw [Reuse.force_eq_sum_physicalNewtonForce, hsum]

theorem force_physicalCoordinates_decomposition {m : Masses}
    {d : OrderedClusterDatum} {ε : ℝ} (hε : 0 < ε)
    (h : BlowupCoordinates m d) (hsep : InternallySeparated h) (i : Label) :
    force m (physicalCoordinates ε h) i =
      (ε ^ 2)⁻¹ • innerField h i + externalField ε h i := by
  classical
  rw [force_eq_sum_all_physicalNewton, innerField_eq_fiber_sum,
    Finset.smul_sum, externalField, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases heq : j = i
  · subst j
    simp [Reuse.physicalNewtonForce]
  · by_cases hblock : blockOf d j = blockOf d i
    · rw [if_pos ⟨hblock, heq⟩, if_neg (not_not.mpr hblock), add_zero]
      exact physicalNewtonForce_internal_scale hε h hsep i j hblock.symm (Ne.symm heq)
    · simp [hblock]

theorem force_physicalCoordinates_coordinate {m : Masses}
    {d : OrderedClusterDatum} {ε : ℝ} (hε : 0 < ε)
    (h : BlowupCoordinates m d) (hsep : InternallySeparated h)
    (i : Label) (k : Axis) :
    force m (physicalCoordinates ε h) i k =
      (ε ^ 2)⁻¹ * innerField h i k + externalField ε h i k := by
  rw [force_physicalCoordinates_decomposition hε h hsep]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

theorem physicalResidual_x {m : Masses} {d : OrderedClusterDatum}
    {ε : ℝ} (hε : 0 < ε) (h : BlowupCoordinates m d)
    (hsep : InternallySeparated h) (i : Label) :
    residual m (parameterFromEpsilon ε) (physicalCoordinates ε h) i 0 =
      (ε ^ 2)⁻¹ * (innerField h i 0 - outerH h (blockOf d i) - innerU h i) +
        externalField ε h i 0 := by
  simp only [residual, PiLp.sub_apply, anisotropy_x, parameterFromEpsilon,
    force_physicalCoordinates_coordinate hε h hsep, physicalCoordinates,
    Matrix.cons_val_zero]
  field_simp [ne_of_gt hε]
  ring

theorem physicalResidual_y {m : Masses} {d : OrderedClusterDatum}
    {ε : ℝ} (hε : 0 < ε) (h : BlowupCoordinates m d)
    (hsep : InternallySeparated h) (i : Label) :
    residual m (parameterFromEpsilon ε) (physicalCoordinates ε h) i 1 =
      (ε ^ 2)⁻¹ * innerField h i 1 + externalField ε h i 1 -
        outerY h (blockOf d i) - ε * innerV h i := by
  simp [residual, force_physicalCoordinates_coordinate hε h hsep,
    physicalCoordinates]
  ring

theorem physicalResidual_block_mean_x {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {ε : ℝ} (hε : 0 < ε)
    (h : BlowupCoordinates m d) (hsep : InternallySeparated h) (a : BlockIndex d) :
    datumBlockMean m d (residual m (parameterFromEpsilon ε)
      (physicalCoordinates ε h)) a 0 =
      externalMean ε h a 0 - (ε ^ 2)⁻¹ * outerH h a := by
  have hM := datumBlockMass_ne_zero hm d a
  have hc := coordinate_constraints h
  rw [datumBlockMean_apply, externalMean, datumBlockMean_apply]
  have hsum : (∑ i ∈ datumBlockLabels d a, m i *
      residual m (parameterFromEpsilon ε) (physicalCoordinates ε h) i 0) =
      (∑ i ∈ datumBlockLabels d a, m i * externalField ε h i 0) -
        (ε ^ 2)⁻¹ * datumBlockMass m d a * outerH h a := by
    have hexpand : (∑ i ∈ datumBlockLabels d a, m i *
        residual m (parameterFromEpsilon ε) (physicalCoordinates ε h) i 0) =
        ∑ i ∈ datumBlockLabels d a,
          ((ε ^ 2)⁻¹ * (m i * innerField h i 0) -
            ((ε ^ 2)⁻¹ * outerH h a) * m i -
            (ε ^ 2)⁻¹ * (m i * innerU h i) + m i * externalField ε h i 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [physicalResidual_x hε h hsep,
        blockOf_eq_of_mem d (by simpa [datumBlockLabels] using hi)]
      ring
    rw [hexpand]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [innerField_weighted_coordinate_cancel, hc.2.2.1 a]
    unfold datumBlockMass
    ring
  rw [hsum]
  field_simp

theorem physicalResidual_block_mean_y {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {ε : ℝ} (hε : 0 < ε)
    (h : BlowupCoordinates m d) (hsep : InternallySeparated h) (a : BlockIndex d) :
    datumBlockMean m d (residual m (parameterFromEpsilon ε)
      (physicalCoordinates ε h)) a 1 = externalMean ε h a 1 - outerY h a := by
  have hM := datumBlockMass_ne_zero hm d a
  have hc := coordinate_constraints h
  rw [datumBlockMean_apply, externalMean, datumBlockMean_apply]
  have hsum : (∑ i ∈ datumBlockLabels d a, m i *
      residual m (parameterFromEpsilon ε) (physicalCoordinates ε h) i 1) =
      (∑ i ∈ datumBlockLabels d a, m i * externalField ε h i 1) -
        datumBlockMass m d a * outerY h a := by
    have hexpand : (∑ i ∈ datumBlockLabels d a, m i *
        residual m (parameterFromEpsilon ε) (physicalCoordinates ε h) i 1) =
        ∑ i ∈ datumBlockLabels d a,
          ((ε ^ 2)⁻¹ * (m i * innerField h i 1) + m i * externalField ε h i 1 -
            outerY h a * m i - ε * (m i * innerV h i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [physicalResidual_y hε h hsep,
        blockOf_eq_of_mem d (by simpa [datumBlockLabels] using hi)]
      ring
    rw [hexpand]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [innerField_weighted_coordinate_cancel, hc.2.2.2 a]
    unfold datumBlockMass
    ring
  rw [hsum]
  field_simp

theorem blowupResidual_eq_transformed_physical {m : Masses}
    (hm : PositiveMasses m) {d : OrderedClusterDatum} {ε : ℝ} (hε : 0 < ε)
    (h : BlowupCoordinates m d) (hsep : InternallySeparated h) :
    blowupResidual hm ε h = residualT hm d ε
      (restrictedResidual m (parameterFromEpsilon ε) (coordinateQ m d ε h)) := by
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · funext a
      change outerH (blowupResidual hm ε h) a = outerH
        (residualT hm d ε (restrictedResidual m (parameterFromEpsilon ε)
          (coordinateQ m d ε h))) a
      rw [blowupResidual_outerH hm, residualT_outerH hm]
      change ε ^ 2 * externalMean ε h a 0 - outerH h a =
        ε ^ 2 * datumBlockMean m d (residual m (parameterFromEpsilon ε)
          (physicalCoordinates ε h)) a 0
      rw [physicalResidual_block_mean_x hm hε h hsep]
      field_simp [ne_of_gt hε]
    · funext a
      change outerY (blowupResidual hm ε h) a = outerY
        (residualT hm d ε (restrictedResidual m (parameterFromEpsilon ε)
          (coordinateQ m d ε h))) a
      rw [blowupResidual_outerY hm, residualT_outerY hm]
      exact (physicalResidual_block_mean_y hm hε h hsep a).symm
  · apply Prod.ext
    · funext i
      change innerU (blowupResidual hm ε h) i = innerU
        (residualT hm d ε (restrictedResidual m (parameterFromEpsilon ε)
          (coordinateQ m d ε h))) i
      rw [blowupResidual_innerU hm, residualT_innerU hm]
      change innerField h i 0 + ε ^ 2 *
        (externalField ε h i 0 - externalMean ε h (blockOf d i) 0) - innerU h i =
        ε ^ 2 * (residual m (parameterFromEpsilon ε) (physicalCoordinates ε h) i 0 -
          datumBlockMean m d (residual m (parameterFromEpsilon ε)
            (physicalCoordinates ε h)) (blockOf d i) 0)
      rw [physicalResidual_x hε h hsep, physicalResidual_block_mean_x hm hε h hsep]
      field_simp [ne_of_gt hε]
      ring
    · funext i
      change innerV (blowupResidual hm ε h) i = innerV
        (residualT hm d ε (restrictedResidual m (parameterFromEpsilon ε)
          (coordinateQ m d ε h))) i
      rw [blowupResidual_innerV hm, residualT_innerV hm]
      change innerField h i 1 + ε ^ 2 *
        (externalField ε h i 1 - externalMean ε h (blockOf d i) 1) - ε ^ 3 * innerV h i =
        ε ^ 2 * (residual m (parameterFromEpsilon ε) (physicalCoordinates ε h) i 1 -
          datumBlockMean m d (residual m (parameterFromEpsilon ε)
            (physicalCoordinates ε h)) (blockOf d i) 1)
      rw [physicalResidual_y hε h hsep, physicalResidual_block_mean_y hm hε h hsep]
      field_simp [ne_of_gt hε]
      ring

theorem blowupResidual_zero_iff_restrictedResidual_zero {m : Masses}
    (hm : PositiveMasses m) {d : OrderedClusterDatum} {ε : ℝ} (hε : 0 < ε)
    (h : BlowupCoordinates m d) (hsep : InternallySeparated h) :
    blowupResidual hm ε h = 0 ↔
      restrictedResidual m (parameterFromEpsilon ε) (coordinateQ m d ε h) = 0 := by
  rw [blowupResidual_eq_transformed_physical hm hε h hsep]
  let e := residualTEquivalence hm d (ne_of_gt hε)
  change e (restrictedResidual m (parameterFromEpsilon ε) (coordinateQ m d ε h)) = 0 ↔
    restrictedResidual m (parameterFromEpsilon ε) (coordinateQ m d ε h) = 0
  constructor
  · intro hz
    apply e.injective
    simpa only [map_zero] using hz
  · intro hz
    rw [hz]
    exact e.map_zero

end FourBody

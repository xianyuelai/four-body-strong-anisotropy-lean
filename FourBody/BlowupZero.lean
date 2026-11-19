import FourBody.BlowupResidual

/-!
The exact ε=0 formula of v2 eq:zero-residual. The outer vertical field
is the concrete one-dimensional Newton field of the block masses;
internal positions do not occur in this field.
Static preparation; all proof bodies await actual compiler checking.
-/

noncomputable section
open scoped BigOperators
namespace FourBody

theorem internalRho_eq_sqrt {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (i j : Label) :
    internalRho h i j = Real.sqrt
      ((innerU h i - innerU h j) ^ 2 + (innerV h i - innerV h j) ^ 2) := by
  simp [internalRho, internalCoordinates, dist_eq_norm,
    EuclideanSpace.norm_eq, Fin.sum_univ_two]

theorem norm_vertical_point (t : ℝ) : ‖(!₂[0, t] : Point)‖ = |t| := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_sq_eq_abs]

theorem physicalCoordinates_zero {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (i : Label) :
    physicalCoordinates 0 h i = !₂[0, outerY h (blockOf d i)] := by
  simp [physicalCoordinates]

theorem externalField_zero_x {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (i : Label) : externalField 0 h i 0 = 0 := by
  classical
  simp only [externalField, WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  split_ifs
  · simp [Reuse.physicalNewtonForce, physicalCoordinates, PiLp.smul_apply]
  · rfl

theorem externalField_zero_y_expanded {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (i : Label) :
    externalField 0 h i 1 = ∑ j, if blockOf d j ≠ blockOf d i then
      m j * (outerY h (blockOf d i) - outerY h (blockOf d j)) /
        |outerY h (blockOf d i) - outerY h (blockOf d j)| ^ 3 else 0 := by
  classical
  simp only [externalField, WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs
  · rw [Reuse.physicalNewtonForce, dist_eq_norm]
    have hdiff : physicalCoordinates 0 h i - physicalCoordinates 0 h j =
        !₂[0, outerY h (blockOf d i) - outerY h (blockOf d j)] := by
      ext k
      fin_cases k <;> simp [physicalCoordinates]
    rw [hdiff, norm_vertical_point]
    simp only [PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_zero]
    ring
  · rfl

def outerSeedField {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (a : BlockIndex d) : ℝ :=
  oneDimensionalForce (datumBlockMass m d) (outerY h) a

theorem oneDimensionalForce_eq_if_sum {n : ℕ} (μ : Fin n → ℝ)
    (z : Fin n → ℝ) (i : Fin n) :
    oneDimensionalForce μ z i = ∑ j, if j ≠ i then
      μ j * (z i - z j) / |z i - z j| ^ 3 else 0 := by
  classical
  rw [← Finset.sum_filter]
  have hset : Finset.univ.filter (fun j : Fin n => j ≠ i) = Finset.univ.erase i := by
    ext j
    simp
  rw [hset]
  rfl

theorem externalField_zero_y {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (i : Label) :
    externalField 0 h i 1 = outerSeedField h (blockOf d i) := by
  classical
  rw [externalField_zero_y_expanded, outerSeedField, oneDimensionalForce_eq_if_sum]
  calc
    (∑ j, if blockOf d j ≠ blockOf d i then
      m j * (outerY h (blockOf d i) - outerY h (blockOf d j)) /
        |outerY h (blockOf d i) - outerY h (blockOf d j)| ^ 3 else 0) =
      ∑ b, ∑ j ∈ datumBlockLabels d b, if blockOf d j ≠ blockOf d i then
        m j * (outerY h (blockOf d i) - outerY h (blockOf d j)) /
          |outerY h (blockOf d i) - outerY h (blockOf d j)| ^ 3 else 0 :=
      (sum_datumBlocks d _).symm
    _ = ∑ b, if b ≠ blockOf d i then datumBlockMass m d b *
        (outerY h (blockOf d i) - outerY h b) /
          |outerY h (blockOf d i) - outerY h b| ^ 3 else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hbi : b = blockOf d i
      · simp only [hbi, ne_eq, not_true_eq_false, if_false]
        apply Finset.sum_eq_zero
        intro j hj
        rw [blockOf_eq_of_mem d (by simpa [datumBlockLabels] using hj)]
        simp
      · rw [if_pos hbi]
        calc
          _ = ∑ j ∈ datumBlockLabels d b,
              m j * ((outerY h (blockOf d i) - outerY h b) /
                |outerY h (blockOf d i) - outerY h b| ^ 3) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [blockOf_eq_of_mem d (by simpa [datumBlockLabels] using hj), if_pos hbi]
            ring
          _ = _ := by rw [← Finset.sum_mul]; unfold datumBlockMass; ring

theorem datumBlockMean_coordinate_constant {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (q : Configuration) (a : BlockIndex d) (k : Axis)
    (c : ℝ) (hc : ∀ i ∈ datumBlockLabels d a, q i k = c) :
    datumBlockMean m d q a k = c := by
  have hM := datumBlockMass_ne_zero hm d a
  apply (mul_left_cancel₀ hM)
  rw [block_mass_mul_mean hm]
  calc
    _ = ∑ i ∈ datumBlockLabels d a, m i * c :=
      Finset.sum_congr rfl (fun i hi => by rw [hc i hi])
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem externalMean_zero_x {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (h : BlowupCoordinates m d) (a : BlockIndex d) :
    externalMean 0 h a 0 = 0 :=
  datumBlockMean_coordinate_constant hm d (externalField 0 h) a 0 0
    (fun i _ => externalField_zero_x h i)

theorem externalMean_zero_y {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (h : BlowupCoordinates m d) (a : BlockIndex d) :
    externalMean 0 h a 1 = outerSeedField h a := by
  apply datumBlockMean_coordinate_constant hm d (externalField 0 h) a 1
  intro i hi
  rw [externalField_zero_y, blockOf_eq_of_mem d (by simpa [datumBlockLabels] using hi)]

theorem blowupResidual_zero_outerY {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (h : BlowupCoordinates m d) (a : BlockIndex d) :
    outerY (blowupResidual hm 0 h) a = outerSeedField h a - outerY h a := by
  rw [blowupResidual_outerY, externalMean_zero_y hm]

theorem blowupResidual_zero_formula {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (h : BlowupCoordinates m d) :
    (blowupResidual hm 0 h).val =
      ((fun a => -outerH h a, fun a => outerSeedField h a - outerY h a),
       (fun i => innerField h i 0 - innerU h i, fun i => innerField h i 1)) := by
  apply Prod.ext
  · apply Prod.ext
    · funext a
      exact blowupResidual_zero_outerH hm h a
    · funext a
      exact blowupResidual_zero_outerY hm h a
  · apply Prod.ext
    · funext i
      exact blowupResidual_zero_innerU hm h i
    · funext i
      exact blowupResidual_zero_innerV hm h i

end FourBody

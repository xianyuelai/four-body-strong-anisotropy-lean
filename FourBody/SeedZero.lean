import FourBody.SeedConstruction
import FourBody.BlowupZero

/-!
The actual seed is a zero of the actual six-dimensional blow-up residual.
This statically prepared proof uses list-position reindexing of the literal
Newton sums. It must still be compiled; no seed-Jacobian claim is made here.
-/

noncomputable section
open scoped BigOperators
namespace FourBody

theorem norm_horizontal_point (t : ℝ) : ‖(!₂[t, 0] : Point)‖ = |t| := by
  have hs : ‖(!₂[t, 0] : Point)‖ ^ 2 = |t| ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simp [sq_abs]
  exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp hs

theorem internalFieldOn_eq_full_sum (m : Masses) (S : Finset Label)
    (q : Configuration) {i : Label} (hi : i ∈ S) :
    internalFieldOn m S q i = ∑ j ∈ S, Reuse.physicalNewtonForce (m j) (q j) (q i) := by
  have hz : Reuse.physicalNewtonForce (m i) (q i) (q i) = 0 := by
    simp [Reuse.physicalNewtonForce]
  simpa only [internalFieldOn, hz, add_zero] using
    Finset.sum_erase_add S (fun j => Reuse.physicalNewtonForce (m j) (q j) (q i)) hi

theorem oneDimensionalForce_eq_full_sum {n : ℕ} (μ z : Fin n → ℝ) (i : Fin n) :
    oneDimensionalForce μ z i = ∑ j, μ j * (z i - z j) / |z i - z j| ^ 3 := by
  have hz : μ i * (z i - z i) / |z i - z i| ^ 3 = 0 := by simp
  have hsum := Finset.sum_erase_add Finset.univ
    (fun j : Fin n => μ j * (z i - z j) / |z i - z j| ^ 3) (Finset.mem_univ i)
  rw [hz, add_zero] at hsum
  exact hsum

theorem internalPhysicalPair_horizontal {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (hv : ∀ i, innerV h i = 0) (i j : Label) :
    Reuse.physicalNewtonForce (m j) (internalCoordinates h j) (internalCoordinates h i) =
      !₂[m j * (innerU h i - innerU h j) / |innerU h i - innerU h j| ^ 3, 0] := by
  have hd : internalCoordinates h i - internalCoordinates h j =
      !₂[innerU h i - innerU h j, 0] := by
    ext k
    fin_cases k <;> simp [internalCoordinates, hv]
  rw [Reuse.physicalNewtonForce, dist_eq_norm, hd, norm_horizontal_point]
  ext k
  fin_cases k
  · simp [smul_eq_mul]
    ring
  · simp

/-- Genuine finite-subset internal force at a horizontal seed, read in the
prescribed list order, with the same masses and same normalization. -/
theorem innerField_seed_formula {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (hv : ∀ i, innerV h i = 0)
    (a : BlockIndex d) (i : InternalIndex d a) :
    innerField h (internalLabel d a i) =
      !₂[oneDimensionalForce (fun j => m (internalLabel d a j))
        (fun j => innerU h (internalLabel d a j)) i, 0] := by
  have hi := internalLabel_mem d a i
  have hif : internalLabel d a i ∈ datumBlockLabels d a := by
    simpa only [datumBlockLabels, List.mem_toFinset] using hi
  rw [innerField, blockOf_eq_of_mem d hi,
    internalFieldOn_eq_full_sum m _ _ hif, ← sum_internalLabels]
  ext k
  fin_cases k
  · rw [show oneDimensionalForce (fun j => m (internalLabel d a j))
        (fun j => innerU h (internalLabel d a j)) i = _ from
      oneDimensionalForce_eq_full_sum _ _ i]
    simp only [WithLp.ofLp_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [internalPhysicalPair_horizontal h hv]
    rfl
  · simp only [WithLp.ofLp_sum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    rw [internalPhysicalPair_horizontal h hv]
    rfl

theorem isSeed_innerField {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (hh : IsSeed m d h) (i : Label) :
    innerField h i = !₂[innerU h i, 0] := by
  let a := blockOf d i
  obtain ⟨j, hj⟩ := internalLabel_surjective d a (label_mem_blockOf d i)
  rw [← hj, innerField_seed_formula h hh.2.1 a j]
  rw [(hh.2.2.2.2 a).2.2.2 j]

theorem isSeed_blowupResidual_zero {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (h : BlowupCoordinates m d) (hh : IsSeed m d h) :
    blowupResidual hm 0 h = 0 := by
  apply Subtype.ext
  rw [blowupResidual_zero_formula hm]
  apply Prod.ext
  · apply Prod.ext
    · funext a
      simp [hh.1 a]
    · funext a
      change outerSeedField h a - outerY h a = 0
      rw [outerSeedField, hh.2.2.2.1.2.2 a, sub_self]
  · apply Prod.ext
    · funext i
      simp [isSeed_innerField h hh i]
    · funext i
      simp [isSeed_innerField h hh i]

theorem seedCoordinates_blowupResidual_zero {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) : blowupResidual hm 0 (seedCoordinates hm d) = 0 :=
  isSeed_blowupResidual_zero hm _ (seedCoordinates_isSeed hm d)

end FourBody

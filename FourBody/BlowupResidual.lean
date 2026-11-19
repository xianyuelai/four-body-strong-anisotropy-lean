import FourBody.BlowupFields
import FourBody.ResidualTransform

/-!
Literal v2 residual eq:outer-residual and eq:inner-residual, and its
membership in the actual six-dimensional constrained space.
Frozen TeX SHA256 97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
Static preparation: these proof bodies have not yet been compiled.
-/

noncomputable section
open scoped BigOperators
namespace FourBody

def blowupResidualAmbient {m : Masses} {d : OrderedClusterDatum} (ε : ℝ)
    (h : BlowupCoordinates m d) : CoordinateAmbient d :=
  ((fun a => ε ^ 2 * externalMean ε h a 0 - outerH h a,
    fun a => externalMean ε h a 1 - outerY h a),
   (fun i => innerField h i 0 +
      ε ^ 2 * (externalField ε h i 0 - externalMean ε h (blockOf d i) 0) - innerU h i,
    fun i => innerField h i 1 +
      ε ^ 2 * (externalField ε h i 1 - externalMean ε h (blockOf d i) 1) -
        ε ^ 3 * innerV h i))

theorem blowupResidualAmbient_mem {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (ε : ℝ) (h : BlowupCoordinates m d) :
    blowupResidualAmbient ε h ∈ coordinateSpace m d := by
  apply (mem_coordinateSpace_iff m d _).mpr
  have hc := coordinate_constraints h
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (∑ a, datumBlockMass m d a *
      (ε ^ 2 * externalMean ε h a 0 - outerH h a)) = 0
    calc
      _ = ε ^ 2 * (∑ a, datumBlockMass m d a * externalMean ε h a 0) -
          (∑ a, datumBlockMass m d a * outerH h a) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = 0 := by rw [externalMean_total_cancel hm, hc.1]; ring
  · change (∑ a, datumBlockMass m d a *
      (externalMean ε h a 1 - outerY h a)) = 0
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, externalMean_total_cancel hm, hc.2.1, sub_self]
  · intro a
    change (∑ i ∈ datumBlockLabels d a, m i *
      (innerField h i 0 + ε ^ 2 *
        (externalField ε h i 0 - externalMean ε h (blockOf d i) 0) - innerU h i)) = 0
    calc
      _ = (∑ i ∈ datumBlockLabels d a, m i * innerField h i 0) +
          ε ^ 2 * (∑ i ∈ datumBlockLabels d a,
            m i * (externalField ε h i 0 - externalMean ε h (blockOf d i) 0)) -
          (∑ i ∈ datumBlockLabels d a, m i * innerU h i) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [innerField_weighted_coordinate_cancel,
        external_deviation_cancel hm, hc.2.2.1 a]; ring
  · intro a
    change (∑ i ∈ datumBlockLabels d a, m i *
      (innerField h i 1 + ε ^ 2 *
        (externalField ε h i 1 - externalMean ε h (blockOf d i) 1) -
          ε ^ 3 * innerV h i)) = 0
    calc
      _ = (∑ i ∈ datumBlockLabels d a, m i * innerField h i 1) +
          ε ^ 2 * (∑ i ∈ datumBlockLabels d a,
            m i * (externalField ε h i 1 - externalMean ε h (blockOf d i) 1)) -
          ε ^ 3 * (∑ i ∈ datumBlockLabels d a, m i * innerV h i) := by
        rw [Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [innerField_weighted_coordinate_cancel,
        external_deviation_cancel hm, hc.2.2.2 a]; ring

def blowupResidual {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (ε : ℝ) (h : BlowupCoordinates m d) :
    BlowupCoordinates m d :=
  ⟨blowupResidualAmbient ε h, blowupResidualAmbient_mem hm ε h⟩

theorem blowupResidual_outerH {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (ε : ℝ) (h : BlowupCoordinates m d) (a : BlockIndex d) :
    outerH (blowupResidual hm ε h) a = ε ^ 2 * externalMean ε h a 0 - outerH h a := rfl

theorem blowupResidual_outerY {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (ε : ℝ) (h : BlowupCoordinates m d) (a : BlockIndex d) :
    outerY (blowupResidual hm ε h) a = externalMean ε h a 1 - outerY h a := rfl

theorem blowupResidual_innerU {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (ε : ℝ) (h : BlowupCoordinates m d) (i : Label) :
    innerU (blowupResidual hm ε h) i = innerField h i 0 +
      ε ^ 2 * (externalField ε h i 0 - externalMean ε h (blockOf d i) 0) - innerU h i := rfl

theorem blowupResidual_innerV {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (ε : ℝ) (h : BlowupCoordinates m d) (i : Label) :
    innerV (blowupResidual hm ε h) i = innerField h i 1 +
      ε ^ 2 * (externalField ε h i 1 - externalMean ε h (blockOf d i) 1) -
        ε ^ 3 * innerV h i := rfl

theorem blowupResidual_zero_outerH {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (h : BlowupCoordinates m d) (a : BlockIndex d) :
    outerH (blowupResidual hm 0 h) a = -outerH h a := by
  simp [blowupResidual_outerH]

theorem blowupResidual_zero_innerU {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (h : BlowupCoordinates m d) (i : Label) :
    innerU (blowupResidual hm 0 h) i = innerField h i 0 - innerU h i := by
  simp [blowupResidual_innerU]

theorem blowupResidual_zero_innerV {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (h : BlowupCoordinates m d) (i : Label) :
    innerV (blowupResidual hm 0 h) i = innerField h i 1 := by
  simp [blowupResidual_innerV]

end FourBody

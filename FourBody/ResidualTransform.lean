import FourBody.CoordinateEquivalence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
The actual Tε of v2 eq:residual-transform, distinct from the inverse of Qε.
In particular its physical vertical inverse is η_a+ε⁻²θ_i.
Frozen v2 SHA256 97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
Static preparation; no compilation or axiom audit is claimed yet.
-/

noncomputable section
open scoped BigOperators
namespace FourBody

def componentScale (m : Masses) (d : OrderedClusterDatum) (α β γ δ : ℝ) :
    BlowupCoordinates m d →ₗ[ℝ] BlowupCoordinates m d where
  toFun h := ⟨((fun a => α * outerH h a, fun a => β * outerY h a),
    (fun i => γ * innerU h i, fun i => δ * innerV h i)), by
      apply (mem_coordinateSpace_iff m d _).mpr
      have hc := coordinate_constraints h
      refine ⟨?_, ?_, ?_, ?_⟩
      · change (∑ a, datumBlockMass m d a * (α * outerH h a)) = 0
        simp_rw [show ∀ a, datumBlockMass m d a * (α * outerH h a) =
          α * (datumBlockMass m d a * outerH h a) from fun a => by ring]
        rw [← Finset.mul_sum, hc.1, mul_zero]
      · change (∑ a, datumBlockMass m d a * (β * outerY h a)) = 0
        simp_rw [show ∀ a, datumBlockMass m d a * (β * outerY h a) =
          β * (datumBlockMass m d a * outerY h a) from fun a => by ring]
        rw [← Finset.mul_sum, hc.2.1, mul_zero]
      · intro a
        change (∑ i ∈ datumBlockLabels d a, m i * (γ * innerU h i)) = 0
        simp_rw [show ∀ i, m i * (γ * innerU h i) =
          γ * (m i * innerU h i) from fun i => by ring]
        rw [← Finset.mul_sum, hc.2.2.1 a, mul_zero]
      · intro a
        change (∑ i ∈ datumBlockLabels d a, m i * (δ * innerV h i)) = 0
        simp_rw [show ∀ i, m i * (δ * innerV h i) =
          δ * (m i * innerV h i) from fun i => by ring]
        rw [← Finset.mul_sum, hc.2.2.2 a, mul_zero]⟩
  map_add' h g := by
    apply Subtype.ext
    apply Prod.ext <;> apply Prod.ext <;> funext i <;>
      simp [outerH, outerY, innerU, innerV, mul_add]
  map_smul' c h := by
    apply Subtype.ext
    apply Prod.ext <;> apply Prod.ext <;> funext i <;>
      simp [outerH, outerY, innerU, innerV, smul_eq_mul, mul_left_comm]

def componentScaleEquivalence (m : Masses) (d : OrderedClusterDatum)
    {α β γ δ : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hδ : δ ≠ 0) :
    BlowupCoordinates m d ≃ₗ[ℝ] BlowupCoordinates m d where
  toFun := componentScale m d α β γ δ
  invFun := componentScale m d α⁻¹ β⁻¹ γ⁻¹ δ⁻¹
  left_inv h := by
    apply Subtype.ext
    apply Prod.ext <;> apply Prod.ext <;> funext i <;>
      simp [componentScale, outerH, outerY, innerU, innerV,
        hα, hβ, hγ, hδ]
  right_inv h := by
    apply Subtype.ext
    apply Prod.ext <;> apply Prod.ext <;> funext i <;>
      simp [componentScale, outerH, outerY, innerU, innerV,
        hα, hβ, hγ, hδ]
  map_add' := (componentScale m d α β γ δ).map_add
  map_smul' := (componentScale m d α β γ δ).map_smul

/-- The displayed finite mass-mean transform, defined also at ε=0. -/
def residualT {m : Masses} (hm : PositiveMasses m) (d : OrderedClusterDatum)
    (ε : ℝ) : W m →ₗ[ℝ] BlowupCoordinates m d :=
  (componentScale m d (ε ^ 2) 1 (ε ^ 2) (ε ^ 2)).comp
    (coordinateEquivalence hm d (ε := 1) one_ne_zero).symm.toLinearMap

theorem residualT_outerH {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (ε : ℝ) (b : W m) (a : BlockIndex d) :
    outerH (residualT hm d ε b) a = ε ^ 2 * datumBlockMean m d b.val a 0 := by
  simp [residualT, componentScale, coordinateEquivalence, meanInverse,
    meanInverseAmbient, outerH]

theorem residualT_outerY {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (ε : ℝ) (b : W m) (a : BlockIndex d) :
    outerY (residualT hm d ε b) a = datumBlockMean m d b.val a 1 := by
  simp [residualT, componentScale, coordinateEquivalence, meanInverse,
    meanInverseAmbient, outerY]

theorem residualT_innerU {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (ε : ℝ) (b : W m) (i : Label) :
    innerU (residualT hm d ε b) i =
      ε ^ 2 * (b.val i 0 - datumBlockMean m d b.val (blockOf d i) 0) := by
  simp [residualT, componentScale, coordinateEquivalence, meanInverse,
    meanInverseAmbient, innerU]

theorem residualT_innerV {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (ε : ℝ) (b : W m) (i : Label) :
    innerV (residualT hm d ε b) i =
      ε ^ 2 * (b.val i 1 - datumBlockMean m d b.val (blockOf d i) 1) := by
  simp [residualT, componentScale, coordinateEquivalence, meanInverse,
    meanInverseAmbient, innerV]

def residualTEquivalence {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) {ε : ℝ} (hε : ε ≠ 0) :
    W m ≃ₗ[ℝ] BlowupCoordinates m d :=
  (coordinateEquivalence hm d (ε := 1) one_ne_zero).symm.trans
    (componentScaleEquivalence m d (pow_ne_zero 2 hε) one_ne_zero
      (pow_ne_zero 2 hε) (pow_ne_zero 2 hε))

theorem residualTEquivalence_toLinearMap {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) {ε : ℝ} (hε : ε ≠ 0) :
    (residualTEquivalence hm d hε).toLinearMap = residualT hm d ε := rfl

/-- The vertical term is Y+ε⁻²v; it is not ε⁻²(Y+v). -/
theorem residualTEquivalence_inverse_apply {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) {ε : ℝ} (hε : ε ≠ 0)
    (h : BlowupCoordinates m d) (i : Label) :
    ((residualTEquivalence hm d hε).symm h).val i =
      !₂[(ε ^ 2)⁻¹ * (outerH h (blockOf d i) + innerU h i),
        outerY h (blockOf d i) + (ε ^ 2)⁻¹ * innerV h i] := by
  ext k
  fin_cases k <;>
    simp [residualTEquivalence, componentScaleEquivalence, componentScale,
      coordinateEquivalence, coordinateQ, physicalCoordinates,
      outerH, outerY, innerU, innerV, mul_add]

def residualTContinuousEquivalence {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) {ε : ℝ} (hε : ε ≠ 0) :
    W m ≃L[ℝ] BlowupCoordinates m d :=
  (residualTEquivalence hm d hε).toContinuousLinearEquiv

end FourBody

import FourBody.SeedConstruction
import FourBody.Operators
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The actual constrained coordinate kernel is linearly and continuously
equivalent to the two outer scalar center spaces times the two ordered scalar
center spaces in each actual block. The inverse patches actual list positions
back to their labels. No seed existence theorem is used by these proofs.
Static candidate only; compilation and full-type audit remain pending. -/

noncomputable section
open scoped BigOperators
namespace FourBody.CoordinateProduct

def internalMass (m : Masses) (d : OrderedClusterDatum) (a : BlockIndex d)
    (i : InternalIndex d a) : ℝ := m (internalLabel d a i)

abbrev OuterSpace (m : Masses) (d : OrderedClusterDatum) :=
  ScalarGeometry.ScalarW (datumBlockMass m d)

abbrev InnerSpace (m : Masses) (d : OrderedClusterDatum) (a : BlockIndex d) :=
  ScalarGeometry.ScalarW (internalMass m d a)

abbrev ProductSpace (m : Masses) (d : OrderedClusterDatum) :=
  (OuterSpace m d × OuterSpace m d) ×
    (∀ a : BlockIndex d, InnerSpace m d a × InnerSpace m d a)

def outerHCentered {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) : OuterSpace m d :=
  ⟨outerH h, (coordinate_constraints h).1⟩

def outerYCentered {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) : OuterSpace m d :=
  ⟨outerY h, (coordinate_constraints h).2.1⟩

def innerUCentered {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (a : BlockIndex d) : InnerSpace m d a :=
  ⟨fun i => innerU h (internalLabel d a i), by
    change (∑ i : InternalIndex d a,
      m (internalLabel d a i) * innerU h (internalLabel d a i)) = 0
    rw [sum_internalLabels d a (fun i => m i * innerU h i)]
    exact (coordinate_constraints h).2.2.1 a⟩

def innerVCentered {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (a : BlockIndex d) : InnerSpace m d a :=
  ⟨fun i => innerV h (internalLabel d a i), by
    change (∑ i : InternalIndex d a,
      m (internalLabel d a i) * innerV h (internalLabel d a i)) = 0
    rw [sum_internalLabels d a (fun i => m i * innerV h i)]
    exact (coordinate_constraints h).2.2.2 a⟩

def extractLM (m : Masses) (d : OrderedClusterDatum) :
    BlowupCoordinates m d →ₗ[ℝ] ProductSpace m d where
  toFun h := ((outerHCentered h, outerYCentered h),
    fun a => (innerUCentered h a, innerVCentered h a))
  map_add' h g := by
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext; funext a; rfl
      · apply Subtype.ext; funext a; rfl
    · funext a
      apply Prod.ext
      · apply Subtype.ext; funext i; rfl
      · apply Subtype.ext; funext i; rfl
  map_smul' c h := by
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext; funext a; rfl
      · apply Subtype.ext; funext a; rfl
    · funext a
      apply Prod.ext
      · apply Subtype.ext; funext i; rfl
      · apply Subtype.ext; funext i; rfl

def assemble {m : Masses} {d : OrderedClusterDatum}
    (p : ProductSpace m d) : BlowupCoordinates m d :=
  ⟨((p.1.1.val, p.1.2.val),
    (assembleInternal d (fun a => (p.2 a).1.val),
     assembleInternal d (fun a => (p.2 a).2.val))), by
    apply (mem_coordinateSpace_iff m d _).mpr
    refine ⟨p.1.1.property, p.1.2.property, ?_, ?_⟩
    · intro a
      apply assembleInternal_weighted_center
      intro b
      exact (p.2 b).1.property
    · intro a
      apply assembleInternal_weighted_center
      intro b
      exact (p.2 b).2.property⟩

theorem assembleInternal_restrict (d : OrderedClusterDatum) (u : Label → ℝ) :
    assembleInternal d (fun a i => u (internalLabel d a i)) = u := by
  funext i
  obtain ⟨j, hj⟩ := internalLabel_surjective d (blockOf d i) (label_mem_blockOf d i)
  rw [← hj, assembleInternal_apply]

theorem assemble_extract (m : Masses) (d : OrderedClusterDatum)
    (h : BlowupCoordinates m d) : assemble (extractLM m d h) = h := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact assembleInternal_restrict d (innerU h)
    · exact assembleInternal_restrict d (innerV h)

theorem extract_assemble (m : Masses) (d : OrderedClusterDatum)
    (p : ProductSpace m d) : extractLM m d (assemble p) = p := by
  apply Prod.ext
  · apply Prod.ext <;> apply Subtype.ext <;> rfl
  · funext a
    apply Prod.ext
    · apply Subtype.ext
      funext i
      exact assembleInternal_apply d (fun b => (p.2 b).1.val) a i
    · apply Subtype.ext
      funext i
      exact assembleInternal_apply d (fun b => (p.2 b).2.val) a i

def equivalenceLM (m : Masses) (d : OrderedClusterDatum) :
    BlowupCoordinates m d ≃ₗ[ℝ] ProductSpace m d where
  toFun := extractLM m d
  invFun := assemble
  left_inv := assemble_extract m d
  right_inv := extract_assemble m d
  map_add' := (extractLM m d).map_add
  map_smul' := (extractLM m d).map_smul

def equivalence (m : Masses) (d : OrderedClusterDatum) :
    BlowupCoordinates m d ≃L[ℝ] ProductSpace m d :=
  (equivalenceLM m d).toContinuousLinearEquiv

@[simp] theorem equivalence_outerH (m : Masses) (d : OrderedClusterDatum)
    (h : BlowupCoordinates m d) (a : BlockIndex d) :
    (equivalence m d h).1.1.val a = outerH h a := rfl

@[simp] theorem equivalence_outerY (m : Masses) (d : OrderedClusterDatum)
    (h : BlowupCoordinates m d) (a : BlockIndex d) :
    (equivalence m d h).1.2.val a = outerY h a := rfl

@[simp] theorem equivalence_innerU (m : Masses) (d : OrderedClusterDatum)
    (h : BlowupCoordinates m d) (a : BlockIndex d) (i : InternalIndex d a) :
    ((equivalence m d h).2 a).1.val i = innerU h (internalLabel d a i) := rfl

@[simp] theorem equivalence_innerV (m : Masses) (d : OrderedClusterDatum)
    (h : BlowupCoordinates m d) (a : BlockIndex d) (i : InternalIndex d a) :
    ((equivalence m d h).2 a).2.val i = innerV h (internalLabel d a i) := rfl

theorem seed_outerH_zero {m : Masses} {d : OrderedClusterDatum}
    {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) :
    (equivalence m d seed).1.1 = 0 := by
  apply Subtype.ext
  funext a
  exact hs.1 a

theorem seed_innerV_zero {m : Masses} {d : OrderedClusterDatum}
    {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) (a : BlockIndex d) :
    ((equivalence m d seed).2 a).2 = 0 := by
  apply Subtype.ext
  funext i
  exact hs.2.1 (internalLabel d a i)

theorem seed_outerY_chamber {m : Masses} {d : OrderedClusterDatum}
    {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) :
    (equivalence m d seed).1.2 ∈ ScalarGeometry.chamber (datumBlockMass m d) :=
  hs.2.2.1

theorem seed_innerU_chamber {m : Masses} {d : OrderedClusterDatum}
    {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) (a : BlockIndex d) :
    ((equivalence m d seed).2 a).1 ∈ ScalarGeometry.chamber (internalMass m d a) :=
  (hs.2.2.2.2 a).1

theorem internalMass_pos {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (a : BlockIndex d) : ∀ i, 0 < internalMass m d a i :=
  fun i => hm (internalLabel d a i)

end FourBody.CoordinateProduct

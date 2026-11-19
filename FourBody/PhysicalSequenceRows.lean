import FourBody.NewtonFieldLimits
import FourBody.BlowupPhysicalBridge

/-!
# The exact original equations in the selected mass-mean coordinates

Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
These rows are derived from actual IsSolution and the actual coordinate
relation. The relation is existentially constructed by the proved mean
inverse bridge in VerticalPartition; no seed, branch or scaled-equation
certificate is assumed. BlowupPhysicalBridge is an uncompiled dependency
candidate, and all bodies here are also uncompiled.
-/

noncomputable section
open scoped BigOperators

namespace FourBody.PhysicalSequenceRows

theorem internallySeparated_of_original_solution {m : Masses}
    {d : OrderedClusterDatum} {ε s : ℝ} {h : BlowupCoordinates m d} {q : Configuration}
    (hq : IsSolution m s q) (hh : CoordinatesOfConfiguration m d ε q h) :
    InternallySeparated h := by
  intro i j hblock hij hsame
  have heq := (represents_iff_eq_physicalCoordinates ε h q).mp hh.1
  have hdiff : physicalCoordinates ε h i - physicalCoordinates ε h j = 0 := by
    rw [physicalCoordinates_difference_sameBlock ε h i j hblock, hsame, sub_self, smul_zero]
  exact hq.1 i j hij (by rw [heq]; exact sub_eq_zero.mp hdiff)

theorem solution_blowupResidual_zero {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {s : ℝ} (hs : 0 < s)
    {h : BlowupCoordinates m d} {q : Configuration}
    (hq : IsSolution m s q) (hh : CoordinatesOfConfiguration m d (epsilon s) q h) :
    blowupResidual hm (epsilon s) h = 0 := by
  have heq := (represents_iff_eq_physicalCoordinates (epsilon s) h q).mp hh.1
  apply (blowupResidual_zero_iff_restrictedResidual_zero hm (SequenceStart.epsilon_pos hs)
    h (internallySeparated_of_original_solution hq hh)).mpr
  apply Subtype.ext
  change residual m (parameterFromEpsilon (epsilon s))
    (physicalCoordinates (epsilon s) h) = 0
  rw [SequenceStart.parameterFromEpsilon_epsilon hs, ← heq]
  funext i
  exact sub_eq_zero.mpr (hq.2 i)

theorem internalCoordinates_eq_actual_vectors {m : Masses}
    {d : OrderedClusterDatum} {ε : ℝ} {h : BlowupCoordinates m d} {q : Configuration}
    (hh : CoordinatesOfConfiguration m d ε q h) :
    internalCoordinates h = InternalCoordinates.internalVectors m d ε q := by
  funext i
  exact hh.2.2.2 (blockOf d i) i (label_mem_blockOf d i)

theorem externalField_eq_actual_field {m : Masses}
    {d : OrderedClusterDatum} {ε : ℝ} {h : BlowupCoordinates m d} {q : Configuration}
    (hh : CoordinatesOfConfiguration m d ε q h) :
    externalField ε h = NewtonFieldLimits.physicalExternalField m d q := by
  have heq := (represents_iff_eq_physicalCoordinates ε h q).mp hh.1
  rw [heq]
  rfl

theorem externalMean_eq_actual_mean {m : Masses}
    {d : OrderedClusterDatum} {ε : ℝ} {h : BlowupCoordinates m d} {q : Configuration}
    (hh : CoordinatesOfConfiguration m d ε q h) (a : BlockIndex d) :
    externalMean ε h a = NewtonFieldLimits.physicalExternalMean m d q a := by
  rw [externalMean, externalField_eq_actual_field hh]
  rfl

theorem innerField_eq_actual_field {m : Masses}
    {d : OrderedClusterDatum} {ε : ℝ} {h : BlowupCoordinates m d} {q : Configuration}
    (hh : CoordinatesOfConfiguration m d ε q h) (i : Label) :
    innerField h i = NewtonFieldLimits.physicalInternalField m d
      (InternalCoordinates.internalVectors m d ε q) i := by
  rw [innerField, internalFieldOn, internalCoordinates_eq_actual_vectors hh]
  rfl

/-- The exact horizontal block mean equation H=ε² Emean_x. -/
theorem horizontal_mean_row {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {s : ℝ} (hs : 0 < s)
    {h : BlowupCoordinates m d} {q : Configuration}
    (hq : IsSolution m s q) (hh : CoordinatesOfConfiguration m d (epsilon s) q h)
    (a : BlockIndex d) :
    outerH h a = (epsilon s) ^ 2 *
      NewtonFieldLimits.physicalExternalMean m d q a 0 := by
  have hr := congrArg (fun z : BlowupCoordinates m d => outerH z a)
    (solution_blowupResidual_zero hm hs hq hh)
  rw [blowupResidual_outerH, externalMean_eq_actual_mean hh] at hr
  change (epsilon s) ^ 2 * NewtonFieldLimits.physicalExternalMean m d q a 0 -
    outerH h a = 0 at hr
  linarith

/-- The exact vertical block mean equation Y=Emean_y. -/
theorem vertical_mean_row {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {s : ℝ} (hs : 0 < s)
    {h : BlowupCoordinates m d} {q : Configuration}
    (hq : IsSolution m s q) (hh : CoordinatesOfConfiguration m d (epsilon s) q h)
    (a : BlockIndex d) :
    outerY h a = NewtonFieldLimits.physicalExternalMean m d q a 1 := by
  have hr := congrArg (fun z : BlowupCoordinates m d => outerY z a)
    (solution_blowupResidual_zero hm hs hq hh)
  rw [blowupResidual_outerY, externalMean_eq_actual_mean hh] at hr
  change NewtonFieldLimits.physicalExternalMean m d q a 1 - outerY h a = 0 at hr
  linarith

/-- Literal internal scaled x equation, with the actual P_x on the right. -/
theorem internal_horizontal_row {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {s : ℝ} (hs : 0 < s)
    {h : BlowupCoordinates m d} {q : Configuration}
    (hq : IsSolution m s q) (hh : CoordinatesOfConfiguration m d (epsilon s) q h)
    (i : Label) :
    NewtonFieldLimits.physicalInternalField m d
      (InternalCoordinates.internalVectors m d (epsilon s) q) i 0 +
      (epsilon s) ^ 2 * (NewtonFieldLimits.physicalExternalField m d q i 0 -
        NewtonFieldLimits.physicalExternalMean m d q (blockOf d i) 0) =
      InternalCoordinates.internalVectors m d (epsilon s) q i 0 := by
  have hr := congrArg (fun z : BlowupCoordinates m d => innerU z i)
    (solution_blowupResidual_zero hm hs hq hh)
  rw [blowupResidual_innerU, innerField_eq_actual_field hh,
    externalField_eq_actual_field hh, externalMean_eq_actual_mean hh] at hr
  have hp := congrArg (fun p : Configuration => p i 0) (internalCoordinates_eq_actual_vectors hh)
  change innerU h i = InternalCoordinates.internalVectors m d (epsilon s) q i 0 at hp
  change NewtonFieldLimits.physicalInternalField m d
      (InternalCoordinates.internalVectors m d (epsilon s) q) i 0 +
      (epsilon s) ^ 2 * (NewtonFieldLimits.physicalExternalField m d q i 0 -
        NewtonFieldLimits.physicalExternalMean m d q (blockOf d i) 0) - innerU h i = 0 at hr
  rw [hp] at hr
  linarith

/-- Literal internal scaled y equation, with ε³ P_y on the right. -/
theorem internal_vertical_row {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {s : ℝ} (hs : 0 < s)
    {h : BlowupCoordinates m d} {q : Configuration}
    (hq : IsSolution m s q) (hh : CoordinatesOfConfiguration m d (epsilon s) q h)
    (i : Label) :
    NewtonFieldLimits.physicalInternalField m d
      (InternalCoordinates.internalVectors m d (epsilon s) q) i 1 +
      (epsilon s) ^ 2 * (NewtonFieldLimits.physicalExternalField m d q i 1 -
        NewtonFieldLimits.physicalExternalMean m d q (blockOf d i) 1) =
      (epsilon s) ^ 3 * InternalCoordinates.internalVectors m d (epsilon s) q i 1 := by
  have hr := congrArg (fun z : BlowupCoordinates m d => innerV z i)
    (solution_blowupResidual_zero hm hs hq hh)
  rw [blowupResidual_innerV, innerField_eq_actual_field hh,
    externalField_eq_actual_field hh, externalMean_eq_actual_mean hh] at hr
  have hp := congrArg (fun p : Configuration => p i 1) (internalCoordinates_eq_actual_vectors hh)
  change innerV h i = InternalCoordinates.internalVectors m d (epsilon s) q i 1 at hp
  change NewtonFieldLimits.physicalInternalField m d
      (InternalCoordinates.internalVectors m d (epsilon s) q) i 1 +
      (epsilon s) ^ 2 * (NewtonFieldLimits.physicalExternalField m d q i 1 -
        NewtonFieldLimits.physicalExternalMean m d q (blockOf d i) 1) -
      (epsilon s) ^ 3 * innerV h i = 0 at hr
  rw [hp] at hr
  linarith

end FourBody.PhysicalSequenceRows


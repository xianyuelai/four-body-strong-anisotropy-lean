import FourBody.SeedConstruction
import Mathlib.Data.Finset.Max

/-!
The actual common positive outer seed gap in v2 lines 677--679.
The finite set is proved nonempty using the already proved four-block
datum count. This is a static candidate, not yet compiler-verified.
All seeds are the concrete ones constructed by actual scalar minimization.
-/

noncomputable section
set_option maxRecDepth 4096
open scoped BigOperators
namespace FourBody

def seedOuterGaps {m : Masses} (hm : PositiveMasses m) : Finset ℝ := by
  classical
  exact Finset.univ.biUnion fun d : OrderedClusterDatum =>
    ((Finset.univ : Finset (BlockIndex d × BlockIndex d)).filter (fun p => p.1 < p.2)).image
      (fun p => outerY (seedCoordinates hm d) p.2 - outerY (seedCoordinates hm d) p.1)

theorem seedOuterGap_mem {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (a b : BlockIndex d) (hab : a < b) :
    outerY (seedCoordinates hm d) b - outerY (seedCoordinates hm d) a ∈ seedOuterGaps hm := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨d, Finset.mem_univ d, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩, rfl⟩

theorem seedOuterGaps_positive {m : Masses} (hm : PositiveMasses m)
    {t : ℝ} (ht : t ∈ seedOuterGaps hm) : 0 < t := by
  classical
  obtain ⟨d, _, htd⟩ := Finset.mem_biUnion.mp ht
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp htd
  exact sub_pos.mpr ((seedCoordinates_isSeed hm d).2.2.1 (Finset.mem_filter.mp hp).2)

theorem seedOuterGaps_nonempty {m : Masses} (hm : PositiveMasses m) :
    (seedOuterGaps hm).Nonempty := by
  have hcard : 0 < Fintype.card {d : OrderedClusterDatum // d.blockCount = 4} := by
    rw [card_fourBlockData]
    decide
  obtain ⟨d⟩ := Fintype.card_pos_iff.mp hcard
  have hd : d.val.blocks.length = 4 := d.property
  let a : BlockIndex d.val := ⟨0, by rw [hd]; decide⟩
  let b : BlockIndex d.val := ⟨1, by rw [hd]; decide⟩
  have hab : a < b := by change (0 : ℕ) < 1; decide
  exact ⟨_, seedOuterGap_mem hm d.val a b hab⟩

def commonSeedGap {m : Masses} (hm : PositiveMasses m) : ℝ :=
  (seedOuterGaps hm).min' (seedOuterGaps_nonempty hm)

theorem commonSeedGap_positive {m : Masses} (hm : PositiveMasses m) :
    0 < commonSeedGap hm :=
  seedOuterGaps_positive hm (Finset.min'_mem _ _)

theorem commonSeedGap_le {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (a b : BlockIndex d) (hab : a < b) :
    commonSeedGap hm ≤ outerY (seedCoordinates hm d) b - outerY (seedCoordinates hm d) a :=
  Finset.min'_le _ _ (seedOuterGap_mem hm d a b hab)

/-- The mass-dependent minimum is an attained actual positive outer gap. -/
theorem commonSeedGap_attained {m : Masses} (hm : PositiveMasses m) :
    ∃ d : OrderedClusterDatum, ∃ a b : BlockIndex d,
      a < b ∧ commonSeedGap hm =
        outerY (seedCoordinates hm d) b - outerY (seedCoordinates hm d) a := by
  classical
  have hmem : commonSeedGap hm ∈ seedOuterGaps hm := Finset.min'_mem _ _
  obtain ⟨d, _, hd⟩ := Finset.mem_biUnion.mp hmem
  obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hd
  exact ⟨d, p.1, p.2, (Finset.mem_filter.mp hp).2, heq.symm⟩

end FourBody

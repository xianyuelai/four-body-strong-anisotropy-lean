import FourBody.CoordinateEquivalence
import FourBody.Reuse.NewtonBounds
import FourBody.NewtonFieldLimits
import FourBody.VerticalPairing

/-!
# The actual finite block indices for the limit-force pairing

Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
The first five elementary proof bodies adapt the actual list-label
equivalence and full-sum reindexing from seed-prep/SeedConstruction.lean,
SHA256 509673093FFB69F026284DF27541F812DA2BA7E96C1D5F07C444E325FA560F67.
That candidate has not been compiled; this file does not import it, depend
on a scalar minimizer or assume any seed conclusion. Its underlying
blockLabelsEquiv is from the checked literal ClusterData representation.
The erased sum and scalar Newton row bridges are proved explicitly here.
All new proof bodies remain uncompiled.
-/

noncomputable section
open scoped BigOperators

namespace FourBody.SequenceBlockIndices

def labelsEquivalence (d : OrderedClusterDatum) (a : BlockIndex d) :
    InternalIndex d a ≃ {i : Label // i ∈ datumBlock d a} :=
  d.blockLabelsEquiv (datumBlock d a) (List.get_mem d.blocks a)

theorem internalLabel_mem (d : OrderedClusterDatum) (a : BlockIndex d)
    (j : InternalIndex d a) : internalLabel d a j ∈ datumBlock d a :=
  (labelsEquivalence d a j).property

theorem internalLabel_injective (d : OrderedClusterDatum) (a : BlockIndex d) :
    Function.Injective (internalLabel d a) := by
  intro j k hjk
  apply (labelsEquivalence d a).injective
  exact Subtype.ext hjk

theorem internalLabel_surjective (d : OrderedClusterDatum) (a : BlockIndex d)
    {i : Label} (hi : i ∈ datumBlock d a) :
    ∃ j : InternalIndex d a, internalLabel d a j = i := by
  refine ⟨(labelsEquivalence d a).symm ⟨i, hi⟩, ?_⟩
  exact congrArg Subtype.val ((labelsEquivalence d a).apply_symm_apply ⟨i, hi⟩)

theorem sum_internalLabels {A : Type*} [AddCommMonoid A]
    (d : OrderedClusterDatum) (a : BlockIndex d) (f : Label → A) :
    (∑ j : InternalIndex d a, f (internalLabel d a j)) =
      ∑ i ∈ datumBlockLabels d a, f i := by
  classical
  apply Finset.sum_bij (fun j _ => internalLabel d a j)
  · intro j _hj
    simpa only [datumBlockLabels, List.mem_toFinset] using internalLabel_mem d a j
  · intro j _hj k _hk hjk
    exact internalLabel_injective d a hjk
  · intro i hi
    have himem : i ∈ datumBlock d a := by
      simpa only [datumBlockLabels, List.mem_toFinset] using hi
    obtain ⟨j, hj⟩ := internalLabel_surjective d a himem
    exact ⟨j, Finset.mem_univ j, hj⟩
  · intro j _hj
    rfl

/-- Exact deletion of the same physical label on both sides. -/
theorem sum_erase_internalLabels {A : Type*} [AddCommMonoid A]
    (d : OrderedClusterDatum) (a : BlockIndex d) (j : InternalIndex d a)
    (f : Label → A) :
    (∑ k ∈ (Finset.univ : Finset (InternalIndex d a)).erase j,
      f (internalLabel d a k)) =
      ∑ i ∈ (datumBlockLabels d a).erase (internalLabel d a j), f i := by
  classical
  apply Finset.sum_bij (fun k _ => internalLabel d a k)
  · intro k hk
    apply Finset.mem_erase.mpr
    refine ⟨?_, ?_⟩
    · intro hlabel
      exact (Finset.mem_erase.mp hk).1 (internalLabel_injective d a hlabel)
    · simpa only [datumBlockLabels, List.mem_toFinset] using internalLabel_mem d a k
  · intro k _hk l _hl hkl
    exact internalLabel_injective d a hkl
  · intro i hi
    have himem : i ∈ datumBlock d a := by
      simpa only [datumBlockLabels, List.mem_toFinset] using (Finset.mem_erase.mp hi).2
    obtain ⟨k, hk⟩ := internalLabel_surjective d a himem
    refine ⟨k, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ k⟩, hk⟩
    intro hkj
    exact (Finset.mem_erase.mp hi).1 (hk.symm.trans (congrArg (internalLabel d a) hkj))
  · intro k _hk
    rfl

/-- The actual finite Point field component is the exact indexed scalar
force used by the already checked vertical pairing theorem. -/
theorem verticalForce_eq_actual_internal_field (m : Masses)
    (d : OrderedClusterDatum) (P : Configuration) (a : BlockIndex d)
    (j : InternalIndex d a) :
    VerticalEnergy.verticalForce (fun k => m (internalLabel d a k))
      (fun k => P (internalLabel d a k))
      (fun k => P (internalLabel d a k) 1) j =
      NewtonFieldLimits.physicalInternalField m d P (internalLabel d a j) 1 := by
  classical
  rw [VerticalEnergy.verticalForce, sum_erase_internalLabels d a j
    (fun i => m i * (P (internalLabel d a j) 1 - P i 1) /
      dist (P (internalLabel d a j)) (P i) ^ 3)]
  rw [NewtonFieldLimits.physicalInternalField,
    blockOf_eq_of_mem d (internalLabel_mem d a j)]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, Reuse.physicalNewtonForce,
    PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Scalar centering is obtained from the actual Point-valued block mean
identity, with an exact reindexing rather than an extra premise. -/
theorem indexed_coordinate_center_zero (m : Masses) (d : OrderedClusterDatum)
    (P : Configuration) (a : BlockIndex d) (k : Axis)
    (hcenter : (∑ i ∈ datumBlockLabels d a, m i • P i) = 0) :
    (∑ j : InternalIndex d a, m (internalLabel d a j) * P (internalLabel d a j) k) = 0 := by
  rw [sum_internalLabels d a (fun i => m i * P i k)]
  have hcoord := congrArg (fun p : Point => p k) hcenter
  simpa only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    PiLp.zero_apply, smul_eq_mul] using hcoord

end FourBody.SequenceBlockIndices

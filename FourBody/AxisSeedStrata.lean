import FourBody.DatumRecovery
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Exact physical axis solutions at the actual one-block/four-block seeds

Frozen Pro v2 manuscript SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
Source Section 5, lines 718--724. STATIC CANDIDATE, not compiled.

The constructions below use actual IsSeed equations, actual block-label
reindexing, actual Euclidean distance, and the original force/anisotropy.
They assert no local branch existence. The final two uniqueness bridges
are elementary eliminations of an explicit fixed-neighborhood uniqueness
statement; later they must be applied to the genuinely proved local branch
theorem. No Main, count, global classification or nondegeneracy is assumed.
-/

noncomputable section
open scoped BigOperators
namespace FourBody

def seedHorizontalLift (z : Label → ℝ) : Configuration := fun i => !₂[z i, 0]
def seedVerticalLift (z : Label → ℝ) : Configuration := fun i => !₂[0, z i]

private theorem norm_seed_horizontal_point (t : ℝ) : ‖(!₂[t, 0] : Point)‖ = |t| := by
  have hs : ‖(!₂[t, 0] : Point)‖ ^ 2 = |t| ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simp [sq_abs]
  exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp hs

private theorem norm_seed_vertical_point (t : ℝ) : ‖(!₂[0, t] : Point)‖ = |t| := by
  have hs : ‖(!₂[0, t] : Point)‖ ^ 2 = |t| ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simp [sq_abs]
  exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp hs

theorem seedHorizontalLift_distance (z : Label → ℝ) (i j : Label) :
    dist (seedHorizontalLift z i) (seedHorizontalLift z j) = |z i - z j| := by
  have hd : seedHorizontalLift z i - seedHorizontalLift z j = !₂[z i - z j, 0] := by
    ext k
    fin_cases k <;> simp [seedHorizontalLift]
  rw [dist_eq_norm, hd, norm_seed_horizontal_point]

theorem seedVerticalLift_distance (z : Label → ℝ) (i j : Label) :
    dist (seedVerticalLift z i) (seedVerticalLift z j) = |z i - z j| := by
  have hd : seedVerticalLift z i - seedVerticalLift z j = !₂[0, z i - z j] := by
    ext k
    fin_cases k <;> simp [seedVerticalLift]
  rw [dist_eq_norm, hd, norm_seed_vertical_point]

theorem seedHorizontalLift_force (m : Masses) (z : Label → ℝ) (i : Label) :
    force m (seedHorizontalLift z) i = !₂[oneDimensionalForce m z i, 0] := by
  ext k
  fin_cases k
  · simp only [force, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      PiLp.sub_apply, smul_eq_mul]
    change (∑ j ∈ Finset.univ.erase i,
      m j / dist (seedHorizontalLift z i) (seedHorizontalLift z j) ^ 3 * (z i - z j)) =
      ∑ j ∈ Finset.univ.erase i, m j * (z i - z j) / |z i - z j| ^ 3
    apply Finset.sum_congr rfl
    intro j _
    rw [seedHorizontalLift_distance]
    ring
  · simp [force, seedHorizontalLift, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]

theorem seedVerticalLift_force (m : Masses) (z : Label → ℝ) (i : Label) :
    force m (seedVerticalLift z) i = !₂[0, oneDimensionalForce m z i] := by
  ext k
  fin_cases k
  · simp [force, seedVerticalLift, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
  · simp only [force, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      PiLp.sub_apply, smul_eq_mul]
    change (∑ j ∈ Finset.univ.erase i,
      m j / dist (seedVerticalLift z i) (seedVerticalLift z j) ^ 3 * (z i - z j)) =
      ∑ j ∈ Finset.univ.erase i, m j * (z i - z j) / |z i - z j| ^ 3
    apply Finset.sum_congr rfl
    intro j _
    rw [seedVerticalLift_distance]
    ring

theorem seedHorizontalLift_collisionFree {z : Label → ℝ}
    (hz : ∀ i j, i ≠ j → z i ≠ z j) : CollisionFree (seedHorizontalLift z) := by
  intro i j hij heq
  apply hz i j hij
  exact congrArg (fun p : Point => p 0) heq

theorem seedVerticalLift_collisionFree {z : Label → ℝ}
    (hz : ∀ i j, i ≠ j → z i ≠ z j) : CollisionFree (seedVerticalLift z) := by
  intro i j hij heq
  apply hz i j hij
  exact congrArg (fun p : Point => p 1) heq

/-- The normalized horizontal one-dimensional root is an exact original
solution after the positive epsilon dilation, with s=epsilon^(-3). -/
theorem scaled_horizontal_scalar_solution {m : Masses} {z : Label → ℝ}
    (hz : OneDimensionalSolution m z) {ε : ℝ} (hε : 0 < ε) :
    IsSolution m (parameterFromEpsilon ε) (ε • seedHorizontalLift z) := by
  have hcf := seedHorizontalLift_collisionFree hz.1
  refine ⟨collisionFree_positive_dilation hcf hε, ?_⟩
  intro i
  rw [force_positive_dilation m hcf hε i, seedHorizontalLift_force, hz.2.2 i]
  ext k
  fin_cases k
  · change (ε ^ 2)⁻¹ * z i = (ε ^ 3)⁻¹ * (ε * z i)
    field_simp [ne_of_gt hε]
  · simp [anisotropy, seedHorizontalLift]

/-- The normalized vertical one-dimensional root is an exact original
solution at every s; the anisotropy does not alter its vertical coordinate. -/
theorem vertical_scalar_solution {m : Masses} {z : Label → ℝ}
    (hz : OneDimensionalSolution m z) (s : ℝ) : IsSolution m s (seedVerticalLift z) := by
  refine ⟨seedVerticalLift_collisionFree hz.1, ?_⟩
  intro i
  rw [seedVerticalLift_force, hz.2.2 i]
  ext k
  fin_cases k <;> simp [anisotropy, seedVerticalLift]

theorem oneDimensionalForce_full_sum_recovery {n : ℕ}
    (μ z : Fin n → ℝ) (i : Fin n) :
    oneDimensionalForce μ z i = ∑ j, μ j * (z i - z j) / |z i - z j| ^ 3 := by
  have hz : μ i * (z i - z i) / |z i - z i| ^ 3 = 0 := by simp
  have hsum := Finset.sum_erase_add Finset.univ
    (fun j : Fin n => μ j * (z i - z j) / |z i - z j| ^ 3) (Finset.mem_univ i)
  rw [hz, add_zero] at hsum
  exact hsum

theorem one_block_labels_univ (d : OrderedClusterDatum) (hd : d.blocks.length = 1)
    (a : BlockIndex d) : datumBlockLabels d a = Finset.univ := by
  ext i
  simp only [datumBlockLabels, List.mem_toFinset, Finset.mem_univ, iff_true]
  have hia : blockOf d i = a := by
    apply Fin.ext
    have hi := (blockOf d i).isLt
    have ha := a.isLt
    omega
  exact (mem_datumBlock_iff d i a).mpr hia

/-- For k=1 the internal one-dimensional equations are exactly the global
literal-label equations, proved by actual block-position reindexing. -/
theorem one_block_seed_global_scalar_solution {m : Masses} {d : OrderedClusterDatum}
    (hd : d.blocks.length = 1) (h : BlowupCoordinates m d) (hh : IsSeed m d h) :
    OneDimensionalSolution m (innerU h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij hU
    let a : BlockIndex d := blockOf d i
    have himem : i ∈ datumBlock d a := label_mem_blockOf d i
    have hjmem : j ∈ datumBlock d a := by
      rw [show a = blockOf d j from (one_block_same_blockOf d hd i j)]
      exact label_mem_blockOf d j
    obtain ⟨p, hp⟩ := internalLabel_surjective d a himem
    obtain ⟨r, hr⟩ := internalLabel_surjective d a hjmem
    have hpr : p = r := ((hh.2.2.2.2 a).1).injective (by simpa [hp, hr] using hU)
    exact hij (hp.symm.trans ((congrArg (internalLabel d a) hpr).trans hr))
  · let a : BlockIndex d := blockOf d (0 : Label)
    have hc := (coordinate_constraints h).2.2.1 a
    simpa only [one_block_labels_univ d hd a] using hc
  · intro i
    let a : BlockIndex d := blockOf d i
    obtain ⟨p, hp⟩ := internalLabel_surjective d a (label_mem_blockOf d i)
    have hforce := ((hh.2.2.2.2 a).2).2.2 p
    rw [oneDimensionalForce_full_sum_recovery, hp] at hforce
    calc
      oneDimensionalForce m (innerU h) i =
          ∑ j : Label, m j * (innerU h i - innerU h j) / |innerU h i - innerU h j| ^ 3 :=
        oneDimensionalForce_full_sum_recovery _ _ i
      _ = ∑ j : InternalIndex d a, m (internalLabel d a j) *
          (innerU h i - innerU h (internalLabel d a j)) /
            |innerU h i - innerU h (internalLabel d a j)| ^ 3 := by
        simpa only [one_block_labels_univ d hd a] using
          (sum_internalLabels d a (fun j : Label =>
            m j * (innerU h i - innerU h j) / |innerU h i - innerU h j| ^ 3)).symm
      _ = innerU h i := by simpa only [hp] using hforce

theorem one_block_seed_physical_formula {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (hd : d.blocks.length = 1)
    (h : BlowupCoordinates m d) (hh : IsSeed m d h) (ε : ℝ) :
    physicalCoordinates ε h = ε • seedHorizontalLift (innerU h) := by
  funext i
  have hy := (one_block_outer_coordinates_zero hm hd h (blockOf d i)).2
  ext k
  fin_cases k <;> simp [physicalCoordinates, seedHorizontalLift, hh.1, hh.2.1, hy]

/-- Source k=1 exact branch candidate: the actual physical seed coordinates
are an original collision-free x-axis solution, without local IFT input. -/
theorem one_block_seed_exact_solution {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (hd : d.blocks.length = 1)
    (h : BlowupCoordinates m d) (hh : IsSeed m d h) {ε : ℝ} (hε : 0 < ε) :
    IsSolution m (parameterFromEpsilon ε) (physicalCoordinates ε h) ∧
      OnXAxis (physicalCoordinates ε h) := by
  rw [one_block_seed_physical_formula hm hd h hh]
  refine ⟨scaled_horizontal_scalar_solution (one_block_seed_global_scalar_solution hd h hh) hε, ?_⟩
  intro i
  simp [seedHorizontalLift]

/-- The actual fiber over every label is a singleton for k=4. -/
theorem four_block_labels_singleton (d : OrderedClusterDatum) (hd : d.blocks.length = 4)
    (i : Label) : datumBlockLabels d (blockOf d i) = {i} := by
  ext j
  rw [datumBlockLabels_eq_fiber]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hji
    exact four_block_blockOf_injective d hd hji
  · rintro rfl
    rfl

theorem four_block_internal_coordinates_zero {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (hd : d.blocks.length = 4)
    (h : BlowupCoordinates m d) (i : Label) : innerU h i = 0 ∧ innerV h i = 0 := by
  have hu := (coordinate_constraints h).2.2.1 (blockOf d i)
  have hv := (coordinate_constraints h).2.2.2 (blockOf d i)
  rw [four_block_labels_singleton d hd, Finset.sum_singleton] at hu hv
  exact ⟨(mul_eq_zero.mp hu).resolve_left (ne_of_gt (hm i)),
    (mul_eq_zero.mp hv).resolve_left (ne_of_gt (hm i))⟩

theorem four_block_mass_at_label (m : Masses) (d : OrderedClusterDatum)
    (hd : d.blocks.length = 4) (i : Label) : datumBlockMass m d (blockOf d i) = m i := by
  unfold datumBlockMass
  rw [four_block_labels_singleton d hd, Finset.sum_singleton]

theorem four_block_sum_blockOf {A : Type*} [AddCommMonoid A]
    (d : OrderedClusterDatum) (hd : d.blocks.length = 4) (f : BlockIndex d → A) :
    (∑ i : Label, f (blockOf d i)) = ∑ a : BlockIndex d, f a :=
  (show Function.Bijective (blockOf d) from
    ⟨four_block_blockOf_injective d hd, blockOf_surjective d⟩).sum_comp f

/-- For k=4 the actual outer equations become the global labelled scalar
equations with singleton block masses equal to the original masses. -/
theorem four_block_seed_global_scalar_solution {m : Masses} {d : OrderedClusterDatum}
    (hd : d.blocks.length = 4) (h : BlowupCoordinates m d) (hh : IsSeed m d h) :
    OneDimensionalSolution m (fun i => outerY h (blockOf d i)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij hy
    exact hij (four_block_blockOf_injective d hd (hh.2.2.1.injective hy))
  · calc
      (∑ i : Label, m i * outerY h (blockOf d i)) =
          ∑ i : Label, datumBlockMass m d (blockOf d i) * outerY h (blockOf d i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [four_block_mass_at_label m d hd i]
      _ = ∑ a : BlockIndex d, datumBlockMass m d a * outerY h a :=
        four_block_sum_blockOf d hd (fun a => datumBlockMass m d a * outerY h a)
      _ = 0 := (coordinate_constraints h).2.1
  · intro i
    calc
      oneDimensionalForce m (fun j => outerY h (blockOf d j)) i =
          ∑ j : Label, m j * (outerY h (blockOf d i) - outerY h (blockOf d j)) /
            |outerY h (blockOf d i) - outerY h (blockOf d j)| ^ 3 :=
        oneDimensionalForce_full_sum_recovery _ _ i
      _ = ∑ j : Label, datumBlockMass m d (blockOf d j) *
          (outerY h (blockOf d i) - outerY h (blockOf d j)) /
            |outerY h (blockOf d i) - outerY h (blockOf d j)| ^ 3 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [four_block_mass_at_label m d hd j]
      _ = ∑ a : BlockIndex d, datumBlockMass m d a *
          (outerY h (blockOf d i) - outerY h a) / |outerY h (blockOf d i) - outerY h a| ^ 3 :=
        four_block_sum_blockOf d hd (fun a => datumBlockMass m d a *
          (outerY h (blockOf d i) - outerY h a) / |outerY h (blockOf d i) - outerY h a| ^ 3)
      _ = oneDimensionalForce (datumBlockMass m d) (outerY h) (blockOf d i) :=
        (oneDimensionalForce_full_sum_recovery _ _ _).symm
      _ = outerY h (blockOf d i) := hh.2.2.2.1.2.2 (blockOf d i)

theorem four_block_seed_physical_formula {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (hd : d.blocks.length = 4)
    (h : BlowupCoordinates m d) (hh : IsSeed m d h) (ε : ℝ) :
    physicalCoordinates ε h = seedVerticalLift (fun i => outerY h (blockOf d i)) := by
  funext i
  have hu := (four_block_internal_coordinates_zero hm hd h i).1
  ext k
  fin_cases k <;> simp [physicalCoordinates, seedVerticalLift, hh.1, hh.2.1, hu]

/-- Source k=4 exact branch candidate: the physical seed coordinates are an
original collision-free y-axis solution and do not depend on epsilon. -/
theorem four_block_seed_exact_solution {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (hd : d.blocks.length = 4)
    (h : BlowupCoordinates m d) (hh : IsSeed m d h) (ε : ℝ) :
    IsSolution m (parameterFromEpsilon ε) (physicalCoordinates ε h) ∧
      OnYAxis (physicalCoordinates ε h) := by
  rw [four_block_seed_physical_formula hm hd h hh]
  refine ⟨vertical_scalar_solution (four_block_seed_global_scalar_solution hd h hh) _, ?_⟩
  intro i
  simp [seedVerticalLift]

/-- These corollaries use the seeds whose existence/uniqueness was actually
constructed from centered scalar minimization in the current project. -/
theorem one_block_actual_seed_exact_solution {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (hd : d.blocks.length = 1) {ε : ℝ} (hε : 0 < ε) :
    IsSolution m (parameterFromEpsilon ε) (physicalCoordinates ε (seedCoordinates hm d)) ∧
      OnXAxis (physicalCoordinates ε (seedCoordinates hm d)) :=
  one_block_seed_exact_solution hm hd _ (seedCoordinates_isSeed hm d) hε

theorem four_block_actual_seed_exact_solution {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (hd : d.blocks.length = 4) (ε : ℝ) :
    IsSolution m (parameterFromEpsilon ε) (physicalCoordinates ε (seedCoordinates hm d)) ∧
      OnYAxis (physicalCoordinates ε (seedCoordinates hm d)) :=
  four_block_seed_exact_solution hm hd _ (seedCoordinates_isSeed hm d) ε

/-- A narrow fixed-neighborhood uniqueness elimination bridge. This does
not construct that uniqueness statement; the future proved local theorem
must supply it for the actual fixed N and actual physical branch value. -/
theorem one_block_seed_identified_by_fixed_neighborhood_uniqueness
    {m : Masses} (hm : PositiveMasses m) {d : OrderedClusterDatum}
    (hd : d.blocks.length = 1) {ε : ℝ} (hε : 0 < ε)
    (seed : BlowupCoordinates m d) (hseed : IsSeed m d seed)
    (N : Set (BlowupCoordinates m d)) (hseedN : seed ∈ N) (q : Configuration)
    (hunique : ∀ q' : Configuration,
      IsSolution m (parameterFromEpsilon ε) q' →
      (∃ h' : BlowupCoordinates m d, h' ∈ N ∧ RepresentsCoordinates m d ε h' q') → q' = q) :
    physicalCoordinates ε seed = q ∧ OnXAxis q := by
  have hs := one_block_seed_exact_solution hm hd seed hseed hε
  have heq := hunique (physicalCoordinates ε seed) hs.1
    ⟨seed, hseedN, represents_physicalCoordinates ε seed⟩
  exact ⟨heq, heq ▸ hs.2⟩

theorem four_block_seed_identified_by_fixed_neighborhood_uniqueness
    {m : Masses} (hm : PositiveMasses m) {d : OrderedClusterDatum}
    (hd : d.blocks.length = 4) (ε : ℝ)
    (seed : BlowupCoordinates m d) (hseed : IsSeed m d seed)
    (N : Set (BlowupCoordinates m d)) (hseedN : seed ∈ N) (q : Configuration)
    (hunique : ∀ q' : Configuration,
      IsSolution m (parameterFromEpsilon ε) q' →
      (∃ h' : BlowupCoordinates m d, h' ∈ N ∧ RepresentsCoordinates m d ε h' q') → q' = q) :
    physicalCoordinates ε seed = q ∧ OnYAxis q := by
  have hs := four_block_seed_exact_solution hm hd seed hseed ε
  have heq := hunique (physicalCoordinates ε seed) hs.1
    ⟨seed, hseedN, represents_physicalCoordinates ε seed⟩
  exact ⟨heq, heq ▸ hs.2⟩

end FourBody

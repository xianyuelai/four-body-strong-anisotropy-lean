import FourBody.Geometry
import FourBody.ExternalClusterBounds
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
STATIC, not yet elaborated. Source: the frozen v2, Section 2, lines 237--246
and 301--313. These are actual extrema of Euclidean pair distances on any
nonempty finite subset of the four fixed labels; no radius or separation
certificate is taken as input.
-/
set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace FourBody.SourceFaithfulCluster

def pairDistances (q : Configuration) (J : Finset Label) : Finset ℝ := by
  classical
  exact (J.product J).image (fun p : Label × Label => dist (q p.1) (q p.2))

theorem pairDistances_nonempty (q : Configuration) (J : Finset Label)
    (hJ : J.Nonempty) : (pairDistances q J).Nonempty := by
  classical
  obtain ⟨i, hi⟩ := hJ
  refine ⟨dist (q i) (q i), ?_⟩
  exact Finset.mem_image.mpr ⟨(i, i), Finset.mem_product.mpr ⟨hi, hi⟩, rfl⟩

def diameter (q : Configuration) (J : Finset Label) (hJ : J.Nonempty) : ℝ :=
  (pairDistances q J).max' (pairDistances_nonempty q J hJ)

theorem diameter_attained (q : Configuration) (J : Finset Label)
    (hJ : J.Nonempty) :
    ∃ a ∈ J, ∃ b ∈ J, dist (q a) (q b) = diameter q J hJ := by
  classical
  have hmem := Finset.max'_mem (pairDistances q J) (pairDistances_nonempty q J hJ)
  obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hmem
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
  exact ⟨p.1, ha, p.2, hb, heq⟩

theorem dist_le_diameter (q : Configuration) (J : Finset Label)
    (hJ : J.Nonempty) {a b : Label} (ha : a ∈ J) (hb : b ∈ J) :
    dist (q a) (q b) ≤ diameter q J hJ := by
  classical
  exact Finset.le_max' (pairDistances q J) _
    (Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩)

theorem diameter_nonneg (q : Configuration) (J : Finset Label)
    (hJ : J.Nonempty) : 0 ≤ diameter q J hJ := by
  obtain ⟨a, _, b, _, hab⟩ := diameter_attained q J hJ
  rw [← hab]
  exact dist_nonneg

theorem diameter_pos (q : Configuration) (hq : CollisionFree q)
    (J : Finset Label) (hJ : J.Nonempty) (hcard : 2 ≤ J.card) :
    0 < diameter q J hJ := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < J.card)
  exact (collisionFree_dist_pos hq hab).trans_le (dist_le_diameter q J hJ ha hb)

theorem diameter_le_of_all_dist_le (q : Configuration) (J : Finset Label)
    (hJ : J.Nonempty) (r : ℝ)
    (hbound : ∀ a ∈ J, ∀ b ∈ J, dist (q a) (q b) ≤ r) :
    diameter q J hJ ≤ r := by
  obtain ⟨a, ha, b, hb, hab⟩ := diameter_attained q J hJ
  rw [← hab]
  exact hbound a ha b hb

theorem diameter_eq_of_attained (q : Configuration) (J : Finset Label)
    (hJ : J.Nonempty) (r : ℝ)
    (hbound : ∀ a ∈ J, ∀ b ∈ J, dist (q a) (q b) ≤ r)
    (hattained : ∃ a ∈ J, ∃ b ∈ J, dist (q a) (q b) = r) :
    diameter q J hJ = r := by
  apply le_antisymm (diameter_le_of_all_dist_le q J hJ r hbound)
  obtain ⟨a, ha, b, hb, hab⟩ := hattained
  rw [← hab]
  exact dist_le_diameter q J hJ ha hb

theorem diameter_mono (q : Configuration) (J K : Finset Label)
    (hJ : J.Nonempty) (hK : K.Nonempty) (hJK : J ⊆ K) :
    diameter q J hJ ≤ diameter q K hK := by
  obtain ⟨a, ha, b, hb, hab⟩ := diameter_attained q J hJ
  rw [← hab]
  exact dist_le_diameter q K hK (hJK ha) (hJK hb)

theorem complement_nonempty (J : Finset Label) (hproper : J ≠ Finset.univ) :
    (Finset.univ \ J).Nonempty := by
  classical
  have hnot : ¬ ∀ j : Label, j ∈ J := by
    intro hall
    apply hproper
    apply Finset.ext
    intro j
    simp only [Finset.mem_univ, iff_true]
    exact hall j
  obtain ⟨j, hj⟩ := not_forall.mp hnot
  exact ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩⟩

def crossDistances (q : Configuration) (J : Finset Label) : Finset ℝ := by
  classical
  exact (J.product (Finset.univ \ J)).image
    (fun p : Label × Label => dist (q p.1) (q p.2))

theorem crossDistances_nonempty (q : Configuration) (J : Finset Label)
    (hJ : J.Nonempty) (hproper : J ≠ Finset.univ) :
    (crossDistances q J).Nonempty := by
  classical
  obtain ⟨a, ha⟩ := hJ
  obtain ⟨b, hb⟩ := complement_nonempty J hproper
  exact ⟨dist (q a) (q b), Finset.mem_image.mpr
    ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩⟩

def separation (q : Configuration) (J : Finset Label) (hJ : J.Nonempty)
    (hproper : J ≠ Finset.univ) : ℝ :=
  (crossDistances q J).min' (crossDistances_nonempty q J hJ hproper)

theorem separation_attained (q : Configuration) (J : Finset Label)
    (hJ : J.Nonempty) (hproper : J ≠ Finset.univ) :
    ∃ a ∈ J, ∃ b ∉ J, dist (q a) (q b) = separation q J hJ hproper := by
  classical
  have hmem := Finset.min'_mem (crossDistances q J)
    (crossDistances_nonempty q J hJ hproper)
  obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hmem
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
  exact ⟨p.1, ha, p.2, (Finset.mem_sdiff.mp hb).2, heq⟩

theorem separation_le_cross (q : Configuration) (J : Finset Label)
    (hJ : J.Nonempty) (hproper : J ≠ Finset.univ)
    {a b : Label} (ha : a ∈ J) (hb : b ∉ J) :
    separation q J hJ hproper ≤ dist (q a) (q b) := by
  classical
  exact Finset.min'_le (crossDistances q J) _ (Finset.mem_image.mpr
    ⟨(a, b), Finset.mem_product.mpr ⟨ha, Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ b, hb⟩⟩, rfl⟩)

theorem separation_nonneg (q : Configuration) (J : Finset Label)
    (hJ : J.Nonempty) (hproper : J ≠ Finset.univ) :
    0 ≤ separation q J hJ hproper := by
  obtain ⟨a, _, b, _, hab⟩ := separation_attained q J hJ hproper
  rw [← hab]
  exact dist_nonneg

theorem separation_pos (q : Configuration) (hq : CollisionFree q)
    (J : Finset Label) (hJ : J.Nonempty) (hproper : J ≠ Finset.univ) :
    0 < separation q J hJ hproper := by
  obtain ⟨a, ha, b, hb, hab⟩ := separation_attained q J hJ hproper
  have hne : a ≠ b := by
    intro heq
    exact hb (heq ▸ ha)
  rw [← hab]
  exact collisionFree_dist_pos hq hne

/-- Both attainment and every comparison are exported in the public type. -/
theorem separation_is_actual_minimum (q : Configuration) (J : Finset Label)
    (hJ : J.Nonempty) (hproper : J ≠ Finset.univ) :
    (∃ a ∈ J, ∃ b ∉ J, dist (q a) (q b) = separation q J hJ hproper) ∧
    (∀ a ∈ J, ∀ b ∉ J, separation q J hJ hproper ≤ dist (q a) (q b)) := by
  exact ⟨separation_attained q J hJ hproper,
    fun _ ha _ hb => separation_le_cross q J hJ hproper ha hb⟩

/-- The exact triangle bound used before the paper weakens it to δ/2. -/
theorem hull_exterior_delta_sub_diameter (q : Configuration) (J : Finset Label)
    (hJ : J.Nonempty) (hproper : J ≠ Finset.univ)
    {z : Point} (hz : z ∈ ClusterVirial.clusterHull q J)
    {b : Label} (hb : b ∉ J) :
    separation q J hJ hproper - diameter q J hJ ≤ dist z (q b) := by
  have hJw := hJ
  obtain ⟨a, ha⟩ := hJw
  have hcross := separation_le_cross q J hJ hproper ha hb
  have hnear := ClusterVirial.hull_dist_le_diameter q J
    (fun _ hi _ hj => dist_le_diameter q J hJ hi hj) ha hz
  have htriangle := dist_triangle (q a) z (q b)
  rw [dist_comm (q a) z] at htriangle
  linarith

theorem hull_exterior_half_separation (q : Configuration) (J : Finset Label)
    (hJ : J.Nonempty) (hproper : J ≠ Finset.univ)
    (hsmall : diameter q J hJ ≤ separation q J hJ hproper / 2)
    {z : Point} (hz : z ∈ ClusterVirial.clusterHull q J)
    {b : Label} (hb : b ∉ J) :
    separation q J hJ hproper / 2 ≤ dist z (q b) := by
  have hbound := hull_exterior_delta_sub_diameter q J hJ hproper hz hb
  linarith

/-- The already proved physical Newton-field estimate instantiated at
the actual maximum and minimum, with all geometric inputs discharged. -/
theorem external_lipschitz_on_actual_hull (m : Masses) (hm : PositiveMasses m)
    (q : Configuration) (hq : CollisionFree q) (J : Finset Label)
    (hJ : J.Nonempty) (hproper : J ≠ Finset.univ)
    (hsmall : diameter q J hJ ≤ separation q J hJ hproper / 2)
    {z w : Point} (hz : z ∈ ClusterVirial.clusterHull q J)
    (hw : w ∈ ClusterVirial.clusterHull q J) :
    ‖ClusterVirial.externalField m q J z - ClusterVirial.externalField m q J w‖ ≤
      (16 * (totalMass m - ClusterVirial.mass m J) /
        separation q J hJ hproper ^ 3) * ‖z - w‖ := by
  exact ClusterVirial.external_lipschitz_on_hull m hm q J hJ
    (separation_pos q hq J hJ hproper) hsmall
    (fun _ hi _ hj => dist_le_diameter q J hJ hi hj)
    (fun _ hi _ hj => separation_le_cross q J hJ hproper hi hj) hz hw

theorem actual_isolation_implies_half_separation (q : Configuration)
    (J : Finset Label) (hJ : J.Nonempty) (hproper : J ≠ Finset.univ)
    (T : ℝ) (hT : 2 < T)
    (hisolated : T * diameter q J hJ ≤ separation q J hJ hproper) :
    diameter q J hJ ≤ separation q J hJ hproper / 2 := by
  have hr := diameter_nonneg q J hJ
  nlinarith

/-- Genuine solution equations imply the source virial inequality for
a proper isolated cluster with its own exact diameter and separation. -/
theorem actual_isolated_cluster_virial_bound (m : Masses) (hm : PositiveMasses m)
    (q : Configuration) {s : ℝ} (hs : 1 ≤ s) (hq : IsSolution m s q)
    (J : Finset Label) (hJ : J.Nonempty) (hproper : J ≠ Finset.univ)
    (hcard : 2 ≤ J.card) (T : ℝ) (hT : 2 < T)
    (hisolated : T * diameter q J hJ ≤ separation q J hJ hproper) :
    ClusterVirial.mass m J ≤ s * diameter q J hJ ^ 3 +
      (16 * (totalMass m - ClusterVirial.mass m J) /
        separation q J hJ hproper ^ 3) * diameter q J hJ ^ 3 := by
  exact ClusterVirial.separated_cluster_virial_bound m hm q hs hq J hcard
    (diameter_pos q hq.1 J hJ hcard) (separation_pos q hq.1 J hJ hproper)
    (actual_isolation_implies_half_separation q J hJ hproper T hT hisolated)
    (fun _ hi _ hj => dist_le_diameter q J hJ hi hj)
    (fun _ hi _ hj => separation_le_cross q J hJ hproper hi hj)

end FourBody.SourceFaithfulCluster

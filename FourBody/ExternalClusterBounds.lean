import FourBody.ClusterVirial
import FourBody.Reuse.NewtonBounds
import Mathlib.Analysis.Convex.Combination

/-!
The source instance of the finite-cluster external Lipschitz estimate.
This uses the genuine Newton derivative and convex-domain mean-value
bound from FourBody.Reuse.NewtonBounds, not an assumed analysis interface.
The hull is the actual convex hull of the points with labels in J.
Separation is the physical cross-cluster distance lower bound delta.
-/

noncomputable section
open scoped BigOperators

namespace FourBody.ClusterVirial

def clusterHull (q : Configuration) (J : Finset Label) : Set Point :=
  convexHull ℝ (q '' (J : Set Label))

theorem clusterHull_convex (q : Configuration) (J : Finset Label) :
    Convex ℝ (clusterHull q J) :=
  convex_convexHull ℝ _

theorem point_mem_clusterHull (q : Configuration) (J : Finset Label)
    {i : Label} (hi : i ∈ J) : q i ∈ clusterHull q J := by
  exact subset_convexHull ℝ _ ⟨i, hi, rfl⟩

theorem centroid_mem_clusterHull (m : Masses) (hm : PositiveMasses m)
    (q : Configuration) (J : Finset Label) (hJ : J.Nonempty) :
    centroid m q J ∈ clusterHull q J := by
  change J.centerMass m q ∈ clusterHull q J
  exact (clusterHull_convex q J).centerMass_mem
    (fun i _ => (hm i).le) (mass_pos m hm J hJ)
    (fun i hi => point_mem_clusterHull q J hi)

/-- The actual hull is in every radius-r closed ball centered at a cluster point. -/
theorem hull_dist_le_diameter (q : Configuration) (J : Finset Label) {r : ℝ}
    (hdiam : ∀ i ∈ J, ∀ j ∈ J, dist (q i) (q j) ≤ r)
    {i : Label} (hi : i ∈ J) {z : Point} (hz : z ∈ clusterHull q J) :
    dist z (q i) ≤ r := by
  have hsubset : q '' (J : Set Label) ⊆ Metric.closedBall (q i) r := by
    rintro z ⟨j, hj, rfl⟩
    exact hdiam j hj i hi
  exact (convexHull_min hsubset (convex_closedBall (q i) r)) hz

theorem hull_exterior_separation (q : Configuration) (J : Finset Label)
    (hJ : J.Nonempty) {r δ : ℝ} (hrδ : r ≤ δ / 2)
    (hdiam : ∀ i ∈ J, ∀ j ∈ J, dist (q i) (q j) ≤ r)
    (hsep : ∀ i ∈ J, ∀ j ∉ J, δ ≤ dist (q i) (q j)) :
    ∀ z ∈ clusterHull q J, ∀ j ∈ Finset.univ \ J, δ / 2 ≤ dist z (q j) := by
  obtain ⟨i, hi⟩ := hJ
  intro z hz j hj
  have hd := hsep i hi j (Finset.mem_sdiff.mp hj).2
  have hnear : dist (q i) z ≤ r := by
    rw [dist_comm]
    exact hull_dist_le_diameter q J hdiam hi hz
  have ht := dist_triangle (q i) z (q j)
  linarith

theorem complementary_mass (m : Masses) (J : Finset Label) :
    (∑ j ∈ Finset.univ \ J, m j) = totalMass m - mass m J := by
  exact Finset.sum_sdiff_eq_sub (Finset.subset_univ J)

theorem externalField_eq_exteriorNewtonForce (m : Masses) (q : Configuration)
    (J : Finset Label) (z : Point) :
    externalField m q J z =
      FourBody.Reuse.exteriorNewtonForce (Finset.univ \ J) m q z := rfl

/-- v2 eq:external-lipschitz with exactly its numerical constant 16. -/
theorem external_lipschitz_on_hull (m : Masses) (hm : PositiveMasses m)
    (q : Configuration) (J : Finset Label) (hJ : J.Nonempty)
    {r δ : ℝ} (hδ : 0 < δ) (hrδ : r ≤ δ / 2)
    (hdiam : ∀ i ∈ J, ∀ j ∈ J, dist (q i) (q j) ≤ r)
    (hsep : ∀ i ∈ J, ∀ j ∉ J, δ ≤ dist (q i) (q j))
    {z w : Point} (hz : z ∈ clusterHull q J) (hw : w ∈ clusterHull q J) :
    ‖externalField m q J z - externalField m q J w‖ ≤
      (16 * (totalMass m - mass m J) / δ ^ 3) * ‖z - w‖ := by
  simp only [externalField_eq_exteriorNewtonForce]
  simpa only [complementary_mass] using
    FourBody.Reuse.exteriorNewtonForce_sub_norm_bound_on_convex
      (Finset.univ \ J) m q (clusterHull q J) δ (fun i _ => (hm i).le)
      hδ (clusterHull_convex q J)
      (hull_exterior_separation q J hJ hrδ hdiam hsep) z w hz hw

theorem external_pointwise_lipschitz (m : Masses) (hm : PositiveMasses m)
    (q : Configuration) (J : Finset Label) (hJ : J.Nonempty)
    {r δ : ℝ} (hδ : 0 < δ) (hrδ : r ≤ δ / 2)
    (hdiam : ∀ i ∈ J, ∀ j ∈ J, dist (q i) (q j) ≤ r)
    (hsep : ∀ i ∈ J, ∀ j ∉ J, δ ≤ dist (q i) (q j)) :
    ∀ i ∈ J,
      ‖externalField m q J (q i) - externalField m q J (centroid m q J)‖ ≤
        (16 * (totalMass m - mass m J) / δ ^ 3) * ‖centered m q J i‖ := by
  intro i hi
  exact external_lipschitz_on_hull m hm q J hJ hδ hrδ hdiam hsep
    (point_mem_clusterHull q J hi) (centroid_mem_clusterHull m hm q J hJ)

/-- The physical separated-cluster instance of eq:cluster-virial-bound.
    No final two-scale estimate is a premise. -/
theorem separated_cluster_virial_bound (m : Masses) (hm : PositiveMasses m)
    (q : Configuration) {s : ℝ} (hs : 1 ≤ s) (hq : IsSolution m s q)
    (J : Finset Label) (hcard : 2 ≤ J.card) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hrδ : r ≤ δ / 2)
    (hdiam : ∀ i ∈ J, ∀ j ∈ J, dist (q i) (q j) ≤ r)
    (hsep : ∀ i ∈ J, ∀ j ∉ J, δ ≤ dist (q i) (q j)) :
    mass m J ≤ s * r ^ 3 + (16 * (totalMass m - mass m J) / δ ^ 3) * r ^ 3 := by
  have hJ : J.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hcard)
  exact cluster_virial_bound m hm q hs hq J hcard hr hdiam
    (external_pointwise_lipschitz m hm q J hJ hδ hrδ hdiam hsep)

end FourBody.ClusterVirial

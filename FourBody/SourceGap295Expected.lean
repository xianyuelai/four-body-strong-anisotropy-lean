import FourBody.SourceGapSharp
import FourBody.ClusterVertical
import FourBody.ClusterExtrema

/-!
Independent source expectations authored BEFORE the new proof draft or any
new Lean output. Frozen v2 line295 is m_J*h/((ell-1)*r^3) <= h+L*r.
All real denominator subtraction is explicit. Neither this proposition nor
the later coefficient-three bound is a hypothesis of its proof endpoints.
STATIC_NOT_RUN: no Lean/Lake/compiler/AST/axiom acceptance claimed.
-/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace FourBody.SourceGap295.ExpectedSignatures
open ClusterVertical SourceFaithfulGap SourceFaithfulCluster

def reduced_cardinality_real_pos : Prop :=
  ∀ (J : Finset Label), 2 ≤ J.card → 0 < (J.card : ℝ) - 1

def vertical_gap_sharp_from_cut : Prop :=
  ∀ {m : Masses}, PositiveMasses m →
  ∀ {q : Configuration} {s : ℝ}, IsSolution m s q →
  ∀ {J A : Finset Label}, A ⊆ J → A.Nonempty → (J \ A).Nonempty →
    2 ≤ J.card → ∀ {r h g L : ℝ}, 0 < r → 0 < g → 0 ≤ L →
    LipschitzOnHull m q J L →
    (∀ i ∈ J, ∀ j ∈ J, dist (q i) (q j) ≤ r) →
    (∀ i ∈ A, ∀ j ∈ J \ A, g ≤ q j 1 - q i 1) →
    (∀ i ∈ A, ∀ j ∈ J \ A, q j 1 - q i 1 ≤ h) →
    h / ((J.card : ℝ) - 1) ≤ g →
    cutMass m J * h / (((J.card : ℝ) - 1) * r ^ 3) ≤ h + L * r

def exists_largest_cut_mean_evidence : Prop :=
  ∀ {m : Masses}, PositiveMasses m →
  ∀ {q : Configuration} {s : ℝ}, IsSolution m s q →
  ∀ (J : Finset Label) (hJ : J.Nonempty), 2 ≤ J.card →
  ∀ {r L : ℝ}, 0 < r → 0 ≤ L → LipschitzOnHull m q J L →
    (∀ i ∈ J, ∀ j ∈ J, dist (q i) (q j) ≤ r) →
    0 < clusterCoordinateDiameter J (fun i => q i 1) hJ →
    ∃ (n : ℕ) (σ : Fin (n + 1) ≃ {i : Label // i ∈ J})
      (k : Fin n) (A B : Finset Label),
      J.card = n + 1 ∧ Monotone (fun l => q (σ l).val 1) ∧
      A ⊆ J ∧ B ⊆ J ∧ A.Nonempty ∧ B.Nonempty ∧
      B = J \ A ∧ Disjoint A B ∧ A ∪ B = J ∧
      (σ k.castSucc).val ∈ A ∧ (σ k.succ).val ∈ B ∧
      0 < adjacentGap (fun l => q (σ l).val 1) k ∧
      (∀ l : Fin n, adjacentGap (fun a => q (σ a).val 1) l ≤
        adjacentGap (fun a => q (σ a).val 1) k) ∧
      clusterCoordinateDiameter J (fun i => q i 1) hJ /
        (((J.card - 1 : ℕ) : ℝ)) ≤ adjacentGap (fun a => q (σ a).val 1) k ∧
      clusterCoordinateDiameter J (fun i => q i 1) hJ ≤
        (((J.card - 1 : ℕ) : ℝ)) * adjacentGap (fun a => q (σ a).val 1) k ∧
      (∀ i ∈ A, ∀ j ∈ B,
        adjacentGap (fun a => q (σ a).val 1) k ≤ q j 1 - q i 1) ∧
      (cutMean m q 1 B - cutMean m q 1 A =
        (1 / cutMass m A + 1 / cutMass m B) * internalCrossForce m q 1 J A +
          cutMean m (externalConfiguration m q J) 1 B -
            cutMean m (externalConfiguration m q J) 1 A) ∧
      |cutMean m (externalConfiguration m q J) 1 B -
        cutMean m (externalConfiguration m q J) 1 A| ≤ L * r ∧
      cutMass m J * adjacentGap (fun a => q (σ a).val 1) k / r ^ 3 ≤
        (1 / cutMass m A + 1 / cutMass m B) * internalCrossForce m q 1 J A ∧
      cutMean m q 1 B - cutMean m q 1 A ≤
        clusterCoordinateDiameter J (fun i => q i 1) hJ ∧
      cutMass m J * clusterCoordinateDiameter J (fun i => q i 1) hJ /
        (((J.card : ℝ) - 1) * r ^ 3) ≤
        clusterCoordinateDiameter J (fun i => q i 1) hJ + L * r

def cluster_vertical_gap_sharp : Prop :=
  ∀ {m : Masses}, PositiveMasses m →
  ∀ {q : Configuration} {s : ℝ}, IsSolution m s q →
  ∀ (J : Finset Label) (hJ : J.Nonempty), 2 ≤ J.card →
  ∀ {r L : ℝ}, 0 < r → 0 ≤ L → LipschitzOnHull m q J L →
    (∀ i ∈ J, ∀ j ∈ J, dist (q i) (q j) ≤ r) →
    0 < clusterCoordinateDiameter J (fun i => q i 1) hJ →
    cutMass m J * clusterCoordinateDiameter J (fun i => q i 1) hJ /
      (((J.card : ℝ) - 1) * r ^ 3) ≤
      clusterCoordinateDiameter J (fun i => q i 1) hJ + L * r

def separated_cluster_vertical_gap_sharp : Prop :=
  ∀ {m : Masses}, PositiveMasses m →
  ∀ {q : Configuration} {s : ℝ}, IsSolution m s q →
  ∀ (J : Finset Label) (hJ : J.Nonempty), 2 ≤ J.card →
  ∀ {r δ : ℝ}, 0 < r → 0 < δ → r ≤ δ / 2 →
    (∀ i ∈ J, ∀ j ∈ J, dist (q i) (q j) ≤ r) →
    (∀ i ∈ J, ∀ j ∉ J, δ ≤ dist (q i) (q j)) →
    0 < clusterCoordinateDiameter J (fun i => q i 1) hJ →
    cutMass m J * clusterCoordinateDiameter J (fun i => q i 1) hJ /
      (((J.card : ℝ) - 1) * r ^ 3) ≤
      clusterCoordinateDiameter J (fun i => q i 1) hJ +
        (16 * (totalMass m - cutMass m J) / δ ^ 3) * r

def actual_proper_cluster_vertical_gap_sharp : Prop :=
  ∀ {m : Masses}, PositiveMasses m →
  ∀ {q : Configuration} {s : ℝ}, IsSolution m s q →
  ∀ (J : Finset Label) (hJ : J.Nonempty) (hproper : J ≠ Finset.univ),
    2 ≤ J.card → diameter q J hJ ≤ separation q J hJ hproper / 2 →
    0 < clusterCoordinateDiameter J (fun i => q i 1) hJ →
    cutMass m J * clusterCoordinateDiameter J (fun i => q i 1) hJ /
      (((J.card : ℝ) - 1) * diameter q J hJ ^ 3) ≤
      clusterCoordinateDiameter J (fun i => q i 1) hJ +
        (16 * (totalMass m - cutMass m J) / separation q J hJ hproper ^ 3) *
          diameter q J hJ

def actual_full_cluster_vertical_gap_sharp : Prop :=
  ∀ {m : Masses}, PositiveMasses m →
  ∀ {q : Configuration} {s : ℝ}, IsSolution m s q →
    0 < clusterCoordinateDiameter Finset.univ (fun i => q i 1) Finset.univ_nonempty →
    totalMass m * clusterCoordinateDiameter Finset.univ (fun i => q i 1)
      Finset.univ_nonempty /
      (3 * diameter q Finset.univ Finset.univ_nonempty ^ 3) ≤
      clusterCoordinateDiameter Finset.univ (fun i => q i 1) Finset.univ_nonempty

def cluster_vertical_coefficient_three_from_sharp : Prop :=
  ∀ {m : Masses}, PositiveMasses m →
  ∀ {q : Configuration} {s : ℝ}, IsSolution m s q →
  ∀ (J : Finset Label) (hJ : J.Nonempty), 2 ≤ J.card →
  ∀ {r L : ℝ}, 0 < r → 0 ≤ L → LipschitzOnHull m q J L →
    (∀ i ∈ J, ∀ j ∈ J, dist (q i) (q j) ≤ r) →
    0 < clusterCoordinateDiameter J (fun i => q i 1) hJ →
    cutMass m J ≤ 3 * r ^ 3 +
      3 * L * r ^ 4 / clusterCoordinateDiameter J (fun i => q i 1) hJ

end FourBody.SourceGap295.ExpectedSignatures

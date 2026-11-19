import FourBody.ScalarGeometry
import FourBody.Reuse.ConvexPotential
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
The actual Lemma 3.1 scalar energy for arbitrary finite positive masses.
There is no mass normalization, fixed triple coefficient, or Fin 3 expansion.
The ambient chamber is used for the unconstrained variational proof; weighted
centering is recovered from the energy itself in ScalarPotentialMinimizer.
Source proof bodies are staged for the parent's serial Lean verification.
-/

noncomputable section
open scoped BigOperators ContDiff
open Set Filter Topology

namespace FourBody.ScalarMinimizer

abbrev ScalarVector (n : ℕ) := Fin n → ℝ

def scalarPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2)

def ambientChamber (n : ℕ) : Set (ScalarVector n) :=
  {z | StrictMono z}

def scalarQuadraticPotential {n : ℕ} (μ z : ScalarVector n) : ℝ :=
  FourBody.Reuse.quadraticPotential 1 μ z

def scalarPotential {n : ℕ} (μ z : ScalarVector n) : ℝ :=
  scalarQuadraticPotential μ z +
    ∑ p ∈ scalarPairs n, μ p.1 * μ p.2 / |z p.1 - z p.2|

theorem ambientChamber_nonempty (n : ℕ) : (ambientChamber n).Nonempty := by
  refine ⟨fun i => (i.val : ℝ), ?_⟩
  intro i j hij
  change (i.val : ℝ) < (j.val : ℝ)
  exact_mod_cast (show i.val < j.val from hij)

theorem ambientChamber_isOpen (n : ℕ) : IsOpen (ambientChamber n) := by
  change IsOpen {z : ScalarVector n | ∀ i j, i < j → z i < z j}
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro _
  exact isOpen_lt (continuous_apply i) (continuous_apply j)

theorem ambientChamber_convex (n : ℕ) : Convex ℝ (ambientChamber n) := by
  intro x hx y hy a b ha hb hab i j hij
  have hxij : 0 < x j - x i := sub_pos.mpr (hx hij)
  have hyij : 0 < y j - y i := sub_pos.mpr (hy hij)
  change a * x i + b * y i < a * x j + b * y j
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa only [ha0, hb1, zero_mul, one_mul, zero_add] using hy hij
  · have hpos : 0 < a * (x j - x i) + b * (y j - y i) :=
      add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hxij)
        (mul_nonneg hb hyij.le)
    nlinarith

theorem scalarPotential_ordered_formula {n : ℕ} (μ z : ScalarVector n)
    (hz : z ∈ ambientChamber n) :
    scalarPotential μ z = scalarQuadraticPotential μ z +
      ∑ p ∈ scalarPairs n, μ p.1 * μ p.2 / (z p.2 - z p.1) := by
  unfold scalarPotential
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hij : p.1 < p.2 := (Finset.mem_filter.mp hp).2
  rw [abs_sub_comm, abs_of_pos (sub_pos.mpr (hz hij))]

theorem scalarQuadraticPotential_nonneg {n : ℕ} (μ z : ScalarVector n)
    (hμ : ∀ i, 0 ≤ μ i) : 0 ≤ scalarQuadraticPotential μ z := by
  unfold scalarQuadraticPotential FourBody.Reuse.quadraticPotential
  exact mul_nonneg (by norm_num)
    (Finset.sum_nonneg (fun i _ => mul_nonneg (hμ i) (sq_nonneg _)))

theorem scalarPotential_pairSum_nonneg {n : ℕ} (μ z : ScalarVector n)
    (hμ : ∀ i, 0 ≤ μ i) :
    0 ≤ ∑ p ∈ scalarPairs n, μ p.1 * μ p.2 / |z p.1 - z p.2| := by
  exact Finset.sum_nonneg fun p _ =>
    div_nonneg (mul_nonneg (hμ p.1) (hμ p.2)) (abs_nonneg _)

theorem scalarPotential_nonneg {n : ℕ} (μ z : ScalarVector n)
    (hμ : ∀ i, 0 ≤ μ i) : 0 ≤ scalarPotential μ z := by
  exact add_nonneg (scalarQuadraticPotential_nonneg μ z hμ)
    (scalarPotential_pairSum_nonneg μ z hμ)

theorem translate_mem_ambientChamber {n : ℕ} (z : ScalarVector n)
    (hz : z ∈ ambientChamber n) (a : ℝ) :
    (fun i => z i - a) ∈ ambientChamber n := by
  intro i j hij
  exact sub_lt_sub_right (hz hij) a

theorem scalarPotential_translate {n : ℕ} (μ z : ScalarVector n) (a : ℝ) :
    scalarPotential μ (fun i => z i - a) = scalarPotential μ z -
      a * (∑ i, μ i * z i) + (a ^ 2 / 2) * (∑ i, μ i) := by
  have hp :
      (∑ p ∈ scalarPairs n, μ p.1 * μ p.2 / |(z p.1 - a) - (z p.2 - a)|) =
      ∑ p ∈ scalarPairs n, μ p.1 * μ p.2 / |z p.1 - z p.2| := by
    apply Finset.sum_congr rfl
    intro p _
    have he : (z p.1 - a) - (z p.2 - a) = z p.1 - z p.2 := by ring
    rw [he]
  have hq : scalarQuadraticPotential μ (fun i => z i - a) =
      scalarQuadraticPotential μ z - a * (∑ i, μ i * z i) +
        (a ^ 2 / 2) * (∑ i, μ i) := by
    unfold scalarQuadraticPotential FourBody.Reuse.quadraticPotential
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold scalarPotential
  rw [hp, hq]
  ring

theorem scalarPairs_one : scalarPairs 1 = ∅ := by
  ext p
  have hp : p.1 = p.2 := Subsingleton.elim _ _
  simp [scalarPairs, hp]

theorem scalarPotential_one_formula (μ z : ScalarVector 1) :
    scalarPotential μ z = (1 / 2 : ℝ) * (μ 0 * z 0 ^ 2) := by
  simp [scalarPotential, scalarQuadraticPotential, FourBody.Reuse.quadraticPotential,
    scalarPairs_one]

end FourBody.ScalarMinimizer

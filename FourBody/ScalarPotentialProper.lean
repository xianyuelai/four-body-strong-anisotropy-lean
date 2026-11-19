import FourBody.ScalarPotentialConvex
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Tactic.FunProp

/-! Finite-dimensional compact sublevels of the literal scalar energy.
The separation bound controls all original pair collisions; coordinate bounds
control infinity. Nothing here assumes the minimizer or scalar solution. -/
noncomputable section
open scoped BigOperators
open Set Filter Topology

namespace FourBody.ScalarMinimizer

theorem scalarPotential_continuousAt {n : ℕ} (μ z : ScalarVector n)
    (hz : z ∈ ambientChamber n) : ContinuousAt (scalarPotential μ) z := by
  have hpair (p : Fin n × Fin n) (hp : p ∈ scalarPairs n) :
      ContinuousAt (fun w : ScalarVector n => μ p.1 * μ p.2 / |w p.1 - w p.2|) z := by
    have hij : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    exact continuousAt_const.div
      (((continuous_apply p.1).continuousAt.sub (continuous_apply p.2).continuousAt).abs)
      (abs_ne_zero.mpr (ne_of_lt (sub_neg.mpr (hz hij))))
  have hQ : ContinuousAt (scalarQuadraticPotential μ) z := by
    unfold scalarQuadraticPotential FourBody.Reuse.quadraticPotential
    exact continuousAt_const.mul (tendsto_finsetSum Finset.univ
      (fun i _ => continuousAt_const.mul ((continuous_apply i).continuousAt.pow 2)))
  exact hQ.add (tendsto_finsetSum (scalarPairs n) hpair)

theorem scalarPotential_quadratic_term_le {n : ℕ} (μ z : ScalarVector n)
    (hμ : ∀ i, 0 ≤ μ i) (i : Fin n) :
    (1 / 2 : ℝ) * (μ i * z i ^ 2) ≤ scalarPotential μ z := by
  have hsum : μ i * z i ^ 2 ≤ ∑ j, μ j * z j ^ 2 :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hμ j) (sq_nonneg _)) (Finset.mem_univ i)
  have hQ : (1 / 2 : ℝ) * (μ i * z i ^ 2) ≤ scalarQuadraticPotential μ z :=
    mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hP := scalarPotential_pairSum_nonneg μ z hμ
  unfold scalarPotential
  linarith

theorem scalarPotential_pair_term_le {n : ℕ} (μ z : ScalarVector n)
    (hμ : ∀ i, 0 ≤ μ i) (i j : Fin n) (hij : i < j) :
    μ i * μ j / |z i - z j| ≤ scalarPotential μ z := by
  have hp : (i, j) ∈ scalarPairs n :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
  have hsum : μ i * μ j / |z i - z j| ≤
      ∑ p ∈ scalarPairs n, μ p.1 * μ p.2 / |z p.1 - z p.2| :=
    Finset.single_le_sum
      (f := fun p : Fin n × Fin n => μ p.1 * μ p.2 / |z p.1 - z p.2|)
      (fun p _ => div_nonneg (mul_nonneg (hμ p.1) (hμ p.2)) (abs_nonneg _)) hp
  have hQ := scalarQuadraticPotential_nonneg μ z hμ
  unfold scalarPotential
  linarith

theorem scalarPotential_sublevel_coordinate_bounds {n : ℕ} (μ z : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (C : ℝ) (hC : 0 < C)
    (hlevel : scalarPotential μ z ≤ C) :
    ∀ i, |z i| ≤ 1 + 2 * C / μ i := by
  intro i
  have hterm := (scalarPotential_quadratic_term_le μ z (fun j => (hμ j).le) i).trans hlevel
  have hsq : z i ^ 2 ≤ 2 * C / μ i :=
    (le_div_iff₀ (hμ i)).mpr (by nlinarith)
  have hB : 0 ≤ 2 * C / μ i :=
    div_nonneg (mul_nonneg (by norm_num) hC.le) (hμ i).le
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (z i - 1), sq_nonneg (z i + 1)]

theorem scalarPotential_sublevel_gap_bounds {n : ℕ} (μ z : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (hz : z ∈ ambientChamber n) (C : ℝ) (hC : 0 < C)
    (hlevel : scalarPotential μ z ≤ C) :
    ∀ i j, i < j → μ i * μ j / C ≤ z j - z i := by
  intro i j hij
  have hterm := (scalarPotential_pair_term_le μ z (fun k => (hμ k).le) i j hij).trans hlevel
  rw [abs_sub_comm, abs_of_pos (sub_pos.mpr (hz hij))] at hterm
  exact (div_le_iff₀ hC).mpr
    (by simpa only [mul_comm] using (div_le_iff₀ (sub_pos.mpr (hz hij))).mp hterm)

def scalarSeparationSet {n : ℕ} (μ : ScalarVector n) (C : ℝ) : Set (ScalarVector n) :=
  {z | ∀ i j, i < j → μ i * μ j / C ≤ z j - z i}

theorem scalarSeparationSet_isClosed {n : ℕ} (μ : ScalarVector n) (C : ℝ) :
    IsClosed (scalarSeparationSet μ C) := by
  simp only [scalarSeparationSet, Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro _
  exact isClosed_le continuous_const
    ((continuous_apply j : Continuous (fun z : ScalarVector n => z j)).sub (continuous_apply i))

theorem scalarSeparationSet_subset_chamber {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (C : ℝ) (hC : 0 < C) :
    scalarSeparationSet μ C ⊆ ambientChamber n := by
  intro z hz i j hij
  exact sub_pos.mp ((div_pos (mul_pos (hμ i) (hμ j)) hC).trans_le (hz i j hij))

theorem scalarPotential_compact_sublevel {n : ℕ} (μ : ScalarVector n)
    (hμ : ∀ i, 0 < μ i) (c : ℝ) :
    IsCompact {z : ScalarVector n | z ∈ ambientChamber n ∧ scalarPotential μ z ≤ c} := by
  let C := max c 1
  have hC : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hcC : c ≤ C := le_max_left _ _
  let S : Set (ScalarVector n) := {z | z ∈ ambientChamber n ∧ scalarPotential μ z ≤ c}
  let K := scalarSeparationSet μ C
  have hSK : S ⊆ K := by
    intro z hz
    exact scalarPotential_sublevel_gap_bounds μ z hμ hz.1 C hC (hz.2.trans hcC)
  have hKch : K ⊆ ambientChamber n := scalarSeparationSet_subset_chamber μ hμ C hC
  have hcont : ContinuousOn (scalarPotential μ) K :=
    fun z hz => (scalarPotential_continuousAt μ z (hKch hz)).continuousWithinAt
  have hclosed : IsClosed S := by
    have he : S = K ∩ (scalarPotential μ) ⁻¹' Iic c := by
      ext z
      exact ⟨fun hz => ⟨hSK hz, hz.2⟩, fun hz => ⟨hKch hz.1, hz.2⟩⟩
    rw [he]
    exact hcont.preimage_isClosed_of_isClosed (scalarSeparationSet_isClosed μ C) isClosed_Iic
  have hbox : IsCompact (Set.univ.pi (fun i : Fin n =>
      Icc (-(1 + 2 * C / μ i)) (1 + 2 * C / μ i))) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  apply hbox.of_isClosed_subset hclosed
  intro z hz i _
  exact abs_le.mp (scalarPotential_sublevel_coordinate_bounds μ z hμ C hC (hz.2.trans hcC) i)

end FourBody.ScalarMinimizer

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
The algebraic step following equation `eq:vertical-pairing` in the frozen
v2 manuscript (TeX lines 473--478), SHA256
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

The finite pair set contains each pair exactly in its `i < j` orientation.
Distances below are those of the genuine Euclidean plane, not the sup norm
on a raw function type. The cardinality `n` is arbitrary; no assumption
`2 <= n` is added, so the singleton internal block is included.

These results establish only that zero vertical pair energy and zero mass
mean force the vertical coordinates to vanish. They do not establish the
subsequence construction or the limiting force equation in Proposition 3.2.
-/

noncomputable section

open scoped BigOperators

namespace FourBody.VerticalEnergy

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Each unordered pair is recorded once, in increasing index order. -/
def orderedPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2)

@[simp] theorem mem_orderedPairs {n : ℕ} (i j : Fin n) :
    (i, j) ∈ orderedPairs n ↔ i < j := by
  simp [orderedPairs]

/-- An `i < j` sum, with a strictly positive coefficient for every pair. -/
def pairEnergy {n : ℕ} (w : Fin n → Fin n → ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ p ∈ orderedPairs n, w p.1 p.2 * (v p.1 - v p.2) ^ 2

/-- A zero sum of positive weighted squared differences makes all values equal. -/
theorem constant_of_pairEnergy_eq_zero {n : ℕ}
    (w : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hw : ∀ i j, i < j → 0 < w i j)
    (henergy : pairEnergy w v = 0) :
    ∀ i j, v i = v j := by
  have hnonneg : ∀ p ∈ orderedPairs n,
      0 ≤ w p.1 p.2 * (v p.1 - v p.2) ^ 2 := by
    intro p hp
    have hp' : p.1 < p.2 := by
      simpa [orderedPairs] using hp
    exact mul_nonneg (hw p.1 p.2 hp').le (sq_nonneg _)
  have hzero : ∀ p ∈ orderedPairs n,
      w p.1 p.2 * (v p.1 - v p.2) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp henergy
  have hordered : ∀ i j, i < j → v i = v j := by
    intro i j hij
    have hterm : w i j * (v i - v j) ^ 2 = 0 :=
      hzero (i, j) ((mem_orderedPairs i j).mpr hij)
    have hsquare : (v i - v j) ^ 2 = 0 :=
      (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hw i j hij))
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  intro i j
  rcases lt_trichotomy i j with hij | hij | hji
  · exact hordered i j hij
  · rw [hij]
  · exact (hordered j i hji).symm

/-- A mass-centered constant vector is zero, including a one-point block. -/
theorem zero_of_constant_of_centered {n : ℕ}
    (μ v : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i)
    (hconstant : ∀ i j, v i = v j)
    (hcenter : ∑ i, μ i * v i = 0) :
    ∀ i, v i = 0 := by
  intro i
  have hmass : 0 < ∑ j, μ j :=
    Finset.sum_pos (fun j _ => hμ j) ⟨i, Finset.mem_univ i⟩
  have hproduct : (∑ j, μ j) * v i = 0 := by
    calc
      (∑ j, μ j) * v i = ∑ j, μ j * v i := by
        rw [Finset.sum_mul]
      _ = ∑ j, μ j * v j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hconstant j i]
      _ = 0 := hcenter
  exact (mul_eq_zero.mp hproduct).resolve_left (ne_of_gt hmass)

/-- Positive pair weights and centering together eliminate the constant kernel. -/
theorem zero_of_pairEnergy_eq_zero {n : ℕ}
    (μ : Fin n → ℝ) (w : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i)
    (hw : ∀ i j, i < j → 0 < w i j)
    (hcenter : ∑ i, μ i * v i = 0)
    (henergy : pairEnergy w v = 0) :
    ∀ i, v i = 0 :=
  zero_of_constant_of_centered μ v hμ
    (constant_of_pairEnergy_eq_zero w v hw henergy) hcenter

/-- The actual coefficients in `eq:vertical-pairing` are positive. -/
theorem distance_weight_pos {n : ℕ}
    (μ : Fin n → ℝ) (P : Fin n → Plane)
    (hμ : ∀ i, 0 < μ i)
    (hcollision : ∀ i j, i ≠ j → P i ≠ P j)
    (i j : Fin n) (hij : i < j) :
    0 < μ i * μ j / dist (P i) (P j) ^ 3 := by
  have hdistance : 0 < dist (P i) (P j) :=
    dist_pos.mpr (hcollision i j (ne_of_lt hij))
  exact div_pos (mul_pos (hμ i) (hμ j)) (pow_pos hdistance 3)

/-- Zero vertical energy for a collision-free Euclidean configuration implies zero
vertical values once their mass mean is zero. -/
theorem zero_of_distance_energy_eq_zero {n : ℕ}
    (μ : Fin n → ℝ) (P : Fin n → Plane) (v : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i)
    (hcollision : ∀ i j, i ≠ j → P i ≠ P j)
    (hcenter : ∑ i, μ i * v i = 0)
    (henergy : (∑ p ∈ orderedPairs n,
      μ p.1 * μ p.2 * (v p.1 - v p.2) ^ 2 /
        dist (P p.1) (P p.2) ^ 3) = 0) :
    ∀ i, v i = 0 := by
  let w : Fin n → Fin n → ℝ :=
    fun i j => μ i * μ j / dist (P i) (P j) ^ 3
  have hw : ∀ i j, i < j → 0 < w i j := by
    intro i j hij
    exact distance_weight_pos μ P hμ hcollision i j hij
  apply zero_of_pairEnergy_eq_zero μ w v hμ hw hcenter
  calc
    pairEnergy w v = ∑ p ∈ orderedPairs n,
        μ p.1 * μ p.2 * (v p.1 - v p.2) ^ 2 /
          dist (P p.1) (P p.2) ^ 3 := by
      unfold pairEnergy
      apply Finset.sum_congr rfl
      intro p _
      dsimp [w]
      ring
    _ = 0 := henergy

/-- The precise vertical-coordinate conclusion used after equation
`eq:vertical-pairing`, with `v_i = P_i 1`. -/
theorem vertical_coordinates_eq_zero {n : ℕ}
    (μ : Fin n → ℝ) (P : Fin n → Plane)
    (hμ : ∀ i, 0 < μ i)
    (hcollision : ∀ i j, i ≠ j → P i ≠ P j)
    (hcenter : ∑ i, μ i * P i 1 = 0)
    (henergy : (∑ p ∈ orderedPairs n,
      μ p.1 * μ p.2 * (P p.1 1 - P p.2 1) ^ 2 /
        dist (P p.1) (P p.2) ^ 3) = 0) :
    ∀ i, P i 1 = 0 :=
  zero_of_distance_energy_eq_zero μ P (fun i => P i 1)
    hμ hcollision hcenter henergy

/-- The next sentence of the manuscript: once the vertical coordinates are
zero, noncollision makes the horizontal coordinates distinct. -/
theorem horizontal_injective_of_vertical_zero {n : ℕ}
    (P : Fin n → Plane)
    (hcollision : ∀ i j, i ≠ j → P i ≠ P j)
    (hvertical : ∀ i, P i 1 = 0) :
    Function.Injective (fun i => P i 0) := by
  intro i j hij
  by_contra hne
  apply hcollision i j hne
  ext k
  fin_cases k
  · exact hij
  · exact (hvertical i).trans (hvertical j).symm

end FourBody.VerticalEnergy

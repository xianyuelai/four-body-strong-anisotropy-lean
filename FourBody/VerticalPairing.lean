import FourBody.VerticalEnergy
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
The exact finite-sum pairing at v2 TeX lines 471--478. In contrast to the
preceding algebra module, the concluding theorem here starts from the
individual vertical force equations and proves the zero-energy identity.
The source's limit construction and passage to those equations are still
separate obligations.
-/

noncomputable section

open scoped BigOperators

namespace FourBody.VerticalEnergy

/-- Pair any finite double sum with a zero diagonal in its `i < j` order. -/
theorem sum_eq_ordered_pair_sum {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hdiag : ∀ i, f i i = 0) :
    (∑ p : Fin n × Fin n, f p.1 p.2) =
      ∑ p ∈ orderedPairs n, (f p.1 p.2 + f p.2 p.1) := by
  have hswap :
      (∑ p : Fin n × Fin n, if p.1 < p.2 then f p.2 p.1 else 0) =
        ∑ p : Fin n × Fin n, if p.2 < p.1 then f p.1 p.2 else 0 := by
    exact Fintype.sum_equiv (Equiv.prodComm (Fin n) (Fin n)) _ _
      (fun p => rfl)
  symm
  calc
    (∑ p ∈ orderedPairs n, (f p.1 p.2 + f p.2 p.1)) =
        (∑ p : Fin n × Fin n, if p.1 < p.2 then f p.1 p.2 else 0) +
          ∑ p : Fin n × Fin n, if p.1 < p.2 then f p.2 p.1 else 0 := by
      rw [orderedPairs, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p.1 < p.2 <;> simp [hp]
    _ = (∑ p : Fin n × Fin n, if p.1 < p.2 then f p.1 p.2 else 0) +
          ∑ p : Fin n × Fin n, if p.2 < p.1 then f p.1 p.2 else 0 := by
      rw [hswap]
    _ = ∑ p : Fin n × Fin n, f p.1 p.2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      rcases lt_trichotomy p.1 p.2 with hij | hij | hji
      · simp [hij, not_lt_of_ge hij.le]
      · simp [hij, hdiag]
      · simp [hji, not_lt_of_ge hji.le]

/-- The vertical Newtonian force, with the self term explicitly omitted. -/
def verticalForce {n : ℕ} (μ : Fin n → ℝ)
    (P : Fin n → Plane) (v : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i,
    μ j * (v i - v j) / dist (P i) (P j) ^ 3

/-- Exact mass-weighted pairing of the individual vertical forces. -/
theorem vertical_force_pairing {n : ℕ}
    (μ : Fin n → ℝ) (P : Fin n → Plane) (v : Fin n → ℝ) :
    (∑ i, μ i * v i * verticalForce μ P v i) =
      ∑ p ∈ orderedPairs n,
        μ p.1 * μ p.2 * (v p.1 - v p.2) ^ 2 /
          dist (P p.1) (P p.2) ^ 3 := by
  let f : Fin n → Fin n → ℝ := fun i j =>
    μ i * v i * (μ j * (v i - v j) / dist (P i) (P j) ^ 3)
  have hdiag : ∀ i, f i i = 0 := by
    intro i
    simp [f]
  have hfull : (∑ i, μ i * v i * verticalForce μ P v i) =
      ∑ p : Fin n × Fin n, f p.1 p.2 := by
    calc
      (∑ i, μ i * v i * verticalForce μ P v i) = ∑ i, ∑ j, f i j := by
        apply Finset.sum_congr rfl
        intro i _
        unfold verticalForce
        rw [Finset.mul_sum]
        exact Finset.sum_erase _ (hdiag i)
      _ = ∑ p : Fin n × Fin n, f p.1 p.2 := by
        simpa using (Finset.sum_product' (Finset.univ : Finset (Fin n))
          (Finset.univ : Finset (Fin n)) f).symm
  rw [hfull, sum_eq_ordered_pair_sum f hdiag]
  apply Finset.sum_congr rfl
  intro p _
  dsimp [f]
  rw [dist_comm (P p.2) (P p.1)]
  ring

/-- The manuscript's zero-energy identity follows from the vertical equations. -/
theorem distance_energy_eq_zero_of_vertical_force_zero {n : ℕ}
    (μ : Fin n → ℝ) (P : Fin n → Plane) (v : Fin n → ℝ)
    (hforce : ∀ i, verticalForce μ P v i = 0) :
    (∑ p ∈ orderedPairs n,
      μ p.1 * μ p.2 * (v p.1 - v p.2) ^ 2 /
        dist (P p.1) (P p.2) ^ 3) = 0 := by
  rw [← vertical_force_pairing μ P v]
  simp [hforce]

/-- From the actual individual vertical equations and centering, all vertical
values vanish; the energy conclusion is derived within the proof. -/
theorem zero_of_vertical_force_zero {n : ℕ}
    (μ : Fin n → ℝ) (P : Fin n → Plane) (v : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i)
    (hcollision : ∀ i j, i ≠ j → P i ≠ P j)
    (hcenter : ∑ i, μ i * v i = 0)
    (hforce : ∀ i, verticalForce μ P v i = 0) :
    ∀ i, v i = 0 :=
  zero_of_distance_energy_eq_zero μ P v hμ hcollision hcenter
    (distance_energy_eq_zero_of_vertical_force_zero μ P v hforce)

/-- The source-coordinate instance of the force-equation conclusion. -/
theorem vertical_coordinates_eq_zero_of_force_zero {n : ℕ}
    (μ : Fin n → ℝ) (P : Fin n → Plane)
    (hμ : ∀ i, 0 < μ i)
    (hcollision : ∀ i j, i ≠ j → P i ≠ P j)
    (hcenter : ∑ i, μ i * P i 1 = 0)
    (hforce : ∀ i, verticalForce μ P (fun j => P j 1) i = 0) :
    ∀ i, P i 1 = 0 :=
  zero_of_vertical_force_zero μ P (fun i => P i 1)
    hμ hcollision hcenter hforce

end FourBody.VerticalEnergy

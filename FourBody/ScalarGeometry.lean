import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Exact elementary pieces of v2 Lemma 3.1 (lines 350--394).
The standard increasing chamber represents any prescribed label order
after reading the labels in that order. This module does not assert the
minimizer's existence or uniqueness when n >= 2.
-/

noncomputable section
open scoped BigOperators
namespace FourBody.ScalarGeometry

abbrev ScalarConfiguration (n : ℕ) := Fin n → ℝ

def scalarCenterLM {n : ℕ} (μ : Fin n → ℝ) : ScalarConfiguration n →ₗ[ℝ] ℝ where
  toFun z := ∑ i, μ i * z i
  map_add' z t := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a z := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

def ScalarW {n : ℕ} (μ : Fin n → ℝ) : Submodule ℝ (ScalarConfiguration n) :=
  (scalarCenterLM μ).ker

def chamber {n : ℕ} (μ : Fin n → ℝ) : Set (ScalarW μ) :=
  {z | StrictMono (fun i => (z : ScalarConfiguration n) i)}

def scalarForce {n : ℕ} (μ : Fin n → ℝ) (z : ScalarConfiguration n) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, μ j * (z i - z j) / |z i - z j| ^ 3

def IsScalarSolution {n : ℕ} (μ : Fin n → ℝ) (z : ScalarConfiguration n) : Prop :=
  Function.Injective z ∧ ∀ i, scalarForce μ z i = z i

theorem totalMass_pos {n : ℕ} (hn : 0 < n) (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) : 0 < ∑ i, μ i := by
  exact Finset.sum_pos (fun i _ => hμ i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

/-- A centered translate of the index positions gives a point of every
standard ordered chamber; n = 0 is also treated without division assumptions. -/
theorem chamber_nonempty {n : ℕ} (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i) :
    (chamber μ).Nonempty := by
  by_cases hn : n = 0
  · subst n
    refine ⟨0, ?_⟩
    intro i
    exact Fin.elim0 i
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hmass : (∑ i, μ i) ≠ 0 := ne_of_gt (totalMass_pos hnpos μ hμ)
    let a : ℝ := (∑ i, μ i * (i.val : ℝ)) / ∑ i, μ i
    let z : ScalarConfiguration n := fun i => (i.val : ℝ) - a
    have hcenter : z ∈ ScalarW μ := by
      change (∑ i, μ i * ((i.val : ℝ) - a)) = 0
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      dsimp [a]
      field_simp
      ring
    refine ⟨⟨z, hcenter⟩, ?_⟩
    intro i j hij
    change (i.val : ℝ) - a < (j.val : ℝ) - a
    exact sub_lt_sub_right (by exact_mod_cast hij) a

theorem chamber_convex {n : ℕ} (μ : Fin n → ℝ) : Convex ℝ (chamber μ) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab i j hij
  have hxi : (x : ScalarConfiguration n) i < (x : ScalarConfiguration n) j := hx hij
  have hyi : (y : ScalarConfiguration n) i < (y : ScalarConfiguration n) j := hy hij
  change a * (x : ScalarConfiguration n) i + b * (y : ScalarConfiguration n) i <
    a * (x : ScalarConfiguration n) j + b * (y : ScalarConfiguration n) j
  rcases lt_or_eq_of_le ha with hapos | hazero
  · have hp := mul_pos hapos (sub_pos.mpr hxi)
    have hn := mul_nonneg hb (sub_pos.mpr hyi).le
    nlinarith
  · have hbone : b = 1 := by linarith
    rw [← hazero, hbone]
    simpa using hyi

/-- The singleton centered space is exactly zero, as required for k = 1
outer centers and for singleton internal blocks. -/
theorem singleton_center_eq_zero (μ : Fin 1 → ℝ) (hμ : ∀ i, 0 < μ i)
    (z : ScalarW μ) : z = 0 := by
  have hz : μ 0 * (z : ScalarConfiguration 1) 0 = 0 := by
    simpa [ScalarW, scalarCenterLM, LinearMap.mem_ker] using z.property
  have hz0 : (z : ScalarConfiguration 1) 0 = 0 :=
    (mul_eq_zero.mp hz).resolve_left (ne_of_gt (hμ 0))
  apply Subtype.ext
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  exact hz0

theorem singleton_is_solution (μ : Fin 1 → ℝ) :
    IsScalarSolution μ (0 : ScalarConfiguration 1) := by
  constructor
  · intro i j _
    exact Subsingleton.elim i j
  · intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    simp [scalarForce]

theorem singleton_solution_unique (μ : Fin 1 → ℝ) :
    ∃! z : ScalarConfiguration 1, IsScalarSolution μ z := by
  refine ⟨0, singleton_is_solution μ, ?_⟩
  intro z hz
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  have hforce := hz.2 0
  simpa [scalarForce] using hforce.symm

end FourBody.ScalarGeometry

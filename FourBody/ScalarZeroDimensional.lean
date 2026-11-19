import FourBody.ScalarGeometry
import FourBody.Operators

/-!
STATIC source supplement S3-U18. Fin 0 and Fin 1 are explicit, with
their actual centered points zero and their actual L the automorphism of
the zero space. No nonzero tangent or nonexistent distinct pair is selected.
-/

set_option autoImplicit false
noncomputable section
namespace FourBody.ScalarSupplement

open ScalarGeometry GeneralOperator

theorem empty_scalar_centered_eq_zero (μ : Fin 0 → ℝ) (z : ScalarW μ) : z = 0 := by
  apply Subtype.ext
  funext i
  exact Fin.elim0 i

theorem empty_scalar_solution_existsUnique (μ : Fin 0 → ℝ) :
    ∃! z : ScalarConfiguration 0, IsScalarSolution μ z := by
  refine ⟨0, ?_, ?_⟩
  · constructor
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
  · intro z _
    funext i
    exact Fin.elim0 i

theorem empty_operator_centered_eq_zero (μ : Fin 0 → ℝ)
    (z : centeredSpace μ) : z = 0 := by
  apply Subtype.ext
  funext i
  exact Fin.elim0 i

theorem singleton_operator_centered_eq_zero (μ : Fin 1 → ℝ)
    (hμ : ∀ i, 0 < μ i) (z : centeredSpace μ) : z = 0 := by
  apply centered_constant_eq_zero μ hμ z
  intro i j
  exact congrArg (fun k => z.val k) (Subsingleton.elim i j)

theorem empty_centeredLaplacian_eq_zero (μ : Fin 0 → ℝ)
    (c : Fin 0 → Fin 0 → ℝ) (hc : SymmetricCoefficients c) :
    centeredLaplacianCLM μ c hc = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  exact empty_operator_centered_eq_zero μ (centeredLaplacianCLM μ c hc z)

theorem singleton_centeredLaplacian_eq_zero (μ : Fin 1 → ℝ)
    (hμ : ∀ i, 0 < μ i) (c : Fin 1 → Fin 1 → ℝ)
    (hc : SymmetricCoefficients c) : centeredLaplacianCLM μ c hc = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  exact singleton_operator_centered_eq_zero μ hμ (centeredLaplacianCLM μ c hc z)

theorem empty_centeredLaplacian_zero_space_automorphism (μ : Fin 0 → ℝ)
    (c : Fin 0 → Fin 0 → ℝ) (hc : SymmetricCoefficients c) :
    (centeredLaplacianCLM μ c hc).IsInvertible := by
  refine ⟨ContinuousLinearEquiv.refl ℝ (centeredSpace μ), ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  change z = centeredLaplacianCLM μ c hc z
  exact (empty_operator_centered_eq_zero μ z).trans
    (empty_operator_centered_eq_zero μ (centeredLaplacianCLM μ c hc z)).symm

theorem singleton_centeredLaplacian_zero_space_automorphism (μ : Fin 1 → ℝ)
    (hμ : ∀ i, 0 < μ i) (c : Fin 1 → Fin 1 → ℝ)
    (hc : SymmetricCoefficients c) : (centeredLaplacianCLM μ c hc).IsInvertible := by
  refine ⟨ContinuousLinearEquiv.refl ℝ (centeredSpace μ), ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  change z = centeredLaplacianCLM μ c hc z
  exact (singleton_operator_centered_eq_zero μ hμ z).trans
    (singleton_operator_centered_eq_zero μ hμ (centeredLaplacianCLM μ c hc z)).symm

theorem empty_inverseCubeL_zero_space_automorphism (μ z : Fin 0 → ℝ) :
    (centeredLaplacianCLM μ (inverseCubeCoefficient z)
      (inverseCubeCoefficient_symmetric z)).IsInvertible :=
  empty_centeredLaplacian_zero_space_automorphism μ _ _

theorem singleton_inverseCubeL_zero_space_automorphism (μ z : Fin 1 → ℝ)
    (hμ : ∀ i, 0 < μ i) :
    (centeredLaplacianCLM μ (inverseCubeCoefficient z)
      (inverseCubeCoefficient_symmetric z)).IsInvertible :=
  singleton_centeredLaplacian_zero_space_automorphism μ hμ _ _

end FourBody.ScalarSupplement

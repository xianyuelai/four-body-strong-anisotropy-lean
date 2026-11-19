import FourBody.CoordinateProduct
import FourBody.HorizontalNewtonDerivative
import FourBody.ScalarPotentialJacobian
import FourBody.BlowupZero
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Tactic.Module

/-!
The actual full seed derivative of h ↦ F(0,h), with every sign retained.
The actual coordinate kernel is decomposed using CoordinateProduct, and
Newton derivatives are obtained from HorizontalNewtonDerivative, not from
a Jacobian hypothesis. The two scalar residual derivatives have the
opposite sign to ScalarPotentialJacobian.normalizedScalarResidual.

The resulting four block types are -Id, -(Id+2L₀), -(Id+2Lₐ), Lₐ.
The formula for every arbitrary tangent vector displays all mixed blocks
as zero. Positivity supplies actual continuous linear equivalences for
each block and their finite product. The final derivative is conjugated
back to the actual constraint kernel, without changing its dimension or
introducing an unproved analytic interface.

Frozen v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
Static proof candidate; no Lean build or axiom audit has been run for it.
-/

noncomputable section
open scoped BigOperators
open Filter Set Topology
namespace FourBody.SeedJacobian

open GeneralOperator
open CoordinateProduct

abbrev ScalarSpace {n : ℕ} (μ : Fin n → ℝ) := ScalarGeometry.ScalarW μ
abbrev ScalarPair {n : ℕ} (μ : Fin n → ℝ) := ScalarSpace μ × ScalarSpace μ

def distanceCoefficient {n : ℕ} (q : HorizontalNewton.ConfigurationN n)
    (i j : Fin n) : ℝ := (dist (q i) (q j) ^ 3)⁻¹

theorem distanceCoefficient_symmetric {n : ℕ} (q : HorizontalNewton.ConfigurationN n) :
    SymmetricCoefficients (distanceCoefficient q) := by
  intro i j
  simp only [distanceCoefficient, dist_comm]

/-- The true total Newton field, also at collisions in Lean's total definition,
has each axis equal to the exact weighted Laplacian with distance coefficients. -/
theorem totalNewtonField_axis_eq_laplacian {n : ℕ} (μ : Fin n → ℝ)
    (q : HorizontalNewton.ConfigurationN n) (k : Axis) :
    HorizontalNewton.axisCoordinates (HorizontalNewton.totalNewtonField μ q) k =
      laplacian μ (distanceCoefficient q) (HorizontalNewton.axisCoordinates q k) := by
  classical
  funext i
  change (HorizontalNewton.totalNewtonField μ q i) k = _
  rw [HorizontalNewton.totalNewtonField, HorizontalNewton.plane_sum_apply, laplacian_apply]
  simp only [Reuse.physicalNewtonForce, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul, div_eq_mul_inv, HorizontalNewton.axisCoordinates, distanceCoefficient]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  simp only [sub_self, mul_zero, sub_zero]

theorem totalNewtonField_axis_centered {n : ℕ} (μ : Fin n → ℝ)
    (q : HorizontalNewton.ConfigurationN n) (k : Axis) :
    HorizontalNewton.axisCoordinates (HorizontalNewton.totalNewtonField μ q) k ∈
      ScalarGeometry.ScalarW μ := by
  change scalarCenter μ
    (HorizontalNewton.axisCoordinates (HorizontalNewton.totalNewtonField μ q) k) = 0
  rw [totalNewtonField_axis_eq_laplacian]
  exact scalarCenter_laplacian μ (distanceCoefficient q)
    (distanceCoefficient_symmetric q) _

def newtonAxes {n : ℕ} (μ : Fin n → ℝ) (u : ScalarPair μ) : ScalarPair μ :=
  (⟨HorizontalNewton.axisCoordinates
      (HorizontalNewton.totalNewtonField μ (HorizontalNewton.centeredEmbedding μ u)) 0,
    totalNewtonField_axis_centered μ (HorizontalNewton.centeredEmbedding μ u) 0⟩,
   ⟨HorizontalNewton.axisCoordinates
      (HorizontalNewton.totalNewtonField μ (HorizontalNewton.centeredEmbedding μ u)) 1,
    totalNewtonField_axis_centered μ (HorizontalNewton.centeredEmbedding μ u) 1⟩)

theorem newtonAxes_embedding {n : ℕ} (μ : Fin n → ℝ) (u : ScalarPair μ) :
    HorizontalNewton.centeredEmbedding μ (newtonAxes μ u) =
      HorizontalNewton.totalNewtonField μ (HorizontalNewton.centeredEmbedding μ u) := by
  funext i
  ext k
  fin_cases k <;> rfl

def scalarL {n : ℕ} (μ : Fin n → ℝ) (z : ScalarSpace μ) :
    ScalarSpace μ →L[ℝ] ScalarSpace μ :=
  centeredLaplacianCLM μ (inverseCubeCoefficient z.val) (inverseCubeCoefficient_symmetric z.val)

def scalarShift {n : ℕ} (μ : Fin n → ℝ) (z : ScalarSpace μ) :
    ScalarSpace μ →L[ℝ] ScalarSpace μ :=
  shiftedCenteredLaplacianCLM μ (inverseCubeCoefficient z.val)
    (inverseCubeCoefficient_symmetric z.val)

def newtonAxesDerivative {n : ℕ} (μ : Fin n → ℝ) (z : ScalarSpace μ) :
    ScalarPair μ →L[ℝ] ScalarPair μ :=
  ((-2 : ℝ) • scalarL μ z).prodMap (scalarL μ z)

theorem centeredEmbedding_isEmbedding {n : ℕ} (μ : Fin n → ℝ) :
    Topology.IsEmbedding (HorizontalNewton.centeredEmbedding μ) := by
  have hinj : Function.Injective (HorizontalNewton.centeredEmbedding μ) := by
    intro u v huv
    apply Prod.ext
    · apply Subtype.ext
      funext i
      simpa only [HorizontalNewton.centeredEmbedding_apply, HorizontalNewton.xy_x] using
        congrArg (fun q : HorizontalNewton.ConfigurationN n => q i 0) huv
    · apply Subtype.ext
      funext i
      simpa only [HorizontalNewton.centeredEmbedding_apply, HorizontalNewton.xy_y] using
        congrArg (fun q : HorizontalNewton.ConfigurationN n => q i 1) huv
  exact (LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr hinj :
      (HorizontalNewton.centeredEmbedding μ).toLinearMap.ker = ⊥)).isEmbedding

theorem newtonAxes_hasFDerivAt {n : ℕ} (μ : Fin n → ℝ) (z : ScalarSpace μ)
    (hz : Function.Injective z.val) :
    HasFDerivAt (newtonAxes μ) (newtonAxesDerivative μ z) (z, 0) := by
  have hd := HorizontalNewton.centeredSlice_hasFDerivAt μ z hz
  have hmap : (HorizontalNewton.horizontalBlockDerivative μ z.val).comp
      (HorizontalNewton.centeredEmbedding μ) =
      (HorizontalNewton.centeredEmbedding μ).comp (newtonAxesDerivative μ z) := by
    apply ContinuousLinearMap.ext
    intro u
    exact HorizontalNewton.horizontalBlockDerivative_centered μ z.val u.1 u.2
  have hc : ContinuousAt (newtonAxes μ) (z, 0) := by
    have hx := (HorizontalNewton.axisProjection (ι := Fin n) 0).continuous.continuousAt.comp
      hd.continuousAt
    have hy := (HorizontalNewton.axisProjection (ι := Fin n) 1).continuous.continuousAt.comp
      hd.continuousAt
    exact (hx.codRestrict (fun u => totalNewtonField_axis_centered μ
      (HorizontalNewton.centeredEmbedding μ u) 0)).prodMk
        (hy.codRestrict (fun u => totalNewtonField_axis_centered μ
          (HorizontalNewton.centeredEmbedding μ u) 1))
  exact HasFDerivAt.of_comp_of_isEmbedding hc
    (HorizontalNewton.centeredEmbedding μ).hasFDerivAt
    (centeredEmbedding_isEmbedding μ) (hd.congr_fderiv hmap)
    (Filter.Eventually.of_forall (fun u => newtonAxes_embedding μ u))

/-- The actual internal zero-scale residual has no -v term. -/
def internalResidual {n : ℕ} (μ : Fin n → ℝ) (u : ScalarPair μ) : ScalarPair μ :=
  ((newtonAxes μ u).1 - u.1, (newtonAxes μ u).2)

def internalDerivative {n : ℕ} (μ : Fin n → ℝ) (z : ScalarSpace μ) :
    ScalarPair μ →L[ℝ] ScalarPair μ :=
  (-(scalarShift μ z)).prodMap (scalarL μ z)

theorem internalResidual_hasFDerivAt {n : ℕ} (μ : Fin n → ℝ) (z : ScalarSpace μ)
    (hz : Function.Injective z.val) :
    HasFDerivAt (internalResidual μ) (internalDerivative μ z) (z, 0) := by
  have hd := newtonAxes_hasFDerivAt μ z hz
  have h := (hd.fst.sub (ContinuousLinearMap.fst ℝ (ScalarSpace μ)
    (ScalarSpace μ)).hasFDerivAt).prodMk hd.snd
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro u
  apply Prod.ext
  · change (-2 : ℝ) • scalarL μ z u.1 - u.1 =
      -(u.1 + (2 : ℝ) • scalarL μ z u.1)
    module
  · rfl

def negativeEquivalence {n : ℕ} (μ : Fin n → ℝ) : ScalarSpace μ ≃L[ℝ] ScalarSpace μ :=
  (LinearEquiv.neg ℝ : ScalarSpace μ ≃ₗ[ℝ] ScalarSpace μ).toContinuousLinearEquiv

theorem neg_isInvertible {n : ℕ} (μ : Fin n → ℝ)
    (A : ScalarSpace μ →L[ℝ] ScalarSpace μ) (hA : A.IsInvertible) :
    (-A).IsInvertible := by
  obtain ⟨e, he⟩ := hA
  refine ⟨e.trans (negativeEquivalence μ), ?_⟩
  apply ContinuousLinearMap.ext
  intro u
  exact congrArg (fun B : ScalarSpace μ →L[ℝ] ScalarSpace μ => -(B u)) he

theorem scalarL_isInvertible {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (z : ScalarSpace μ) (hz : Function.Injective z.val) :
    (scalarL μ z).IsInvertible :=
  inverseCube_centeredLaplacian_isInvertible μ hμ z.val hz

theorem scalarShift_isInvertible {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (z : ScalarSpace μ) (hz : Function.Injective z.val) :
    (scalarShift μ z).IsInvertible :=
  inverseCube_shiftedCenteredLaplacian_isInvertible μ hμ z.val hz

theorem internalDerivative_isInvertible {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (z : ScalarSpace μ) (hz : Function.Injective z.val) :
    (internalDerivative μ z).IsInvertible := by
  obtain ⟨eS, hS⟩ := neg_isInvertible μ (scalarShift μ z)
    (scalarShift_isInvertible μ hμ z hz)
  obtain ⟨eL, hL⟩ := scalarL_isInvertible μ hμ z hz
  refine ⟨eS.prodCongr eL, ?_⟩
  rw [ContinuousLinearEquiv.coe_prodCongr, hS, hL]
  rfl

def outerResidual {n : ℕ} (μ : Fin n → ℝ) (u : ScalarPair μ) : ScalarPair μ :=
  (-u.1, -(ScalarMinimizer.centeredNormalizedScalarResidual μ u.2))

def outerDerivative {n : ℕ} (μ : Fin n → ℝ) (z : ScalarSpace μ) :
    ScalarPair μ →L[ℝ] ScalarPair μ :=
  (-(ContinuousLinearMap.id ℝ (ScalarSpace μ))).prodMap (-(scalarShift μ z))

theorem outerResidual_hasFDerivAt {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (p : ScalarPair μ) (hz : p.2 ∈ ScalarGeometry.chamber μ) :
    HasFDerivAt (outerResidual μ) (outerDerivative μ p.2) p := by
  have hH := ((ContinuousLinearMap.fst ℝ (ScalarSpace μ)
    (ScalarSpace μ)).hasFDerivAt (x := p)).neg
  have hY := (ScalarMinimizer.centeredNormalizedScalarResidual_hasFDerivAt μ hμ p.2 hz).neg
  have hd := hH.prodMk (hY.comp p
    (ContinuousLinearMap.snd ℝ (ScalarSpace μ) (ScalarSpace μ)).hasFDerivAt)
  exact hd.congr_fderiv (by apply ContinuousLinearMap.ext; intro u; rfl)

theorem outerDerivative_isInvertible {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 < μ i) (z : ScalarSpace μ) (hz : Function.Injective z.val) :
    (outerDerivative μ z).IsInvertible := by
  obtain ⟨eS, hS⟩ := neg_isInvertible μ (scalarShift μ z)
    (scalarShift_isInvertible μ hμ z hz)
  refine ⟨(negativeEquivalence μ).prodCongr eS, ?_⟩
  rw [ContinuousLinearEquiv.coe_prodCongr, hS]
  rfl

/-- Erased finite block sums are reindexed through the real list positions.
Both erased diagonals vanish by the actual physical Newton definition. -/
theorem innerField_internalLabel_eq {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (a : BlockIndex d) (i : InternalIndex d a) :
    innerField h (internalLabel d a i) =
      HorizontalNewton.totalNewtonField (internalMass m d a)
        (fun j => internalCoordinates h (internalLabel d a j)) i := by
  classical
  have hlabel := internalLabel_mem d a i
  have hfin : internalLabel d a i ∈ datumBlockLabels d a := by
    simpa [datumBlockLabels] using hlabel
  rw [innerField, blockOf_eq_of_mem d hlabel, internalFieldOn,
    HorizontalNewton.totalNewtonField]
  have hself : Reuse.physicalNewtonForce (m (internalLabel d a i))
      (internalCoordinates h (internalLabel d a i))
      (internalCoordinates h (internalLabel d a i)) = 0 := by
    simp [Reuse.physicalNewtonForce]
  rw [Finset.sum_erase_eq_sub hfin,
    Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  simp only [internalMass, hself, sub_zero]
  exact (sum_internalLabels d a (fun j => Reuse.physicalNewtonForce (m j)
    (internalCoordinates h j) (internalCoordinates h (internalLabel d a i)))).symm

theorem extracted_internal_embedding {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (a : BlockIndex d) :
    HorizontalNewton.centeredEmbedding (internalMass m d a)
        ((CoordinateProduct.equivalence m d h).2 a) =
      (fun j => internalCoordinates h (internalLabel d a j)) := by
  funext j
  rfl

def productZeroResidual (m : Masses) (d : OrderedClusterDatum)
    (p : ProductSpace m d) : ProductSpace m d :=
  (outerResidual (datumBlockMass m d) p.1,
    fun a => internalResidual (internalMass m d a) (p.2 a))

/-- This is an identity of the actual zero-scale residual for EVERY h,
not a Jacobian assertion supplied as a premise. -/
theorem residual_zero_product_identity {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (h : BlowupCoordinates m d) :
    CoordinateProduct.equivalence m d (blowupResidual hm 0 h) =
      productZeroResidual m d (CoordinateProduct.equivalence m d h) := by
  apply Prod.ext
  · apply Prod.ext
    · apply Subtype.ext
      funext a
      exact blowupResidual_zero_outerH hm h a
    · apply Subtype.ext
      funext a
      change outerY (blowupResidual hm 0 h) a =
        -(ScalarMinimizer.normalizedScalarResidual (datumBlockMass m d) (outerY h) a)
      rw [blowupResidual_zero_outerY, outerSeedField]
      simp only [ScalarMinimizer.normalizedScalarResidual, oneDimensionalForce,
        ScalarGeometry.scalarForce]
      ring
  · funext a
    apply Prod.ext
    · apply Subtype.ext
      funext i
      change innerU (blowupResidual hm 0 h) (internalLabel d a i) = _
      rw [blowupResidual_zero_innerU, innerField_internalLabel_eq]
      simp only [productZeroResidual, internalResidual, newtonAxes,
        extracted_internal_embedding]
      rfl
    · apply Subtype.ext
      funext i
      change innerV (blowupResidual hm 0 h) (internalLabel d a i) = _
      rw [blowupResidual_zero_innerV, innerField_internalLabel_eq]
      simp only [productZeroResidual, internalResidual, newtonAxes,
        extracted_internal_embedding, HorizontalNewton.axisCoordinates]

def internalProductDerivative {m : Masses} {d : OrderedClusterDatum}
    (seed : BlowupCoordinates m d) :
    (∀ a : BlockIndex d, InnerSpace m d a × InnerSpace m d a) →L[ℝ]
      (∀ a : BlockIndex d, InnerSpace m d a × InnerSpace m d a) :=
  ContinuousLinearMap.pi fun a =>
    (internalDerivative (internalMass m d a)
      ((CoordinateProduct.equivalence m d seed).2 a).1).comp (ContinuousLinearMap.proj a)

def productDerivative {m : Masses} {d : OrderedClusterDatum}
    (seed : BlowupCoordinates m d) : ProductSpace m d →L[ℝ] ProductSpace m d :=
  (outerDerivative (datumBlockMass m d)
    (CoordinateProduct.equivalence m d seed).1.2).prodMap (internalProductDerivative seed)

theorem productZeroResidual_hasFDerivAt {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) :
    HasFDerivAt (productZeroResidual m d) (productDerivative seed)
      (CoordinateProduct.equivalence m d seed) := by
  let p := CoordinateProduct.equivalence m d seed
  have ho := outerResidual_hasFDerivAt (datumBlockMass m d)
    (fun a => datumBlockMass_pos hm d a) p.1 (seed_outerY_chamber hs)
  have hi : HasFDerivAt
      (fun x : ∀ a : BlockIndex d, InnerSpace m d a × InnerSpace m d a =>
        fun a => internalResidual (internalMass m d a) (x a))
      (internalProductDerivative seed) p.2 := by
    apply hasFDerivAt_pi.mpr
    intro a
    have hda := internalResidual_hasFDerivAt (internalMass m d a) (p.2 a).1
      (seed_innerU_chamber hs a).injective
    have hpoint : ((p.2 a).1, 0) = p.2 a := by
      apply Prod.ext
      · rfl
      · exact (seed_innerV_zero hs a).symm
    rw [hpoint] at hda
    exact hda.comp p.2 (ContinuousLinearMap.proj a :
      (∀ b : BlockIndex d, InnerSpace m d b × InnerSpace m d b) →L[ℝ]
        (InnerSpace m d a × InnerSpace m d a)).hasFDerivAt
  have hd := (ho.comp p (ContinuousLinearMap.fst ℝ
    (OuterSpace m d × OuterSpace m d)
    (∀ a : BlockIndex d, InnerSpace m d a × InnerSpace m d a)).hasFDerivAt).prodMk
      (hi.comp p (ContinuousLinearMap.snd ℝ
        (OuterSpace m d × OuterSpace m d)
        (∀ a : BlockIndex d, InnerSpace m d a × InnerSpace m d a)).hasFDerivAt)
  exact hd.congr_fderiv (by apply ContinuousLinearMap.ext; intro v; rfl)

theorem productDerivative_isInvertible {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) :
    (productDerivative seed).IsInvertible := by
  classical
  obtain ⟨eo, heo⟩ := outerDerivative_isInvertible (datumBlockMass m d)
    (fun a => datumBlockMass_pos hm d a) (CoordinateProduct.equivalence m d seed).1.2
    (seed_outerY_chamber hs).injective
  have hi (a : BlockIndex d) := internalDerivative_isInvertible (internalMass m d a)
    (internalMass_pos hm d a) ((CoordinateProduct.equivalence m d seed).2 a).1
    (seed_innerU_chamber hs a).injective
  let ei (a : BlockIndex d) := Classical.choose (hi a)
  have hei (a : BlockIndex d) :
      (ei a : (InnerSpace m d a × InnerSpace m d a) →L[ℝ]
        (InnerSpace m d a × InnerSpace m d a)) =
        internalDerivative (internalMass m d a)
          ((CoordinateProduct.equivalence m d seed).2 a).1 :=
    Classical.choose_spec (hi a)
  refine ⟨eo.prodCongr (ContinuousLinearEquiv.piCongrRight ei), ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · exact congrArg (fun A => A v.1) heo
  · funext a
    exact congrArg (fun A => A (v.2 a)) (hei a)

def actualSeedDerivative {m : Masses} {d : OrderedClusterDatum}
    (seed : BlowupCoordinates m d) : BlowupCoordinates m d →L[ℝ] BlowupCoordinates m d :=
  (CoordinateProduct.equivalence m d).symm.toContinuousLinearMap.comp
    ((productDerivative seed).comp (CoordinateProduct.equivalence m d).toContinuousLinearMap)

/-- Full actual Frechet derivative on the original constraint kernel V. -/
theorem blowupResidual_zero_hasFDerivAt {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) :
    HasFDerivAt (fun h : BlowupCoordinates m d => blowupResidual hm 0 h)
      (actualSeedDerivative seed) seed := by
  let e := CoordinateProduct.equivalence m d
  have hd := e.symm.hasFDerivAt.comp seed
    ((productZeroResidual_hasFDerivAt hm hs).comp seed e.hasFDerivAt)
  have heq : (fun h : BlowupCoordinates m d => blowupResidual hm 0 h) =
      (fun h : BlowupCoordinates m d => e.symm (productZeroResidual m d (e h))) := by
    funext h
    apply e.injective
    rw [e.apply_symm_apply]
    exact residual_zero_product_identity hm h
  rw [heq]
  exact hd

theorem blowupResidual_zero_fderiv {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) :
    fderiv ℝ (fun h : BlowupCoordinates m d => blowupResidual hm 0 h) seed =
      actualSeedDerivative seed :=
  (blowupResidual_zero_hasFDerivAt hm hs).fderiv

/-- The complete arbitrary-tangent formula. Each output only uses the
corresponding input scalar coordinate, so all mixed blocks are zero. -/
theorem blowupResidual_zero_fderiv_components {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d} (hs : IsSeed m d seed)
    (v : BlowupCoordinates m d) :
    CoordinateProduct.equivalence m d
        (fderiv ℝ (fun h : BlowupCoordinates m d => blowupResidual hm 0 h) seed v) =
      ((-(CoordinateProduct.equivalence m d v).1.1,
        -(scalarShift (datumBlockMass m d) (CoordinateProduct.equivalence m d seed).1.2
          (CoordinateProduct.equivalence m d v).1.2)),
       fun a =>
        (-(scalarShift (internalMass m d a) ((CoordinateProduct.equivalence m d seed).2 a).1
          ((CoordinateProduct.equivalence m d v).2 a).1),
         scalarL (internalMass m d a) ((CoordinateProduct.equivalence m d seed).2 a).1
          ((CoordinateProduct.equivalence m d v).2 a).2)) := by
  rw [blowupResidual_zero_fderiv hm hs]
  change CoordinateProduct.equivalence m d
    ((CoordinateProduct.equivalence m d).symm
      (productDerivative seed (CoordinateProduct.equivalence m d v))) = _
  rw [(CoordinateProduct.equivalence m d).apply_symm_apply]
  rfl

def actualSeedEquivalence {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) :
    BlowupCoordinates m d ≃L[ℝ] BlowupCoordinates m d :=
  let eJ := Classical.choose (productDerivative_isInvertible hm hs)
  let e := CoordinateProduct.equivalence m d
  (e.trans eJ).trans e.symm

theorem actualSeedEquivalence_coe {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) :
    (actualSeedEquivalence hm hs : BlowupCoordinates m d →L[ℝ] BlowupCoordinates m d) =
      actualSeedDerivative seed := by
  have heJ := Classical.choose_spec (productDerivative_isInvertible hm hs)
  let e := CoordinateProduct.equivalence m d
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun A => e.symm (A (e v))) heJ

theorem actualSeedDerivative_isInvertible {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) :
    (actualSeedDerivative seed).IsInvertible :=
  ⟨actualSeedEquivalence hm hs, actualSeedEquivalence_coe hm hs⟩

/-- Invertibility of the ACTUAL fderiv, with no Jacobian or inverse premise. -/
theorem blowupResidual_zero_fderiv_isInvertible {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) :
    (fderiv ℝ (fun h : BlowupCoordinates m d => blowupResidual hm 0 h) seed).IsInvertible := by
  rw [blowupResidual_zero_fderiv hm hs]
  exact actualSeedDerivative_isInvertible hm hs

/-- The actual continuous linear inverse, obtained from the proved positive
blocks and their conjugation. No inverse or Jacobian premise is supplied. -/
def actualSeedInverse {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d} (hs : IsSeed m d seed) :
    BlowupCoordinates m d →L[ℝ] BlowupCoordinates m d :=
  (actualSeedEquivalence hm hs).symm.toContinuousLinearMap

theorem actualSeedInverse_left {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d} (hs : IsSeed m d seed)
    (v : BlowupCoordinates m d) :
    actualSeedInverse hm hs
      (fderiv ℝ (fun h : BlowupCoordinates m d => blowupResidual hm 0 h) seed v) = v := by
  change (actualSeedEquivalence hm hs).symm
    (fderiv ℝ (fun h : BlowupCoordinates m d => blowupResidual hm 0 h) seed v) = v
  rw [blowupResidual_zero_fderiv hm hs, ← actualSeedEquivalence_coe hm hs]
  exact (actualSeedEquivalence hm hs).symm_apply_apply v

theorem actualSeedInverse_right {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} {seed : BlowupCoordinates m d} (hs : IsSeed m d seed)
    (v : BlowupCoordinates m d) :
    fderiv ℝ (fun h : BlowupCoordinates m d => blowupResidual hm 0 h) seed
      (actualSeedInverse hm hs v) = v := by
  change fderiv ℝ (fun h : BlowupCoordinates m d => blowupResidual hm 0 h) seed
    ((actualSeedEquivalence hm hs).symm v) = v
  rw [blowupResidual_zero_fderiv hm hs, ← actualSeedEquivalence_coe hm hs]
  exact (actualSeedEquivalence hm hs).apply_symm_apply v

/-- Specialization to the concrete seed constructed from the proved scalar
minimizers. There is no seed-existence premise in this declaration. -/
theorem seedCoordinates_zero_hasFDerivAt {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) :
    HasFDerivAt (fun h : BlowupCoordinates m d => blowupResidual hm 0 h)
      (actualSeedDerivative (seedCoordinates hm d)) (seedCoordinates hm d) :=
  blowupResidual_zero_hasFDerivAt hm (seedCoordinates_isSeed hm d)

theorem seedCoordinates_zero_fderiv_isInvertible {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) :
    (fderiv ℝ (fun h : BlowupCoordinates m d => blowupResidual hm 0 h)
      (seedCoordinates hm d)).IsInvertible :=
  blowupResidual_zero_fderiv_isInvertible hm (seedCoordinates_isSeed hm d)

end FourBody.SeedJacobian

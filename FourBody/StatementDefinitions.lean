import FourBody.Geometry
import FourBody.ClusterData
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Max

/-!
# Source-facing specifications for the frozen Pro v2 manuscript

Source: four_body_strong_anisotropy_pro_v2.tex, 32604 bytes,
SHA256 97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

This module contains concrete definitions and target propositions. It proves
no main theorem and supplies no analytic or classification certificate.
The target propositions are not assumptions of any mathematical theorem.

The solution objects are the actual labeled configurations from Geometry.
All parameter ranges occur in propositions rather than inside IsSolution.
Thus the source's diameter lemma for every s > 0 is not made vacuous.

The datum uses the actual ordered nonempty lists from ClusterData, rather
than a 192-element type detached from blocks or internal label order.
-/

noncomputable section

open scoped BigOperators

namespace FourBody

/-- The collision-free original real solution set, with literal tuple equality. -/
abbrev SolutionSpace (m : Masses) (s : ℝ) :=
  {q : Configuration // IsSolution m s q}

abbrev XAxisSolutionSpace (m : Masses) (s : ℝ) :=
  {q : Configuration // IsSolution m s q ∧ OnXAxis q}

abbrev YAxisSolutionSpace (m : Masses) (s : ℝ) :=
  {q : Configuration // IsSolution m s q ∧ OnYAxis q}

/-- Noncollinear means failure of the actual affine-line predicate. -/
abbrev NoncollinearSolutionSpace (m : Masses) (s : ℝ) :=
  {q : Configuration // IsSolution m s q ∧ ¬ Collinear q}

/-- Finite cardinality is a conclusion, not an input typeclass or hypothesis. -/
def ExactSolutionCounts (m : Masses) (s : ℝ) : Prop :=
  Nonempty (SolutionSpace m s ≃ Fin 192) ∧
  Nonempty (XAxisSolutionSpace m s ≃ Fin 24) ∧
  Nonempty (YAxisSolutionSpace m s ≃ Fin 24) ∧
  Nonempty (NoncollinearSolutionSpace m s ≃ Fin 144)

/-- The membership witness locates the actual original configuration in W.
The derivative is precisely Geometry.Nondegenerate on W with s fixed. -/
def OriginalNondegenerate (m : Masses) (s : ℝ) (q : Configuration) : Prop :=
  ∃ hq : q ∈ W m, Nondegenerate m s (⟨q, hq⟩ : W m)

def AllSolutionsNondegenerate (m : Masses) (s : ℝ) : Prop :=
  ∀ q : Configuration, IsSolution m s q → OriginalNondegenerate m s q

/-- Link the same physical branch classification to the actual block count. -/
def DatumSolutionStrata (d : OrderedClusterDatum) (q : Configuration) : Prop :=
  (d.blocks.length = 1 ↔ OnXAxis q) ∧
  (d.blocks.length = 4 ↔ OnYAxis q) ∧
  ((1 < d.blocks.length ∧ d.blocks.length < 4) ↔ ¬ Collinear q)

/-- This is a transparent target specification, not a proved result.
One threshold is allowed to depend on the fixed mass vector alone. -/
def MainCountNondegeneracyStatement : Prop :=
  ∀ m : Masses, PositiveMasses m →
    ∃ s₀ : ℝ, 1 < s₀ ∧
      Module.finrank ℝ (W m) = 6 ∧
      ∀ s : ℝ, s₀ < s →
        ExactSolutionCounts m s ∧ AllSolutionsNondegenerate m s

/-- Blocks keep the outer list order; each list keeps its internal order. -/
abbrev BlockIndex (d : OrderedClusterDatum) := Fin d.blocks.length

def datumBlock (d : OrderedClusterDatum) (a : BlockIndex d) : List Label :=
  d.blocks.get a

def datumBlockLabels (d : OrderedClusterDatum) (a : BlockIndex d) : Finset Label :=
  (datumBlock d a).toFinset

def datumBlockMass (m : Masses) (d : OrderedClusterDatum) (a : BlockIndex d) : ℝ :=
  ∑ i ∈ datumBlockLabels d a, m i

abbrev InternalIndex (d : OrderedClusterDatum) (a : BlockIndex d) :=
  Fin (datumBlock d a).length

def internalLabel (d : OrderedClusterDatum) (a : BlockIndex d)
    (i : InternalIndex d a) : Label :=
  (datumBlock d a).get i

/-- Four groups of actual coordinates, before imposing mass constraints.
The parentheses fix the order as ((H,Y),(u,v)). -/
abbrev CoordinateAmbient (d : OrderedClusterDatum) :=
  ((BlockIndex d → ℝ) × (BlockIndex d → ℝ)) ×
    ((Label → ℝ) × (Label → ℝ))

/-- The explicit finite linear constraint map from eq:constraints.
Its kernel is the real constrained coordinate space; no arbitrary
six-dimensional model or regularity assumption is substituted. -/
def coordinateConstraintLM (m : Masses) (d : OrderedClusterDatum) :
    CoordinateAmbient d →ₗ[ℝ]
      ((ℝ × ℝ) × ((BlockIndex d → ℝ) × (BlockIndex d → ℝ))) where
  toFun z :=
    ((∑ a, datumBlockMass m d a * z.1.1 a,
      ∑ a, datumBlockMass m d a * z.1.2 a),
     ((fun a => ∑ i ∈ datumBlockLabels d a, m i * z.2.1 i),
      (fun a => ∑ i ∈ datumBlockLabels d a, m i * z.2.2 i)))
  map_add' z t := by
    ext <;> simp [mul_add, Finset.sum_add_distrib]
  map_smul' c z := by
    ext <;> simp [smul_eq_mul, Finset.mul_sum, mul_left_comm]

def coordinateSpace (m : Masses) (d : OrderedClusterDatum) :
    Submodule ℝ (CoordinateAmbient d) :=
  (coordinateConstraintLM m d).ker

abbrev BlowupCoordinates (m : Masses) (d : OrderedClusterDatum) :=
  coordinateSpace m d

def outerH {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (a : BlockIndex d) : ℝ :=
  h.val.1.1 a

def outerY {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (a : BlockIndex d) : ℝ :=
  h.val.1.2 a

def innerU {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (i : Label) : ℝ :=
  h.val.2.1 i

def innerV {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (i : Label) : ℝ :=
  h.val.2.2 i

/-- Finite one-dimensional force, with the same normalization as eq:oned.
As in the planar force, physical claims are confined to distinct positions. -/
def oneDimensionalForce {n : ℕ} (μ z : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, μ j * (z i - z j) / |z i - z j| ^ 3

def OneDimensionalSolution {n : ℕ} (μ z : Fin n → ℝ) : Prop :=
  (∀ i j, i ≠ j → z i ≠ z j) ∧
  (∑ i, μ i * z i) = 0 ∧
  ∀ i, oneDimensionalForce μ z i = z i

/-- A concrete equation/order predicate for a seed. Its existence is not
postulated. Fin indexing orders the blocks and the actual labels in each
block; singleton and one-block cases remain part of this definition. -/
def IsSeed (m : Masses) (d : OrderedClusterDatum)
    (h : BlowupCoordinates m d) : Prop :=
  (∀ a, outerH h a = 0) ∧
  (∀ i, innerV h i = 0) ∧
  StrictMono (outerY h) ∧
  OneDimensionalSolution (datumBlockMass m d) (outerY h) ∧
  ∀ a : BlockIndex d,
    StrictMono (fun i : InternalIndex d a => innerU h (internalLabel d a i)) ∧
    OneDimensionalSolution
      (fun i : InternalIndex d a => m (internalLabel d a i))
      (fun i : InternalIndex d a => innerU h (internalLabel d a i))

/-- The exact physical coordinate formula, for every label in its actual block.
This relation avoids making a hidden arbitrary choice of a block for a label.
The uniqueness and linear-isomorphism bridges are still obligations. -/
def RepresentsCoordinates (m : Masses) (d : OrderedClusterDatum) (ε : ℝ)
    (h : BlowupCoordinates m d) (q : Configuration) : Prop :=
  ∀ (a : BlockIndex d) (i : Label), i ∈ datumBlock d a →
    q i = !₂[ε * outerH h a + ε * innerU h i,
      outerY h a + ε * innerV h i]

def epsilon (s : ℝ) : ℝ := Real.rpow s (-(1 : ℝ) / 3)

def parameterFromEpsilon (ε : ℝ) : ℝ := (ε ^ 3)⁻¹

/-- Source Proposition 4.1, stated through actual coordinate and solution
relations. The same η,N,h witness all components. Negative ε occurs only
in AnalyticOnNhd and the extension h, not in physical solution claims.

No proof of this proposition, seed uniqueness, analytic IFT, or the
Qε/Tε representations is supplied by declaring this definition. -/
def AnalyticLocalBranch (m : Masses) (d : OrderedClusterDatum)
    (seed : BlowupCoordinates m d) (η : ℝ)
    (N : Set (BlowupCoordinates m d)) (h : ℝ → BlowupCoordinates m d) : Prop :=
  0 < η ∧
  IsOpen N ∧ seed ∈ N ∧ IsSeed m d seed ∧
  AnalyticOnNhd ℝ h (Set.Ioo (-η) η) ∧
  h 0 = seed ∧
  ∀ ε : ℝ, 0 < ε → ε < η →
    h ε ∈ N ∧
    ∃ q : Configuration,
      IsSolution m (parameterFromEpsilon ε) q ∧
      RepresentsCoordinates m d ε (h ε) q ∧
      (∀ q' : Configuration,
        IsSolution m (parameterFromEpsilon ε) q' →
        (∃ h' : BlowupCoordinates m d,
          h' ∈ N ∧ RepresentsCoordinates m d ε h' q') →
        q' = q) ∧
      (∀ h' : BlowupCoordinates m d,
        h' ∈ N → RepresentsCoordinates m d ε h' q → h' = h ε) ∧
      OriginalNondegenerate m (parameterFromEpsilon ε) q

/-- The entire datum-local branch target has only the original positive-mass
hypothesis. The seed and analytic branch are existential conclusions. -/
def AllDataLocalBranchesStatement : Prop :=
  ∀ m : Masses, PositiveMasses m →
    ∀ d : OrderedClusterDatum,
      ∃ seed : BlowupCoordinates m d,
      ∃ η : ℝ,
      ∃ N : Set (BlowupCoordinates m d),
      ∃ h : ℝ → BlowupCoordinates m d,
        AnalyticLocalBranch m d seed η N h

/-- A source-facing main target, with one mass-dependent threshold and one
datum-indexed seed/branch family. The physical equivalence at every s is
explicitly tied to that SAME branch family and ε=s^(-1/3).

This definition is a target proposition only. The original 216-item ledger
still requires the two-scale, arbitrary-sequence, IFT, recovery and proof
route obligations; defining this proposition proves none of them. -/
def MainStatement : Prop :=
  ∀ m : Masses, PositiveMasses m →
    ∃ s₀ : ℝ, 1 < s₀ ∧
      Module.finrank ℝ (W m) = 6 ∧
      ∃ seed : ∀ d : OrderedClusterDatum, BlowupCoordinates m d,
      ∃ η : OrderedClusterDatum → ℝ,
      ∃ N : ∀ d : OrderedClusterDatum, Set (BlowupCoordinates m d),
      ∃ h : ∀ d : OrderedClusterDatum, ℝ → BlowupCoordinates m d,
        (∀ d, AnalyticLocalBranch m d (seed d) (η d) (N d) (h d)) ∧
        ∀ s : ℝ, s₀ < s →
          ExactSolutionCounts m s ∧ AllSolutionsNondegenerate m s ∧
          ∃ e : OrderedClusterDatum ≃ SolutionSpace m s,
            ∀ d : OrderedClusterDatum,
              0 < epsilon s ∧ epsilon s < η d ∧
              RepresentsCoordinates m d (epsilon s)
                (h d (epsilon s)) (e d).val ∧
              DatumSolutionStrata d (e d).val

/-- The real coordinate-value set, with all four labels included. -/
def coordinateValues (q : Configuration) (k : Axis) : Finset ℝ :=
  (Finset.univ : Finset Label).image (fun i => q i k)

theorem coordinateValues_nonempty (q : Configuration) (k : Axis) :
    (coordinateValues q k).Nonempty :=
  Finset.univ_nonempty.image (fun i : Label => q i k)

/-- Actual maximum minus actual minimum, including tied coordinates. -/
def actualCoordinateDiameter (q : Configuration) (k : Axis) : ℝ :=
  (coordinateValues q k).max' (coordinateValues_nonempty q k) -
    (coordinateValues q k).min' (coordinateValues_nonempty q k)

/-- Source Lemma 2.1: all s>0 and all original solutions. This is a target
Prop and not a theorem asserted merely by its definition. -/
def DiameterEstimateStatement : Prop :=
  ∀ m : Masses, PositiveMasses m →
    ∀ s : ℝ, 0 < s →
      ∀ q : Configuration, IsSolution m s q →
        actualCoordinateDiameter q 0 ≤ 3 * Real.rpow (totalMass m / s) ((1 : ℝ) / 3) ∧
        actualCoordinateDiameter q 1 ≤ 3 * Real.rpow (totalMass m) ((1 : ℝ) / 3)

/-- Actual block mass mean of a physical configuration. Positive block masses
and its equality with the inverse Qε block centers remain proof obligations. -/
def datumBlockMean (m : Masses) (d : OrderedClusterDatum) (q : Configuration)
    (a : BlockIndex d) : Point :=
  (datumBlockMass m d a)⁻¹ • ∑ i ∈ datumBlockLabels d a, m i • q i

def horizontalCenterCoordinate (m : Masses) (d : OrderedClusterDatum)
    (ε : ℝ) (q : Configuration) (a : BlockIndex d) : ℝ :=
  datumBlockMean m d q a 0 / ε

def verticalCenterCoordinate (m : Masses) (d : OrderedClusterDatum)
    (q : Configuration) (a : BlockIndex d) : ℝ :=
  datumBlockMean m d q a 1

def internalVectorCoordinate (m : Masses) (d : OrderedClusterDatum)
    (ε : ℝ) (q : Configuration) (a : BlockIndex d) (i : Label) : Point :=
  ε⁻¹ • (q i - datumBlockMean m d q a)

/-- Both the physical position formula and every displayed inverse block-mean
coordinate from eq:sequence-coordinates. The relation is concrete and is
not an abstract certificate for a selected solution sequence. -/
def CoordinatesOfConfiguration (m : Masses) (d : OrderedClusterDatum)
    (ε : ℝ) (q : Configuration) (h : BlowupCoordinates m d) : Prop :=
  RepresentsCoordinates m d ε h q ∧
  (∀ a, outerH h a = horizontalCenterCoordinate m d ε q a) ∧
  (∀ a, outerY h a = verticalCenterCoordinate m d q a) ∧
  ∀ (a : BlockIndex d) (i : Label), i ∈ datumBlock d a →
    !₂[innerU h i, innerV h i] = internalVectorCoordinate m d ε q a i

/-- An explicit common cubic bound is a finite-block version of H_a=O(ε³).
Its constant may depend on the selected sequence/subsequence and mass vector. -/
def HorizontalCentersCubicBound (m : Masses) (d : OrderedClusterDatum)
    (e : ℕ → ℝ) (h : ℕ → BlowupCoordinates m d) : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∀ᶠ ν in Filter.atTop, ∀ a : BlockIndex d, |outerH (h ν) a| ≤ K * (e ν) ^ 3

/-- Actual distance regimes along a selected sequence. Same witnesses
d,φ,seed are used by all centers, internal vectors and pair limits. -/
def SequenceDistanceRegimes (m : Masses) (d : OrderedClusterDatum)
    (seed : BlowupCoordinates m d) (e : ℕ → ℝ)
    (q : ℕ → Configuration) : Prop :=
  (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ ν in Filter.atTop,
      ∀ (a : BlockIndex d) (i j : Label),
        i ∈ datumBlock d a → j ∈ datumBlock d a → i ≠ j →
          c * e ν ≤ dist (q ν i) (q ν j) ∧ dist (q ν i) (q ν j) < C * e ν) ∧
  ∀ (a b : BlockIndex d), a ≠ b →
    ∀ (i j : Label), i ∈ datumBlock d a → j ∈ datumBlock d b →
      0 < |outerY seed a - outerY seed b| ∧
      Filter.Tendsto (fun ν => dist (q ν i) (q ν j)) Filter.atTop
        (nhds |outerY seed a - outerY seed b|)

/-- Source Proposition 3.2 with one simultaneous strictly increasing subsequence
and one fixed datum. There is no assumed branch membership or completeness.
No all-index positivity is added to an arbitrary sequence: admissible s>1 is
a conclusion obtained after choosing the subsequence and discarding a prefix.

The explicit ε→0 and common cubic bound follow the source proof and must be
proved, not supplied as input hypotheses. -/
def SeedLimitStatement : Prop :=
  ∀ m : Masses, PositiveMasses m →
    ∀ (s : ℕ → ℝ) (q : ℕ → Configuration),
      Filter.Tendsto s Filter.atTop Filter.atTop →
      (∀ ν : ℕ, IsSolution m (s ν) (q ν)) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∃ d : OrderedClusterDatum,
        ∃ seed : BlowupCoordinates m d,
        ∃ h : ℕ → BlowupCoordinates m d,
          IsSeed m d seed ∧
          (∀ ν : ℕ, 1 < s (φ ν)) ∧
          Filter.Tendsto (fun ν => epsilon (s (φ ν))) Filter.atTop (nhds 0) ∧
          (∀ ν : ℕ, CoordinatesOfConfiguration m d (epsilon (s (φ ν)))
            (q (φ ν)) (h ν)) ∧
          (∀ a : BlockIndex d,
            Filter.Tendsto (fun ν => outerH (h ν) a) Filter.atTop (nhds 0) ∧
            Filter.Tendsto (fun ν => outerY (h ν) a) Filter.atTop (nhds (outerY seed a))) ∧
          (∀ (a : BlockIndex d) (i : Label), i ∈ datumBlock d a →
            Filter.Tendsto
              (fun ν => internalVectorCoordinate m d (epsilon (s (φ ν))) (q (φ ν)) a i)
              Filter.atTop (nhds (!₂[innerU seed i, 0] : Point))) ∧
          HorizontalCentersCubicBound m d (fun ν => epsilon (s (φ ν))) h ∧
          SequenceDistanceRegimes m d seed
            (fun ν => epsilon (s (φ ν))) (fun ν => q (φ ν))

end FourBody


import FourBody.StatementDefinitions
import Mathlib.Data.Fintype.EquivFin

/-!
Frozen Pro v2 Section 5, lines 705--724, SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.

These are actual equivalence transports of a proved literal solution
classification. They do not assume finite cardinality of any solution
space, nor identify configurations under any symmetry.

Initially prepared as a proof candidate. Actual build/audit status is
recorded in strict receipts; this module alone does not attest
whole-paper acceptance.
-/

noncomputable section
namespace FourBody.Global

/-- Forget the intermediate solution subtype while preserving both the
original collision-free equation and the actual physical stratum. -/
def solutionStratumFlatten (m : Masses) (s : ℝ) (Q : Configuration → Prop) :
    {q : SolutionSpace m s // Q q.val} ≃
      {q : Configuration // IsSolution m s q ∧ Q q} where
  toFun q := ⟨q.val.val, q.val.property, q.property⟩
  invFun q := ⟨⟨q.val, q.property.1⟩, q.property.2⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

/-- Restrict the SAME datum/solution equivalence to a concrete physical
predicate. No unrelated bijection is introduced to produce a count. -/
def solutionStratumEquivalence {m : Masses} {s : ℝ}
    (e : OrderedClusterDatum ≃ SolutionSpace m s)
    (P : OrderedClusterDatum → Prop) (Q : Configuration → Prop)
    (he : ∀ d, P d ↔ Q (e d).val) :
    {d : OrderedClusterDatum // P d} ≃
      {q : Configuration // IsSolution m s q ∧ Q q} :=
  (e.subtypeEquiv he).trans (solutionStratumFlatten m s Q)

/-- The complete literal 192=24+24+144 conclusion follows from the actual
data encoding and physical stratum equivalences of this one bijection. -/
theorem exactSolutionCounts_of_datum_equivalence {m : Masses} {s : ℝ}
    (e : OrderedClusterDatum ≃ SolutionSpace m s)
    (hs : ∀ d, DatumSolutionStrata d (e d).val) : ExactSolutionCounts m s := by
  classical
  let ex := solutionStratumEquivalence e
    (fun d => d.blockCount = 1) OnXAxis
    (fun d => by simpa only [OrderedClusterDatum.blockCount] using (hs d).1)
  let ey := solutionStratumEquivalence e
    (fun d => d.blockCount = 4) OnYAxis
    (fun d => by simpa only [OrderedClusterDatum.blockCount] using (hs d).2.1)
  let en := solutionStratumEquivalence e
    (fun d => 1 < d.blockCount ∧ d.blockCount < 4) (fun q => ¬ Collinear q)
    (fun d => by simpa only [OrderedClusterDatum.blockCount] using (hs d).2.2)
  exact ⟨⟨e.symm.trans (Fintype.equivFinOfCardEq card_orderedClusterDatum)⟩,
    ⟨ex.symm.trans (Fintype.equivFinOfCardEq card_oneBlockData)⟩,
    ⟨ey.symm.trans (Fintype.equivFinOfCardEq card_fourBlockData)⟩,
    ⟨en.symm.trans (Fintype.equivFinOfCardEq card_middleBlockData)⟩⟩

end FourBody.Global

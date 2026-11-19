import FourBody.CoordinateEquivalence
import FourBody.Reuse.NewtonBounds
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
The literal fields in v2 sec. 4 (frozen TeX SHA256
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD).
Finite cancellation is proved from the physical Newton kernel, including
its zero diagonal. No analytic, seed, compactness or solution interface
is an assumption here. Static preparation: compilation remains pending.
-/

noncomputable section
open scoped BigOperators
namespace FourBody

def internalCoordinates {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) : Configuration :=
  fun i => !₂[innerU h i, innerV h i]

def internalRho {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (i j : Label) : ℝ :=
  dist (internalCoordinates h i) (internalCoordinates h j)

def internalFieldOn (m : Masses) (S : Finset Label) (q : Configuration)
    (i : Label) : Point :=
  ∑ j ∈ S.erase i, Reuse.physicalNewtonForce (m j) (q j) (q i)

def innerField {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (i : Label) : Point :=
  internalFieldOn m (datumBlockLabels d (blockOf d i)) (internalCoordinates h) i

def crossDifference {m : Masses} {d : OrderedClusterDatum} (ε : ℝ)
    (h : BlowupCoordinates m d) (i j : Label) : Point :=
  !₂[ε * (outerH h (blockOf d i) - outerH h (blockOf d j) +
      innerU h i - innerU h j),
    outerY h (blockOf d i) - outerY h (blockOf d j) +
      ε * (innerV h i - innerV h j)]

theorem crossDifference_eq_sub {m : Masses} {d : OrderedClusterDatum}
    (ε : ℝ) (h : BlowupCoordinates m d) (i j : Label) :
    crossDifference ε h i j = physicalCoordinates ε h i - physicalCoordinates ε h j := by
  ext k
  fin_cases k <;> simp [crossDifference, physicalCoordinates] <;> ring

def externalField {m : Masses} {d : OrderedClusterDatum} (ε : ℝ)
    (h : BlowupCoordinates m d) (i : Label) : Point :=
  ∑ j, if blockOf d j ≠ blockOf d i then
    Reuse.physicalNewtonForce (m j) (physicalCoordinates ε h j)
      (physicalCoordinates ε h i) else 0

def externalMean {m : Masses} {d : OrderedClusterDatum} (ε : ℝ)
    (h : BlowupCoordinates m d) (a : BlockIndex d) : Point :=
  datumBlockMean m d (externalField ε h) a

theorem externalField_eq_cross_sum {m : Masses} {d : OrderedClusterDatum}
    (ε : ℝ) (h : BlowupCoordinates m d) (i : Label) :
    externalField ε h i = ∑ j ∈ Finset.univ.filter
      (fun j => blockOf d j ≠ blockOf d i),
      (m j / ‖crossDifference ε h i j‖ ^ 3) • crossDifference ε h i j := by
  classical
  rw [externalField, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp only [crossDifference_eq_sub, Reuse.physicalNewtonForce,
    dist_eq_norm]

private def newtonWeightedPair (m : Masses) (q : Configuration)
    (i j : Label) : Point :=
  (m i * m j / dist (q i) (q j) ^ 3) • (q i - q j)

private theorem newtonWeightedPair_self (m : Masses) (q : Configuration)
    (i : Label) : newtonWeightedPair m q i i = 0 := by
  simp [newtonWeightedPair]

private theorem newtonWeightedPair_swap (m : Masses) (q : Configuration)
    (i j : Label) : newtonWeightedPair m q j i = -newtonWeightedPair m q i j := by
  simp only [newtonWeightedPair, dist_comm (q j) (q i), mul_comm (m j) (m i)]
  rw [show q j - q i = -(q i - q j) by abel, smul_neg]

private theorem mass_smul_newton (m : Masses) (q : Configuration) (i j : Label) :
    m i • Reuse.physicalNewtonForce (m j) (q j) (q i) =
      newtonWeightedPair m q i j := by
  simp only [Reuse.physicalNewtonForce, newtonWeightedPair, smul_smul]
  congr 1
  ring

theorem internalFieldOn_weighted_cancel (m : Masses) (S : Finset Label)
    (q : Configuration) : (∑ i ∈ S, m i • internalFieldOn m S q i) = 0 := by
  classical
  have hexpand : ∀ i ∈ S, m i • internalFieldOn m S q i =
      ∑ j ∈ S, newtonWeightedPair m q i j := by
    intro i hi
    have herase := Finset.sum_erase_add S (newtonWeightedPair m q i) hi
    rw [newtonWeightedPair_self, add_zero] at herase
    rw [← herase]
    simp only [internalFieldOn, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun j _ => mass_smul_newton m q i j)
  have hswap : (∑ i ∈ S, ∑ j ∈ S, newtonWeightedPair m q i j) =
      -(∑ i ∈ S, ∑ j ∈ S, newtonWeightedPair m q i j) := by
    calc
      _ = ∑ i ∈ S, ∑ j ∈ S, newtonWeightedPair m q j i := Finset.sum_comm
      _ = ∑ i ∈ S, ∑ j ∈ S, -newtonWeightedPair m q i j := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_congr rfl (fun j _ => newtonWeightedPair_swap m q i j)
      _ = _ := by simp only [Finset.sum_neg_distrib]
  rw [Finset.sum_congr rfl hexpand]
  ext k
  have hk := congrArg (fun p : Point => p k) hswap
  change (∑ i ∈ S, ∑ j ∈ S, newtonWeightedPair m q i j) k =
    -((∑ i ∈ S, ∑ j ∈ S, newtonWeightedPair m q i j) k) at hk
  change (∑ i ∈ S, ∑ j ∈ S, newtonWeightedPair m q i j) k = 0
  linarith

theorem innerField_weighted_cancel {m : Masses} {d : OrderedClusterDatum}
    (h : BlowupCoordinates m d) (a : BlockIndex d) :
    (∑ i ∈ datumBlockLabels d a, m i • innerField h i) = 0 := by
  classical
  calc
    _ = ∑ i ∈ datumBlockLabels d a,
        m i • internalFieldOn m (datumBlockLabels d a) (internalCoordinates h) i := by
      apply Finset.sum_congr rfl
      intro i hi
      have himem : i ∈ datumBlock d a := by simpa [datumBlockLabels] using hi
      rw [innerField, blockOf_eq_of_mem d himem]
    _ = 0 := internalFieldOn_weighted_cancel m _ _

theorem externalField_weighted_cancel {m : Masses} {d : OrderedClusterDatum}
    (ε : ℝ) (h : BlowupCoordinates m d) :
    (∑ i, m i • externalField ε h i) = 0 := by
  classical
  let q := physicalCoordinates ε h
  let P : Label → Label → Point := fun i j =>
    if blockOf d j ≠ blockOf d i then newtonWeightedPair m q i j else 0
  have hexpand : ∀ i, m i • externalField ε h i = ∑ j, P i j := by
    intro i
    simp only [externalField, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [P, q]
    split_ifs <;> simp only [mass_smul_newton, smul_zero]
  have hp : ∀ i j, P j i = -P i j := by
    intro i j
    dsimp [P]
    by_cases heq : blockOf d j = blockOf d i
    · simp [heq]
    · rw [if_pos (Ne.symm heq), if_pos heq]
      exact newtonWeightedPair_swap m q i j
  have hswap : (∑ i, ∑ j, P i j) = -(∑ i, ∑ j, P i j) := by
    calc
      _ = ∑ i, ∑ j, P j i := Finset.sum_comm
      _ = ∑ i, ∑ j, -P i j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact hp i j
      _ = _ := by simp only [Finset.sum_neg_distrib]
  simp_rw [hexpand]
  ext k
  have hk := congrArg (fun p : Point => p k) hswap
  change (∑ i, ∑ j, P i j) k = -((∑ i, ∑ j, P i j) k) at hk
  change (∑ i, ∑ j, P i j) k = 0
  linarith

theorem innerField_weighted_coordinate_cancel {m : Masses}
    {d : OrderedClusterDatum} (h : BlowupCoordinates m d)
    (a : BlockIndex d) (k : Axis) :
    (∑ i ∈ datumBlockLabels d a, m i * innerField h i k) = 0 := by
  simpa only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    PiLp.zero_apply, smul_eq_mul] using
    congrArg (fun p : Point => p k) (innerField_weighted_cancel h a)

theorem externalMean_total_cancel {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (ε : ℝ) (h : BlowupCoordinates m d) (k : Axis) :
    (∑ a, datumBlockMass m d a * externalMean ε h a k) = 0 := by
  change (∑ a, datumBlockMass m d a *
    datumBlockMean m d (externalField ε h) a k) = 0
  rw [sum_block_mass_means hm]
  simpa only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    PiLp.zero_apply, smul_eq_mul] using
    congrArg (fun p : Point => p k) (externalField_weighted_cancel ε h)

theorem weighted_mean_deviation_cancel {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (q : Configuration) (a : BlockIndex d) (k : Axis) :
    (∑ i ∈ datumBlockLabels d a,
      m i * (q i k - datumBlockMean m d q (blockOf d i) k)) = 0 := by
  classical
  calc
    _ = ∑ i ∈ datumBlockLabels d a,
        (m i * q i k - m i * datumBlockMean m d q a k) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [blockOf_eq_of_mem d (by simpa [datumBlockLabels] using hi)]
      ring
    _ = (∑ i ∈ datumBlockLabels d a, m i * q i k) -
        datumBlockMass m d a * datumBlockMean m d q a k := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      rfl
    _ = 0 := by rw [block_mass_mul_mean hm, sub_self]

theorem external_deviation_cancel {m : Masses} (hm : PositiveMasses m)
    {d : OrderedClusterDatum} (ε : ℝ) (h : BlowupCoordinates m d)
    (a : BlockIndex d) (k : Axis) :
    (∑ i ∈ datumBlockLabels d a,
      m i * (externalField ε h i k - externalMean ε h (blockOf d i) k)) = 0 :=
  weighted_mean_deviation_cancel hm d _ a k

end FourBody

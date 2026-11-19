import FourBody.SourceGapSharp
import FourBody.ClusterVertical
import FourBody.ClusterExtrema
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
STATIC source-faithful completion for frozen v2 line295 / S2-U19.
Independent expectations were written and hashed before this proof draft.
The exact sharp denominator is proved before the coefficient-three result.
Actual proper/full endpoints discharge all Lipschitz, radius, separation,
and denominator positivity helpers from the manuscript's physical context.
No target inequality, mean equation, chosen cut, or bound is assumed there.
No Lean/Lake/actual type-AST/kernel audit was run for this draft.
-/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace FourBody.SourceGap295
open ClusterVertical SourceFaithfulGap SourceFaithfulCluster

theorem reduced_cardinality_real_pos :
  ∀ (J : Finset Label), 2 ≤ J.card → 0 < (J.card : ℝ) - 1 := by
  intro J hcard
  have hc : (2 : ℝ) ≤ (J.card : ℝ) := by exact_mod_cast hcard
  linarith

theorem vertical_gap_sharp_from_cut :
  ∀ {m : Masses}, PositiveMasses m →
  ∀ {q : Configuration} {s : ℝ}, IsSolution m s q →
  ∀ {J A : Finset Label}, A ⊆ J → A.Nonempty → (J \ A).Nonempty →
    2 ≤ J.card → ∀ {r h g L : ℝ}, 0 < r → 0 < g → 0 ≤ L →
    LipschitzOnHull m q J L →
    (∀ i ∈ J, ∀ j ∈ J, dist (q i) (q j) ≤ r) →
    (∀ i ∈ A, ∀ j ∈ J \ A, g ≤ q j 1 - q i 1) →
    (∀ i ∈ A, ∀ j ∈ J \ A, q j 1 - q i 1 ≤ h) →
    h / ((J.card : ℝ) - 1) ≤ g →
    cutMass m J * h / (((J.card : ℝ) - 1) * r ^ 3) ≤ h + L * r := by
  intro m hm q s hq J A hAJ hA hB hcard r h g L hr hg hL hLip hdiam hgap hspan hdiv
  have hmean := mean_difference_upper hm q 1 hA hB hspan
  have hexternal := external_mean_difference_lower hm hAJ hA hB hL hLip hdiam
  have hbalance := mean_vertical_equation hq J A hAJ
  have hinter := internal_term_lower hm hq.1 hAJ hA hB hr hg hdiam hgap
  have hforce : cutMass m J * g / r ^ 3 ≤ h + L * r := by linarith
  have hcubic : cutMass m J * g ≤ (h + L * r) * r ^ 3 :=
    (div_le_iff₀ (pow_pos hr 3)).mp hforce
  have hn : 0 < (J.card : ℝ) - 1 := reduced_cardinality_real_pos J hcard
  have hmass : 0 < cutMass m J := cutMass_pos hm (hA.mono hAJ)
  have hsmall : h ≤ g * ((J.card : ℝ) - 1) := (div_le_iff₀ hn).mp hdiv
  have hproduct := mul_le_mul_of_nonneg_left hsmall hmass.le
  apply (div_le_iff₀ (mul_pos hn (pow_pos hr 3))).mpr
  calc
    cutMass m J * h ≤ cutMass m J * (g * ((J.card : ℝ) - 1)) := hproduct
    _ = ((J.card : ℝ) - 1) * (cutMass m J * g) := by ring
    _ ≤ ((J.card : ℝ) - 1) * ((h + L * r) * r ^ 3) :=
      mul_le_mul_of_nonneg_left hcubic hn.le
    _ = (h + L * r) * (((J.card : ℝ) - 1) * r ^ 3) := by ring

theorem exists_largest_cut_mean_evidence :
  ∀ {m : Masses}, PositiveMasses m →
  ∀ {q : Configuration} {s : ℝ}, IsSolution m s q →
  ∀ (J : Finset Label) (hJ : J.Nonempty), 2 ≤ J.card →
  ∀ {r L : ℝ}, 0 < r → 0 ≤ L → LipschitzOnHull m q J L →
    (∀ i ∈ J, ∀ j ∈ J, dist (q i) (q j) ≤ r) →
    0 < clusterCoordinateDiameter J (fun i => q i 1) hJ →
    ∃ (n : ℕ) (σ : Fin (n + 1) ≃ {i : Label // i ∈ J})
      (k : Fin n) (A B : Finset Label),
      J.card = n + 1 ∧ Monotone (fun l => q (σ l).val 1) ∧
      A ⊆ J ∧ B ⊆ J ∧ A.Nonempty ∧ B.Nonempty ∧
      B = J \ A ∧ Disjoint A B ∧ A ∪ B = J ∧
      (σ k.castSucc).val ∈ A ∧ (σ k.succ).val ∈ B ∧
      0 < adjacentGap (fun l => q (σ l).val 1) k ∧
      (∀ l : Fin n, adjacentGap (fun a => q (σ a).val 1) l ≤
        adjacentGap (fun a => q (σ a).val 1) k) ∧
      clusterCoordinateDiameter J (fun i => q i 1) hJ /
        (((J.card - 1 : ℕ) : ℝ)) ≤ adjacentGap (fun a => q (σ a).val 1) k ∧
      clusterCoordinateDiameter J (fun i => q i 1) hJ ≤
        (((J.card - 1 : ℕ) : ℝ)) * adjacentGap (fun a => q (σ a).val 1) k ∧
      (∀ i ∈ A, ∀ j ∈ B,
        adjacentGap (fun a => q (σ a).val 1) k ≤ q j 1 - q i 1) ∧
      (cutMean m q 1 B - cutMean m q 1 A =
        (1 / cutMass m A + 1 / cutMass m B) * internalCrossForce m q 1 J A +
          cutMean m (externalConfiguration m q J) 1 B -
            cutMean m (externalConfiguration m q J) 1 A) ∧
      |cutMean m (externalConfiguration m q J) 1 B -
        cutMean m (externalConfiguration m q J) 1 A| ≤ L * r ∧
      cutMass m J * adjacentGap (fun a => q (σ a).val 1) k / r ^ 3 ≤
        (1 / cutMass m A + 1 / cutMass m B) * internalCrossForce m q 1 J A ∧
      cutMean m q 1 B - cutMean m q 1 A ≤
        clusterCoordinateDiameter J (fun i => q i 1) hJ ∧
      cutMass m J * clusterCoordinateDiameter J (fun i => q i 1) hJ /
        (((J.card : ℝ) - 1) * r ^ 3) ≤
        clusterCoordinateDiameter J (fun i => q i 1) hJ + L * r := by
  intro m hm q s hq J hJ hcard r L hr hL hLip hdiam hh
  obtain ⟨n, σ, k, A, B, hcardEq, hmono, hAJ, hBJ, hA, hB,
    hBdef, hdisj, hcover, hleft, hright, hg, hlargest, havg, hbound, hgap⟩ :=
    cluster_largest_adjacent_gap_partition_sharp J (fun i => q i 1) hJ hcard hh
  have hB' : (J \ A).Nonempty := by simpa only [hBdef] using hB
  have hgap' : ∀ i ∈ A, ∀ j ∈ J \ A,
      adjacentGap (fun a => q (σ a).val 1) k ≤ q j 1 - q i 1 := by
    simpa only [hBdef] using hgap
  have hspan : ∀ i ∈ A, ∀ j ∈ J \ A,
      q j 1 - q i 1 ≤ clusterCoordinateDiameter J (fun i => q i 1) hJ := by
    intro i hi j hj
    exact cluster_coordinate_difference_le_diameter J (fun i => q i 1) hJ i j
      (hAJ hi) (Finset.mem_sdiff.mp hj).1
  have hcardOne : 1 ≤ J.card := by omega
  have havgReal : clusterCoordinateDiameter J (fun i => q i 1) hJ /
      ((J.card : ℝ) - 1) ≤ adjacentGap (fun a => q (σ a).val 1) k := by
    simpa only [Nat.cast_sub hcardOne, Nat.cast_one] using havg
  have hsharp := vertical_gap_sharp_from_cut hm hq hAJ hA hB' hcard
    hr hg hL hLip hdiam hgap' hspan havgReal
  refine ⟨n, σ, k, A, B, hcardEq, hmono, hAJ, hBJ, hA, hB,
    hBdef, hdisj, hcover, hleft, hright, hg, hlargest, havg, hbound, hgap,
    ?_, ?_, ?_, ?_, hsharp⟩
  · simpa only [hBdef] using mean_vertical_equation hq J A hAJ
  · simpa only [hBdef] using external_mean_difference_abs hm hAJ hA hB' hL hLip hdiam
  · simpa only [hBdef] using
      internal_term_lower hm hq.1 hAJ hA hB' hr hg hdiam hgap'
  · simpa only [hBdef] using mean_difference_upper hm q 1 hA hB' hspan

theorem cluster_vertical_gap_sharp :
  ∀ {m : Masses}, PositiveMasses m →
  ∀ {q : Configuration} {s : ℝ}, IsSolution m s q →
  ∀ (J : Finset Label) (hJ : J.Nonempty), 2 ≤ J.card →
  ∀ {r L : ℝ}, 0 < r → 0 ≤ L → LipschitzOnHull m q J L →
    (∀ i ∈ J, ∀ j ∈ J, dist (q i) (q j) ≤ r) →
    0 < clusterCoordinateDiameter J (fun i => q i 1) hJ →
    cutMass m J * clusterCoordinateDiameter J (fun i => q i 1) hJ /
      (((J.card : ℝ) - 1) * r ^ 3) ≤
      clusterCoordinateDiameter J (fun i => q i 1) hJ + L * r := by
  intro m hm q s hq J hJ hcard r L hr hL hLip hdiam hh
  obtain ⟨_n, _σ, _k, _A, _B, _hcardEq, _hmono, _hAJ, _hBJ, _hA, _hB,
    _hBdef, _hdisj, _hcover, _hleft, _hright, _hg, _hlargest, _havg, _hbound, _hgap,
    _hmean, _hexternal, _hinternal, _hspan, hsharp⟩ :=
    exists_largest_cut_mean_evidence hm hq J hJ hcard hr hL hLip hdiam hh
  exact hsharp

theorem separated_cluster_vertical_gap_sharp :
  ∀ {m : Masses}, PositiveMasses m →
  ∀ {q : Configuration} {s : ℝ}, IsSolution m s q →
  ∀ (J : Finset Label) (hJ : J.Nonempty), 2 ≤ J.card →
  ∀ {r δ : ℝ}, 0 < r → 0 < δ → r ≤ δ / 2 →
    (∀ i ∈ J, ∀ j ∈ J, dist (q i) (q j) ≤ r) →
    (∀ i ∈ J, ∀ j ∉ J, δ ≤ dist (q i) (q j)) →
    0 < clusterCoordinateDiameter J (fun i => q i 1) hJ →
    cutMass m J * clusterCoordinateDiameter J (fun i => q i 1) hJ /
      (((J.card : ℝ) - 1) * r ^ 3) ≤
      clusterCoordinateDiameter J (fun i => q i 1) hJ +
        (16 * (totalMass m - cutMass m J) / δ ^ 3) * r := by
  intro m hm q s hq J hJ hcard r δ hr hδ hrδ hdiam hsep hh
  have hmass : 0 ≤ totalMass m - cutMass m J := by
    have h := cutMass_complement m J
    have hp : 0 ≤ cutMass m (cutComplement J) :=
      Finset.sum_nonneg (fun j _ => (hm j).le)
    linarith
  have hL : 0 ≤ 16 * (totalMass m - cutMass m J) / δ ^ 3 :=
    div_nonneg (mul_nonneg (by norm_num) hmass) (pow_nonneg hδ.le 3)
  have hHull : ∀ z ∈ hull q J, ∀ j ∈ cutComplement J, δ / 2 ≤ dist z (q j) := by
    intro z hz j hj
    change z ∈ ClusterVirial.clusterHull q J at hz
    change j ∈ Finset.univ \ J at hj
    exact ClusterVirial.hull_exterior_separation q J hJ hrδ hdiam hsep z hz j hj
  exact cluster_vertical_gap_sharp hm hq J hJ hcard hr hL
    (lipschitzOnHull_of_separated hm q J hδ hHull) hdiam hh

theorem actual_proper_cluster_vertical_gap_sharp :
  ∀ {m : Masses}, PositiveMasses m →
  ∀ {q : Configuration} {s : ℝ}, IsSolution m s q →
  ∀ (J : Finset Label) (hJ : J.Nonempty) (hproper : J ≠ Finset.univ),
    2 ≤ J.card → diameter q J hJ ≤ separation q J hJ hproper / 2 →
    0 < clusterCoordinateDiameter J (fun i => q i 1) hJ →
    cutMass m J * clusterCoordinateDiameter J (fun i => q i 1) hJ /
      (((J.card : ℝ) - 1) * diameter q J hJ ^ 3) ≤
      clusterCoordinateDiameter J (fun i => q i 1) hJ +
        (16 * (totalMass m - cutMass m J) / separation q J hJ hproper ^ 3) *
          diameter q J hJ := by
  intro m hm q s hq J hJ hproper hcard hsmall hh
  exact separated_cluster_vertical_gap_sharp hm hq J hJ hcard
    (diameter_pos q hq.1 J hJ hcard) (separation_pos q hq.1 J hJ hproper) hsmall
    (fun _ hi _ hj => dist_le_diameter q J hJ hi hj)
    (fun _ hi _ hj => separation_le_cross q J hJ hproper hi hj) hh

theorem actual_full_cluster_vertical_gap_sharp :
  ∀ {m : Masses}, PositiveMasses m →
  ∀ {q : Configuration} {s : ℝ}, IsSolution m s q →
    0 < clusterCoordinateDiameter Finset.univ (fun i => q i 1) Finset.univ_nonempty →
    totalMass m * clusterCoordinateDiameter Finset.univ (fun i => q i 1)
      Finset.univ_nonempty /
      (3 * diameter q Finset.univ Finset.univ_nonempty ^ 3) ≤
      clusterCoordinateDiameter Finset.univ (fun i => q i 1) Finset.univ_nonempty := by
  intro m hm q s hq hh
  have hcard : 2 ≤ (Finset.univ : Finset Label).card := by norm_num
  have hr := diameter_pos q hq.1 Finset.univ Finset.univ_nonempty hcard
  have hsharp := cluster_vertical_gap_sharp hm hq Finset.univ Finset.univ_nonempty
    hcard hr (le_refl 0) (lipschitzOnHull_univ_zero m q)
    (fun _ hi _ hj => dist_le_diameter q Finset.univ Finset.univ_nonempty hi hj) hh
  simpa only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat,
    show (4 : ℝ) - 1 = 3 by norm_num, zero_mul, add_zero, cutMass, totalMass] using hsharp

theorem cluster_vertical_coefficient_three_from_sharp :
  ∀ {m : Masses}, PositiveMasses m →
  ∀ {q : Configuration} {s : ℝ}, IsSolution m s q →
  ∀ (J : Finset Label) (hJ : J.Nonempty), 2 ≤ J.card →
  ∀ {r L : ℝ}, 0 < r → 0 ≤ L → LipschitzOnHull m q J L →
    (∀ i ∈ J, ∀ j ∈ J, dist (q i) (q j) ≤ r) →
    0 < clusterCoordinateDiameter J (fun i => q i 1) hJ →
    cutMass m J ≤ 3 * r ^ 3 +
      3 * L * r ^ 4 / clusterCoordinateDiameter J (fun i => q i 1) hJ := by
  intro m hm q s hq J hJ hcard r L hr hL hLip hdiam hh
  let h : ℝ := clusterCoordinateDiameter J (fun i => q i 1) hJ
  have hh' : 0 < h := hh
  have hsharp := cluster_vertical_gap_sharp hm hq J hJ hcard hr hL hLip hdiam hh
  change cutMass m J * h / (((J.card : ℝ) - 1) * r ^ 3) ≤ h + L * r at hsharp
  have hn := reduced_cardinality_real_pos J hcard
  have hcardLe : J.card ≤ 4 := by
    calc
      J.card ≤ (Finset.univ : Finset Label).card := Finset.card_le_card (Finset.subset_univ J)
      _ = 4 := by simp
  have hcardReal : (J.card : ℝ) ≤ 4 := by exact_mod_cast hcardLe
  have hnThree : (J.card : ℝ) - 1 ≤ 3 := by linarith
  have hnonneg : 0 ≤ (h + L * r) * r ^ 3 :=
    mul_nonneg (add_nonneg hh'.le (mul_nonneg hL hr.le)) (pow_nonneg hr.le 3)
  have hscaled := (div_le_iff₀ (mul_pos hn (pow_pos hr 3))).mp hsharp
  have hcoefficient := mul_le_mul_of_nonneg_right hnThree hnonneg
  have hscale : cutMass m J * h ≤ 3 * ((h + L * r) * r ^ 3) := by
    calc
      cutMass m J * h ≤ (h + L * r) * (((J.card : ℝ) - 1) * r ^ 3) := hscaled
      _ = ((J.card : ℝ) - 1) * ((h + L * r) * r ^ 3) := by ring
      _ ≤ 3 * ((h + L * r) * r ^ 3) := hcoefficient
  have hquotient : cutMass m J ≤ (3 * r ^ 3 * h + 3 * L * r ^ 4) / h := by
    apply (le_div_iff₀ hh').mpr
    calc
      cutMass m J * h ≤ 3 * ((h + L * r) * r ^ 3) := hscale
      _ = 3 * r ^ 3 * h + 3 * L * r ^ 4 := by ring
  change cutMass m J ≤ 3 * r ^ 3 + 3 * L * r ^ 4 / h
  calc
    cutMass m J ≤ (3 * r ^ 3 * h + 3 * L * r ^ 4) / h := hquotient
    _ = 3 * r ^ 3 + 3 * L * r ^ 4 / h := by field_simp [ne_of_gt hh']

end FourBody.SourceGap295

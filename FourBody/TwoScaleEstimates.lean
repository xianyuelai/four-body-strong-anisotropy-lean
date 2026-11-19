import FourBody.Diameter
import FourBody.ClusterSelection
import FourBody.ScaleConstants
import FourBody.ExternalClusterBounds
import FourBody.StatementDefinitions
import FourBody.ClusterVertical
import FourBody.ClusterWidth

/-!
Formalization of the entire actual v2 Proposition 2.2, lines 212--338.
Baseline SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
All mass-dependent constants are the source's actual ScaleConstants.
The epsilon is the same epsilon definition used in the actual statement.
Closest-pair attainment is proved from the finite distinct-label pair set.
Cluster bounds are obtained from the actual Newtonian equations and the
checked exterior estimates; no scale conclusion is accepted as an input.
Actual build and audit evidence is recorded separately; source presence
alone is not a successful verification certificate.
-/

noncomputable section
open scoped BigOperators

namespace FourBody.TwoScale

theorem collisionFree_injective {q : Configuration} (hq : CollisionFree q) :
    Function.Injective q := by
  intro i j heq
  by_contra hij
  exact hq i j hij heq

/-- A real closest physical pair, constructed among actual distinct labels. -/
theorem exists_closest_pair (q : Configuration) (hq : CollisionFree q) :
    ∃ a b : Label, a ≠ b ∧ 0 < dist (q a) (q b) ∧
      ∀ i j : Label, i ≠ j → dist (q a) (q b) ≤ dist (q i) (q j) := by
  classical
  let P : Finset (Label × Label) := Finset.univ.filter (fun p => p.1 ≠ p.2)
  have hP : P.Nonempty := by
    refine ⟨((0 : Label), (1 : Label)), ?_⟩
    simp [P]
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image P
    (fun p : Label × Label => dist (q p.1) (q p.2)) hP
  have hab : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
  refine ⟨p.1, p.2, hab, collisionFree_dist_pos hq hab, ?_⟩
  intro i j hij
  exact hmin (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)

/-- A genuine cluster of at least two bodies has mass at least 2 m₀. -/
theorem subset_mass_ge_two_minimum (m : Masses) (hm : PositiveMasses m)
    (J : Finset Label) (hcard : 2 ≤ J.card) :
    2 * ScaleConstants.minimumMass m ≤ cutMass m J := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp
    (lt_of_lt_of_le (by decide : 1 < 2) hcard)
  have hsub : ({i, j} : Finset Label) ⊆ J := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hi
    · simpa only [Finset.mem_singleton.mp hk] using hj
  have hpair : m i + m j ≤ cutMass m J := by
    calc
      m i + m j = ∑ k ∈ ({i, j} : Finset Label), m k := by simp [hij]
      _ ≤ cutMass m J :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => (hm k).le)
  have hi0 := ScaleConstants.minimumMass_le m i
  have hj0 := ScaleConstants.minimumMass_le m j
  linarith

theorem epsilon_pos {s : ℝ} (hs : 0 < s) : 0 < epsilon s :=
  Real.rpow_pos_of_pos hs _

theorem epsilon_cube {s : ℝ} (hs : 0 < s) : epsilon s ^ 3 = s⁻¹ := by
  have hexponent : (-(1 : ℝ) / 3) * (3 : ℝ) = -1 := by ring
  calc
    epsilon s ^ 3 = s ^ ((-(1 : ℝ) / 3) * (3 : ℝ)) :=
      (Real.rpow_mul_natCast hs.le (-(1 : ℝ) / 3) 3).symm
    _ = s⁻¹ := by rw [hexponent, Real.rpow_neg_one]

theorem epsilon_eq_inv_root {s : ℝ} (hs : 0 < s) :
    epsilon s = (s ^ (1 / (3 : ℝ)))⁻¹ := by
  unfold epsilon
  rw [show -(1 : ℝ) / 3 = -(1 / (3 : ℝ)) by ring]
  change s ^ (-(1 / (3 : ℝ))) = (s ^ (1 / (3 : ℝ)))⁻¹
  rw [Real.rpow_neg hs.le]

theorem real_cube_root_cube {a : ℝ} (ha : 0 ≤ a) :
    (a ^ (1 / (3 : ℝ))) ^ 3 = a := by
  simpa only [one_div, Nat.cast_ofNat] using
    Real.rpow_inv_natCast_pow ha (by decide : (3 : ℕ) ≠ 0)

theorem mass_bridge (m : Masses) (J : Finset Label) :
    ClusterVirial.mass m J = cutMass m J := rfl

theorem field_bridge (m : Masses) (q : Configuration) (J : Finset Label) (z : Point) :
    ClusterVirial.externalField m q J z = ClusterVertical.externalField m q J z := rfl

/-- A selected physical cluster has a genuinely supplied external L and
virial estimate, with the source's precise error m₀/12. This is proved by
the full-cluster/isolated-cluster cases, not assumed as an analysis interface. -/
theorem isolated_cluster_estimates (m : Masses) (hm : PositiveMasses m)
    (q : Configuration) {s : ℝ} (hs : 1 ≤ s) (hq : IsSolution m s q)
    (J : Finset Label) (hcard : 2 ≤ J.card) {r : ℝ} (hr : 0 < r)
    (hdiam : ClusterSelection.BoundedCluster q J r)
    (hisolated : J = Finset.univ ∨ ClusterSelection.Separated q J r (ScaleConstants.T m)) :
    ∃ L : ℝ, 0 ≤ L ∧ L * r ^ 3 ≤ ScaleConstants.minimumMass m / 12 ∧
      cutMass m J ≤ s * r ^ 3 + L * r ^ 3 ∧
      ClusterVertical.LipschitzOnHull m q J L := by
  have hJ : J.Nonempty := Finset.card_pos.mp
    (lt_of_lt_of_le (by decide : 0 < 2) hcard)
  rcases hisolated with hfull | hsep
  · subst J
    refine ⟨0, le_refl 0, ?_, ?_, ClusterVertical.lipschitzOnHull_univ_zero m q⟩
    · simpa only [zero_mul] using
        (div_nonneg (ScaleConstants.minimumMass_pos m hm).le (by norm_num : (0 : ℝ) ≤ 12))
    · simpa only [cutMass, totalMass, zero_mul, add_zero] using
        ClusterVirial.full_cluster_virial_bound m hm q hs hq hr
          (fun i j => hdiam i (Finset.mem_univ _) j (Finset.mem_univ _))
  · let δ := ScaleConstants.T m * r
    let outside := totalMass m - cutMass m J
    let L := 16 * outside / δ ^ 3
    have hT := ScaleConstants.T_gt_two m hm
    have hδ : 0 < δ := mul_pos (ScaleConstants.T_pos m hm) hr
    have hrδ : r ≤ δ / 2 := by dsimp [δ]; nlinarith
    have hsep' : ∀ i ∈ J, ∀ j ∉ J, δ ≤ dist (q i) (q j) := hsep
    have houtside : 0 ≤ outside := by
      have hp : 0 ≤ cutMass m (cutComplement J) :=
        Finset.sum_nonneg (fun i _ => (hm i).le)
      have h := cutMass_complement m J
      dsimp [outside]
      linarith
    have houtsideM : outside ≤ totalMass m := by
      have hmass := cutMass_pos hm hJ
      dsimp [outside]
      linarith
    have hL : 0 ≤ L := div_nonneg (mul_nonneg (by norm_num) houtside) (pow_nonneg hδ.le 3)
    have hsmall : L * r ^ 3 ≤ ScaleConstants.minimumMass m / 12 :=
      ScaleConstants.exterior_smallness m hm houtsideM hr
    have hvirial : cutMass m J ≤ s * r ^ 3 + L * r ^ 3 := by
      simpa only [mass_bridge] using
        ClusterVirial.separated_cluster_virial_bound m hm q hs hq J hcard
          hr hδ hrδ hdiam hsep'
    have hHull : ∀ z ∈ ClusterVertical.hull q J, ∀ j ∈ cutComplement J,
        δ / 2 ≤ dist z (q j) := by
      simpa only [ClusterVertical.hull, ClusterVirial.clusterHull, cutComplement] using
        ClusterVirial.hull_exterior_separation q J hJ hrδ hdiam hsep'
    have hLip : ClusterVertical.LipschitzOnHull m q J L :=
      ClusterVertical.lipschitzOnHull_of_separated hm q J hδ hHull
    exact ⟨L, hL, hsmall, hvirial, hLip⟩

theorem cluster_cubic_lower (m : Masses) (hm : PositiveMasses m)
    (q : Configuration) {s : ℝ} (hs : 1 ≤ s) (hq : IsSolution m s q)
    (J : Finset Label) (hcard : 2 ≤ J.card) {r : ℝ} (hr : 0 < r)
    (hdiam : ClusterSelection.BoundedCluster q J r)
    (hisolated : J = Finset.univ ∨ ClusterSelection.Separated q J r (ScaleConstants.T m)) :
    ScaleConstants.minimumMass m ≤ s * r ^ 3 := by
  obtain ⟨L, _hL, hsmall, hvirial, _hLip⟩ :=
    isolated_cluster_estimates m hm q hs hq J hcard hr hdiam hisolated
  have hmass := subset_mass_ge_two_minimum m hm J hcard
  have hm0 := ScaleConstants.minimumMass_pos m hm
  linarith

theorem c₀_lower_from_cubic (m : Masses) (hm : PositiveMasses m)
    {s r d : ℝ} (hs : 0 < s) (hr : 0 < r) (hd : 0 ≤ d)
    (hcubic : ScaleConstants.minimumMass m ≤ s * r ^ 3)
    (hgrowth : r ≤ ScaleConstants.G m * d) :
    ScaleConstants.c₀ m * epsilon s ≤ d := by
  have hG := (ScaleConstants.constants_positive m hm).1
  have hm0 := ScaleConstants.minimumMass_pos m hm
  have hroot : (ScaleConstants.minimumMass m ^ (1 / (3 : ℝ)) * epsilon s) ^ 3 =
      ScaleConstants.minimumMass m / s := by
    rw [mul_pow, real_cube_root_cube hm0.le, epsilon_cube hs, div_eq_mul_inv]
  have hc : ScaleConstants.minimumMass m / s ≤ r ^ 3 :=
    (div_le_iff₀ hs).mpr (by nlinarith)
  have hpower :
      (ScaleConstants.minimumMass m ^ (1 / (3 : ℝ)) * epsilon s) ^ 3 ≤
        (ScaleConstants.G m * d) ^ 3 :=
    hroot.le.trans (hc.trans (pow_le_pow_left₀ hr.le hgrowth 3))
  have hlinear := le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0)
    (mul_nonneg hG.le hd) hpower
  unfold ScaleConstants.c₀
  calc
    ScaleConstants.minimumMass m ^ (1 / (3 : ℝ)) / ScaleConstants.G m * epsilon s =
        (ScaleConstants.minimumMass m ^ (1 / (3 : ℝ)) * epsilon s) / ScaleConstants.G m := by ring
    _ ≤ d := (div_le_iff₀ hG).mpr (by simpa only [mul_comm] using hlinear)

/-- The lower scale is first obtained at the actual closest pair, exactly
as in v2 lines 317--324, and is then transferred to every original pair. -/
theorem pair_distance_lower (m : Masses) (hm : PositiveMasses m)
    {s : ℝ} (hs : 1 ≤ s) {q : Configuration} (hq : IsSolution m s q)
    (i j : Label) (hij : i ≠ j) :
    ScaleConstants.c₀ m * epsilon s ≤ dist (q i) (q j) := by
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hs
  obtain ⟨a, b, hab, hd0, hclosest⟩ := exists_closest_pair q hq.1
  have hT : 1 ≤ ScaleConstants.T m := (by norm_num : (1 : ℝ) ≤ 2).trans
    (ScaleConstants.T_gt_two m hm).le
  obtain ⟨J, r, _ha, _hb, hcard, hr, _hd0r, hgrowth, hdiam, _hattained, hisolated⟩ :=
    ClusterSelection.selected_cluster_nontrivial q (collisionFree_injective hq.1)
      (ScaleConstants.T m) hT a b hab
  have hgrowth' : r ≤ ScaleConstants.G m * dist (q a) (q b) := hgrowth
  have hcubic := cluster_cubic_lower m hm q hs hq J hcard hr hdiam hisolated
  exact (c₀_lower_from_cubic m hm hspos hr hd0.le hcubic hgrowth').trans (hclosest i j hij)

/-- The horizontal range bound is converted to the paper's actual C ε / 2. -/
theorem horizontal_diameter_epsilon_bound (m : Masses) (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : IsSolution m s q) :
    coordinateDiameter (fun i => q i 0) ≤ ScaleConstants.C m * epsilon s / 2 := by
  calc
    coordinateDiameter (fun i => q i 0) ≤ 3 * (totalMass m / s) ^ (1 / (3 : ℝ)) :=
      diameter_x hm hs hq
    _ = ScaleConstants.C m * epsilon s / 2 := by
      rw [Real.div_rpow (totalMass_pos hm).le hs.le, epsilon_eq_inv_root hs]
      unfold ScaleConstants.C
      ring

theorem coordinate_abs_difference_le_diameter (t : Label → ℝ) (i j : Label) :
    |t i - t j| ≤ coordinateDiameter t := by
  apply abs_le.mpr
  constructor
  · have h := coordinate_difference_le_diameter t i j
    linarith
  · exact coordinate_difference_le_diameter t j i

/-- The actual attained cluster diameter supplies the large vertical span. -/
theorem selected_cluster_wide_vertical (m : Masses) (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : IsSolution m s q)
    (i j : Label) {J : Finset Label} (hJ : J.Nonempty) {r : ℝ} (hr : 0 < r)
    (hdlarge : ScaleConstants.C m * epsilon s ≤ dist (q i) (q j))
    (hpairr : dist (q i) (q j) ≤ r)
    (hattained : ∃ a ∈ J, ∃ b ∈ J, dist (q a) (q b) = r) :
    r / 2 ≤ clusterCoordinateDiameter J (fun k => q k 1) hJ ∧
      0 < clusterCoordinateDiameter J (fun k => q k 1) hJ := by
  obtain ⟨a, ha, b, hb, hatt⟩ := hattained
  have hhorizontal := horizontal_diameter_epsilon_bound m hm hs hq
  have hxy : |q a 0 - q b 0| ≤ r / 2 := by
    have hcoord := coordinate_abs_difference_le_diameter (fun k => q k 0) a b
    linarith
  exact cluster_vertical_diameter_ge_half_of_wide_pair q J hJ a b ha hb hr hatt hxy

theorem vertical_error_le_six {r h L : ℝ} (hr : 0 < r) (hh : 0 < h)
    (hwide : r / 2 ≤ h) (hL : 0 ≤ L) :
    3 * L * r ^ 4 / h ≤ 6 * L * r ^ 3 := by
  apply (div_le_iff₀ hh).mpr
  have hgeom : r ≤ 2 * h := by linarith
  have hfactor : 0 ≤ 3 * L * r ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num) hL) (pow_nonneg hr.le 3)
  calc
    3 * L * r ^ 4 = (3 * L * r ^ 3) * r := by ring
    _ ≤ (3 * L * r ^ 3) * (2 * h) := mul_le_mul_of_nonneg_left hgeom hfactor
    _ = (6 * L * r ^ 3) * h := by ring

theorem c₁_lower_from_cubic (m : Masses) (hm : PositiveMasses m)
    {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d)
    (hcubic : ScaleConstants.minimumMass m / 2 ≤ r ^ 3)
    (hgrowth : r ≤ ScaleConstants.G m * d) :
    ScaleConstants.c₁ m ≤ d := by
  have hG := (ScaleConstants.constants_positive m hm).1
  have hm0 := ScaleConstants.minimumMass_pos m hm
  have hroot : ((ScaleConstants.minimumMass m / 2) ^ (1 / (3 : ℝ))) ^ 3 =
      ScaleConstants.minimumMass m / 2 :=
    real_cube_root_cube (div_nonneg hm0.le (by norm_num))
  have hpower : ((ScaleConstants.minimumMass m / 2) ^ (1 / (3 : ℝ))) ^ 3 ≤
      (ScaleConstants.G m * d) ^ 3 :=
    hroot.le.trans (hcubic.trans (pow_le_pow_left₀ hr.le hgrowth 3))
  have hlinear := le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0)
    (mul_nonneg hG.le hd) hpower
  unfold ScaleConstants.c₁
  exact (div_le_iff₀ hG).mpr (by simpa only [mul_comm] using hlinear)

/-- A pair outside the strict small-scale alternative has the source's
mass-dependent positive macroscopic lower bound, via the constructed J. -/
theorem pair_distance_macroscopic (m : Masses) (hm : PositiveMasses m)
    {s : ℝ} (hs : 1 ≤ s) {q : Configuration} (hq : IsSolution m s q)
    (i j : Label) (hij : i ≠ j)
    (hdlarge : ScaleConstants.C m * epsilon s ≤ dist (q i) (q j)) :
    ScaleConstants.c₁ m ≤ dist (q i) (q j) := by
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hs
  have hT : 1 ≤ ScaleConstants.T m := (by norm_num : (1 : ℝ) ≤ 2).trans
    (ScaleConstants.T_gt_two m hm).le
  obtain ⟨J, r, _hi, _hj, hcard, hr, hpairr, hgrowth, hdiam, hattained, hisolated⟩ :=
    ClusterSelection.selected_cluster_nontrivial q (collisionFree_injective hq.1)
      (ScaleConstants.T m) hT i j hij
  have hJ : J.Nonempty := Finset.card_pos.mp
    (lt_of_lt_of_le (by decide : 0 < 2) hcard)
  have hwide := selected_cluster_wide_vertical m hm hspos hq i j hJ hr hdlarge hpairr hattained
  obtain ⟨L, hL, hsmall, _hvirial, hLip⟩ :=
    isolated_cluster_estimates m hm q hs hq J hcard hr hdiam hisolated
  have hvertical := ClusterVertical.vertical_cluster_bound hm hq J hJ hr hL hLip hdiam hwide.2
  have herror := vertical_error_le_six hr hwide.2 hwide.1 hL
  have hmass := subset_mass_ge_two_minimum m hm J hcard
  have hcubic : ScaleConstants.minimumMass m / 2 ≤ r ^ 3 := by
    linarith only [hvertical, herror, hsmall, hmass]
  have hgrowth' : r ≤ ScaleConstants.G m * dist (q i) (q j) := hgrowth
  exact c₁_lower_from_cubic m hm hr dist_nonneg hcubic hgrowth'

/-- Entire v2 Proposition 2.2, with its original s≥1 and strict alternative.
This is a theorem about every actual collision-free solution and every
distinct pair, with all constants depending on the fixed positive masses. -/
theorem twoScaleEstimates (m : Masses) (hm : PositiveMasses m)
    {s : ℝ} (hs : 1 ≤ s) {q : Configuration} (hq : IsSolution m s q)
    (i j : Label) (hij : i ≠ j) :
    ScaleConstants.c₀ m * epsilon s ≤ dist (q i) (q j) ∧
      (dist (q i) (q j) < ScaleConstants.C m * epsilon s ∨
        ScaleConstants.c₁ m ≤ dist (q i) (q j)) := by
  refine ⟨pair_distance_lower m hm hs hq i j hij, ?_⟩
  by_cases hsmall : dist (q i) (q j) < ScaleConstants.C m * epsilon s
  · exact Or.inl hsmall
  · exact Or.inr (pair_distance_macroscopic m hm hs hq i j hij (le_of_not_gt hsmall))

end FourBody.TwoScale

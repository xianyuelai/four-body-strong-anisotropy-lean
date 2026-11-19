import FourBody.Geometry
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
Finite-cluster identities used by v2 Proposition 2.2, before
`eq:cluster-virial-bound`. The points are genuine Euclidean vectors and
the pairs satisfy `i < j`, with both labels in the actual cluster `J`.

Reuse/adaptation sources (read only): DominantFiveBody/Coordinates.lean,
ForceBalance.lean, RelativeMassMetric.lean, SectionThreeIdentities.lean.
The mass-centering proof adapts `weightedPosition_translate` and
`centered_weightedPosition_zero`. Bilinear finite-sum factoring adapts
`massWeightedVariance_identity`; pair cancellation and mass weighting
follow ForceBalance. The old acceleration points from i to j, whereas
this paper's force points from j to i, so its sign is deliberately reversed.
The source-specific eps/mass-ratio assumptions are not imported.

The concluding estimate has an explicit pointwise external Lipschitz
premise. Deriving that premise with the manuscript's constant
16 (M - M_J) / delta^3 is a separate analytical obligation.
-/

noncomputable section

open scoped BigOperators

namespace FourBody.ClusterVirial

def mass (m : Masses) (J : Finset Label) : ℝ := ∑ i ∈ J, m i

def centroid (m : Masses) (q : Configuration) (J : Finset Label) : Point :=
  (mass m J)⁻¹ • ∑ i ∈ J, m i • q i

def centered (m : Masses) (q : Configuration) (J : Finset Label) (i : Label) : Point :=
  q i - centroid m q J

def pairs (J : Finset Label) : Finset (Label × Label) :=
  (J ×ˢ J).filter (fun p => p.1 < p.2)

@[simp] theorem mem_pairs (J : Finset Label) (i j : Label) :
    (i, j) ∈ pairs J ↔ i ∈ J ∧ j ∈ J ∧ i < j := by
  simp [pairs, and_assoc]

def inertia (m : Masses) (q : Configuration) (J : Finset Label) : ℝ :=
  ∑ i ∈ J, m i * ‖centered m q J i‖ ^ 2

def potential (m : Masses) (q : Configuration) (J : Finset Label) : ℝ :=
  ∑ p ∈ pairs J, m p.1 * m p.2 / dist (q p.1) (q p.2)

def pairVariance (m : Masses) (q : Configuration) (J : Finset Label) : ℝ :=
  ∑ p ∈ pairs J, m p.1 * m p.2 * dist (q p.1) (q p.2) ^ 2

def internalForce (m : Masses) (q : Configuration) (J : Finset Label)
    (i : Label) : Point :=
  ∑ j ∈ J.erase i, (m j / dist (q i) (q j) ^ 3) • (q i - q j)

def externalField (m : Masses) (q : Configuration) (J : Finset Label)
    (z : Point) : Point :=
  ∑ j ∈ Finset.univ \ J, (m j / dist z (q j) ^ 3) • (z - q j)

def externalPairing (m : Masses) (q : Configuration) (J : Finset Label) : ℝ :=
  ∑ i ∈ J, m i * inner ℝ (centered m q J i) (externalField m q J (q i))

theorem mass_pos (m : Masses) (hm : PositiveMasses m)
    (J : Finset Label) (hJ : J.Nonempty) : 0 < mass m J := by
  exact Finset.sum_pos (fun i _ => hm i) hJ

/-- Direct finite-J generalization of the old `weightedPosition_translate` proof. -/
theorem weighted_sum_translate (m : Masses) (q : Configuration)
    (J : Finset Label) (b : Point) :
    (∑ i ∈ J, m i • (q i - b)) =
      (∑ i ∈ J, m i • q i) - mass m J • b := by
  simp [mass, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]

/-- The precise finite-cluster adaptation of the old centering identities. -/
theorem centered_mass_sum_zero (m : Masses) (q : Configuration)
    (J : Finset Label) (hM : mass m J ≠ 0) :
    (∑ i ∈ J, m i • centered m q J i) = 0 := by
  change (∑ i ∈ J, m i • (q i - centroid m q J)) = 0
  rw [weighted_sum_translate]
  change (∑ i ∈ J, m i • q i) -
    mass m J • ((mass m J)⁻¹ • (∑ i ∈ J, m i • q i)) = 0
  rw [smul_smul, mul_inv_cancel₀ hM, one_smul, sub_self]

theorem centered_difference (m : Masses) (q : Configuration)
    (J : Finset Label) (i j : Label) :
    centered m q J i - centered m q J j = q i - q j := by
  unfold centered
  abel

theorem centered_distance (m : Masses) (q : Configuration)
    (J : Finset Label) (i j : Label) :
    ‖centered m q J i - centered m q J j‖ = dist (q i) (q j) := by
  rw [centered_difference, dist_eq_norm]

/-- Group a double sum over the actual finite cluster into increasing pairs. -/
theorem sum_eq_pair_sum (J : Finset Label) (f : Label → Label → ℝ)
    (hdiag : ∀ i, f i i = 0) :
    (∑ i ∈ J, ∑ j ∈ J, f i j) =
      ∑ p ∈ pairs J, (f p.1 p.2 + f p.2 p.1) := by
  have hswap :
      (∑ p ∈ J ×ˢ J, if p.1 < p.2 then f p.2 p.1 else 0) =
        ∑ p ∈ J ×ˢ J, if p.2 < p.1 then f p.1 p.2 else 0 := by
    apply Finset.sum_equiv (Equiv.prodComm Label Label)
    · intro p
      simp [Finset.mem_product, and_comm]
    · intro p _
      rfl
  rw [← Finset.sum_product']
  symm
  calc
    (∑ p ∈ pairs J, (f p.1 p.2 + f p.2 p.1)) =
        (∑ p ∈ J ×ˢ J, if p.1 < p.2 then f p.1 p.2 else 0) +
          ∑ p ∈ J ×ˢ J, if p.1 < p.2 then f p.2 p.1 else 0 := by
      rw [pairs, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p.1 < p.2 <;> simp [hp]
    _ = (∑ p ∈ J ×ˢ J, if p.1 < p.2 then f p.1 p.2 else 0) +
          ∑ p ∈ J ×ˢ J, if p.2 < p.1 then f p.1 p.2 else 0 := by
      rw [hswap]
    _ = ∑ p ∈ J ×ˢ J, f p.1 p.2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      rcases lt_trichotomy p.1 p.2 with hij | hij | hji
      · simp [hij, not_lt_of_ge hij.le]
      · simp [hij, hdiag]
      · simp [hji, not_lt_of_ge hji.le]

/-- Bilinear pair grouping, used for both the variance and Newtonian virial. -/
theorem pair_inner_identity (J : Finset Label) (m : Masses)
    (p : Configuration) (a : Label → Label → ℝ)
    (hsymm : ∀ i j, a j i = a i j) :
    (∑ i ∈ J, ∑ j ∈ J,
      m i * m j * a i j * inner ℝ (p i) (p i - p j)) =
      ∑ ij ∈ pairs J,
        m ij.1 * m ij.2 * a ij.1 ij.2 * ‖p ij.1 - p ij.2‖ ^ 2 := by
  rw [sum_eq_pair_sum J _ (fun i => by simp)]
  apply Finset.sum_congr rfl
  intro ij _
  have hinner : inner ℝ (p ij.1) (p ij.1 - p ij.2) +
      inner ℝ (p ij.2) (p ij.2 - p ij.1) = ‖p ij.1 - p ij.2‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    ring
  calc
    _ = (m ij.1 * m ij.2 * a ij.1 ij.2) *
        (inner ℝ (p ij.1) (p ij.1 - p ij.2) +
          inner ℝ (p ij.2) (p ij.2 - p ij.1)) := by
      rw [hsymm ij.1 ij.2]
      ring
    _ = _ := by rw [hinner]

theorem centered_inner_const_zero (m : Masses) (q : Configuration)
    (J : Finset Label) (hM : mass m J ≠ 0) (z : Point) :
    (∑ i ∈ J, m i * inner ℝ (centered m q J i) z) = 0 := by
  calc
    _ = inner ℝ (∑ i ∈ J, m i • centered m q J i) z := by
      simp only [sum_inner, real_inner_smul_left]
    _ = 0 := by rw [centered_mass_sum_zero m q J hM, inner_zero_left]

/-- The source's identity `M_J I_J = sum_{i<j} m_i m_j r_ij^2`. -/
theorem weighted_variance (m : Masses) (q : Configuration)
    (J : Finset Label) (hM : mass m J ≠ 0) :
    mass m J * inertia m q J = pairVariance m q J := by
  let p := centered m q J
  have hp : (∑ i ∈ J, m i • p i) = 0 := centered_mass_sum_zero m q J hM
  have hi (i : Label) :
      (∑ j ∈ J, m i * m j * inner ℝ (p i) (p i - p j)) =
        m i * mass m J * ‖p i‖ ^ 2 := by
    have hsum : (∑ j ∈ J, m j • (p i - p j)) = mass m J • p i := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hp,
        sub_zero, mass]
    calc
      _ = m i * inner ℝ (p i) (∑ j ∈ J, m j • (p i - p j)) := by
        simp only [inner_sum, real_inner_smul_right, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        rw [hsum, real_inner_smul_right, real_inner_self_eq_norm_sq]
        ring
  have hpair := pair_inner_identity J m p (fun _ _ => 1) (fun _ _ => rfl)
  simp only [mul_one] at hpair
  simp_rw [hi] at hpair
  calc
    mass m J * inertia m q J = ∑ i ∈ J, m i * mass m J * ‖p i‖ ^ 2 := by
      unfold inertia
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [p]
      ring
    _ = ∑ ij ∈ pairs J, m ij.1 * m ij.2 * ‖p ij.1 - p ij.2‖ ^ 2 := hpair
    _ = pairVariance m q J := by
      unfold pairVariance
      apply Finset.sum_congr rfl
      intro ij _
      dsimp [p]
      rw [centered_distance]

theorem weighted_variance_div_mass (m : Masses) (q : Configuration)
    (J : Finset Label) (hM : mass m J ≠ 0) :
    inertia m q J = pairVariance m q J / mass m J := by
  apply (eq_div_iff hM).mpr
  simpa [mul_comm] using weighted_variance m q J hM

/-- At least two distinct physical positions make the actual centered inertia positive. -/
theorem inertia_pos (m : Masses) (hm : PositiveMasses m)
    (q : Configuration) (hq : CollisionFree q)
    (J : Finset Label) (hcard : 2 ≤ J.card) : 0 < inertia m q J := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp
    (lt_of_lt_of_le (by decide : 1 < 2) hcard)
  have hwitness : ∃ k ∈ J, centered m q J k ≠ 0 := by
    by_cases hpi : centered m q J i = 0
    · refine ⟨j, hj, ?_⟩
      intro hpj
      apply hq i j hij
      exact (sub_eq_zero.mp hpi).trans (sub_eq_zero.mp hpj).symm
    · exact ⟨i, hi, hpi⟩
  obtain ⟨k, hk, hpk⟩ := hwitness
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hm i).le (sq_nonneg _))
    ⟨k, hk, mul_pos (hm k) (pow_pos (norm_pos_iff.mpr hpk) 2)⟩

/-- Internal forces paired with centered positions give the actual Newtonian potential. -/
theorem internal_virial (m : Masses) (q : Configuration) (hq : CollisionFree q)
    (J : Finset Label) :
    (∑ i ∈ J, m i * inner ℝ (centered m q J i) (internalForce m q J i)) =
      potential m q J := by
  let p := centered m q J
  let a : Label → Label → ℝ := fun i j => 1 / dist (q i) (q j) ^ 3
  have hfull :
      (∑ i ∈ J, m i * inner ℝ (p i) (internalForce m q J i)) =
        ∑ i ∈ J, ∑ j ∈ J, m i * m j * a i j * inner ℝ (p i) (p i - p j) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold internalForce
    simp only [inner_sum, real_inner_smul_right, Finset.mul_sum]
    calc
      _ = ∑ j ∈ J.erase i, m i * m j * a i j * inner ℝ (p i) (p i - p j) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp [a, p]
        rw [centered_difference]
        ring
      _ = _ := Finset.sum_erase J (by simp)
  rw [hfull, pair_inner_identity J m p a (by intro i j; simp [a, dist_comm])]
  unfold potential
  apply Finset.sum_congr rfl
  intro ij hij
  have hlt : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
  have hd := ne_of_gt (collisionFree_dist_pos hq (ne_of_lt hlt))
  dsimp [a, p]
  rw [centered_distance]
  field_simp [hd]

/-- Each physical pair is at distance at most r; no global scale conclusion is assumed. -/
theorem potential_ge_mass_inertia_div_cube (m : Masses) (hm : PositiveMasses m)
    (q : Configuration) (hq : CollisionFree q) (J : Finset Label)
    (hM : mass m J ≠ 0) {r : ℝ} (hr : 0 < r)
    (hdiam : ∀ i ∈ J, ∀ j ∈ J, dist (q i) (q j) ≤ r) :
    (mass m J / r ^ 3) * inertia m q J ≤ potential m q J := by
  calc
    (mass m J / r ^ 3) * inertia m q J =
        pairVariance m q J / r ^ 3 := by
      rw [← weighted_variance m q J hM]
      ring
    _ = ∑ ij ∈ pairs J,
        (m ij.1 * m ij.2 * dist (q ij.1) (q ij.2) ^ 2) / r ^ 3 := by
      rw [pairVariance, Finset.sum_div]
    _ ≤ potential m q J := by
      unfold potential
      apply Finset.sum_le_sum
      intro ij hij
      obtain ⟨hi, hj, hlt⟩ := (mem_pairs J ij.1 ij.2).mp hij
      have hd : 0 < dist (q ij.1) (q ij.2) := collisionFree_dist_pos hq (ne_of_lt hlt)
      have hcube : dist (q ij.1) (q ij.2) ^ 3 ≤ r ^ 3 :=
        pow_le_pow_left₀ hd.le (hdiam ij.1 hi ij.2 hj) 3
      apply (div_le_div_iff₀ (pow_pos hr 3) hd).mpr
      calc
        _ = (m ij.1 * m ij.2) * dist (q ij.1) (q ij.2) ^ 3 := by ring
        _ ≤ (m ij.1 * m ij.2) * r ^ 3 :=
          mul_le_mul_of_nonneg_left hcube (mul_nonneg (hm ij.1).le (hm ij.2).le)

theorem force_eq_internal_add_external (m : Masses) (q : Configuration)
    (J : Finset Label) {i : Label} (hi : i ∈ J) :
    force m q i = internalForce m q J i + externalField m q J (q i) := by
  have hdis : Disjoint (J.erase i) (Finset.univ \ J) := by
    apply Finset.disjoint_left.mpr
    intro j hj hext
    exact (Finset.mem_sdiff.mp hext).2 (Finset.mem_erase.mp hj).2
  have hunion : J.erase i ∪ (Finset.univ \ J) = Finset.univ.erase i := by
    ext j
    by_cases hji : j = i <;> by_cases hj : j ∈ J <;> simp_all
  unfold force internalForce externalField
  rw [← hunion, Finset.sum_union hdis]

/-- Subtracting the field at the centroid cancels exactly, before estimating it. -/
theorem external_pairing_subtract_centroid (m : Masses) (q : Configuration)
    (J : Finset Label) (hM : mass m J ≠ 0) :
    externalPairing m q J = ∑ i ∈ J, m i * inner ℝ (centered m q J i)
      (externalField m q J (q i) - externalField m q J (centroid m q J)) := by
  simp only [inner_sub_right, mul_sub, Finset.sum_sub_distrib,
    centered_inner_const_zero m q J hM, sub_zero, externalPairing]

/-- The natural pointwise Lipschitz consequence gives the source's error bound. -/
theorem external_pairing_abs_le (m : Masses) (hm : PositiveMasses m)
    (q : Configuration) (J : Finset Label) (hM : mass m J ≠ 0) {L : ℝ}
    (hLip : ∀ i ∈ J,
      ‖externalField m q J (q i) - externalField m q J (centroid m q J)‖ ≤
        L * ‖centered m q J i‖) :
    |externalPairing m q J| ≤ L * inertia m q J := by
  rw [external_pairing_subtract_centroid m q J hM]
  calc
    _ ≤ ∑ i ∈ J, |m i * inner ℝ (centered m q J i)
        (externalField m q J (q i) - externalField m q J (centroid m q J))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ J, m i * (L * ‖centered m q J i‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_pos (hm i)]
      apply mul_le_mul_of_nonneg_left _ (hm i).le
      calc
        _ ≤ ‖centered m q J i‖ *
            ‖externalField m q J (q i) - externalField m q J (centroid m q J)‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ ‖centered m q J i‖ * (L * ‖centered m q J i‖) :=
          mul_le_mul_of_nonneg_left (hLip i hi) (norm_nonneg _)
        _ = _ := by ring
    _ = L * inertia m q J := by
      unfold inertia
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem anisotropy_quadratic_le {s : ℝ} (hs : 1 ≤ s) (p : Point) :
    inner ℝ p (anisotropy s p) ≤ s * ‖p‖ ^ 2 := by
  have hnorm : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
    simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq p
  have hinner : inner ℝ p (anisotropy s p) = s * (p 0) ^ 2 + (p 1) ^ 2 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, anisotropy]
    ring
  rw [hinner, hnorm]
  nlinarith [sq_nonneg (p 1)]

/-- The physical solution equation, paired and recentered without dropping terms. -/
theorem solution_cluster_virial (m : Masses) (q : Configuration) {s : ℝ}
    (hq : IsSolution m s q) (J : Finset Label) (hM : mass m J ≠ 0) :
    potential m q J + externalPairing m q J =
      ∑ i ∈ J, m i * inner ℝ (centered m q J i)
        (anisotropy s (centered m q J i)) := by
  have hpaired : (∑ i ∈ J, m i * inner ℝ (centered m q J i) (force m q i)) =
      potential m q J + externalPairing m q J := by
    calc
      _ = ∑ i ∈ J, m i * inner ℝ (centered m q J i)
          (internalForce m q J i + externalField m q J (q i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [force_eq_internal_add_external m q J hi]
      _ = _ := by
        simp only [inner_add_right, mul_add, Finset.sum_add_distrib,
          internal_virial m q hq.1 J, externalPairing]
  rw [← hpaired]
  have hqsplit (i : Label) : q i = centered m q J i + centroid m q J := by
    unfold centered
    abel
  calc
    _ = ∑ i ∈ J, m i * inner ℝ (centered m q J i) (anisotropy s (q i)) := by
      simp only [hq.2]
    _ = (∑ i ∈ J, m i * inner ℝ (centered m q J i)
        (anisotropy s (centered m q J i))) +
        ∑ i ∈ J, m i * inner ℝ (centered m q J i)
          (anisotropy s (centroid m q J)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hqsplit i, LinearMap.map_add, inner_add_right, mul_add]
    _ = _ := by
      rw [centered_inner_const_zero m q J hM, add_zero]

/-- Equation `eq:cluster-virial-bound`, with its external Lipschitz premise exposed. -/
theorem cluster_virial_bound (m : Masses) (hm : PositiveMasses m)
    (q : Configuration) {s : ℝ} (hs : 1 ≤ s) (hq : IsSolution m s q)
    (J : Finset Label) (hcard : 2 ≤ J.card) {r L : ℝ} (hr : 0 < r)
    (hdiam : ∀ i ∈ J, ∀ j ∈ J, dist (q i) (q j) ≤ r)
    (hLip : ∀ i ∈ J,
      ‖externalField m q J (q i) - externalField m q J (centroid m q J)‖ ≤
        L * ‖centered m q J i‖) :
    mass m J ≤ s * r ^ 3 + L * r ^ 3 := by
  have hJ : J.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hcard)
  have hM := ne_of_gt (mass_pos m hm J hJ)
  have hI := inertia_pos m hm q hq.1 J hcard
  have hlow := potential_ge_mass_inertia_div_cube m hm q hq.1 J hM hr hdiam
  have herror := neg_le_of_abs_le (external_pairing_abs_le m hm q J hM hLip)
  have hsolution := solution_cluster_virial m q hq J hM
  have hquadratic :
      (∑ i ∈ J, m i * inner ℝ (centered m q J i)
        (anisotropy s (centered m q J i))) ≤ s * inertia m q J := by
    unfold inertia
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ m i * (s * ‖centered m q J i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (anisotropy_quadratic_le hs _) (hm i).le
      _ = _ := by ring
  have hupper : potential m q J ≤ (s + L) * inertia m q J := by
    linarith
  have hcancel : mass m J / r ^ 3 ≤ s + L :=
    (mul_le_mul_iff_of_pos_right hI).mp (hlow.trans hupper)
  have hfinal := (div_le_iff₀ (pow_pos hr 3)).mp hcancel
  nlinarith

@[simp] theorem mass_univ (m : Masses) : mass m Finset.univ = totalMass m := rfl

/-- The manuscript's full cluster has no exterior field, without any separation premise. -/
@[simp] theorem externalField_univ (m : Masses) (q : Configuration) (z : Point) :
    externalField m q Finset.univ z = 0 := by
  simp [externalField]

@[simp] theorem externalPairing_univ (m : Masses) (q : Configuration) :
    externalPairing m q Finset.univ = 0 := by
  simp [externalPairing]

/-- Full-cluster instance of the source virial bound, with the exterior error exactly zero. -/
theorem full_cluster_virial_bound (m : Masses) (hm : PositiveMasses m)
    (q : Configuration) {s : ℝ} (hs : 1 ≤ s) (hq : IsSolution m s q)
    {r : ℝ} (hr : 0 < r) (hdiam : ∀ i j, dist (q i) (q j) ≤ r) :
    totalMass m ≤ s * r ^ 3 := by
  simpa using cluster_virial_bound m hm q hs hq Finset.univ
    (by decide : 2 ≤ (Finset.univ : Finset Label).card) hr
    (fun i _ j _ => hdiam i j) (L := 0) (by simp)

end FourBody.ClusterVirial

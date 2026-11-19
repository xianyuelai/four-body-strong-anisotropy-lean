import FourBody.ClusterExtrema
import FourBody.ClusterSelection
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
STATIC, not yet elaborated. Proposed final import FourBody.ClusterExtrema.
The frozen v2's closest-crosspair enlargement, lines 301--313. Every step
uses the genuine finite minimum, and the radius is always the genuine
finite maximum. No separation, exhaustion, or growth certificate is an
input. Four fixed labels give at most two strict cardinality increases.
-/
set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace FourBody.SourceFaithfulCluster

theorem insert_diameter_le_old_plus_nearest (q : Configuration)
    (J : Finset Label) (hJ : J.Nonempty) (hproper : J ≠ Finset.univ)
    (a b : Label) (ha : a ∈ J)
    (hnearest : dist (q a) (q b) = separation q J hJ hproper) :
    diameter q (insert b J) (hJ.mono (Finset.subset_insert b J)) ≤
      diameter q J hJ + separation q J hJ hproper := by
  classical
  have hsep := separation_nonneg q J hJ hproper
  have hr := diameter_nonneg q J hJ
  have hnew : ∀ x ∈ J, dist (q b) (q x) ≤
      diameter q J hJ + separation q J hJ hproper := by
    intro x hx
    have htriangle := dist_triangle (q b) (q a) (q x)
    have hdiam := dist_le_diameter q J hJ ha hx
    rw [dist_comm (q b) (q a), hnearest] at htriangle
    linarith
  apply diameter_le_of_all_dist_le
  intro x hx y hy
  rcases Finset.mem_insert.mp hx with hxB | hxJ
  · rcases Finset.mem_insert.mp hy with hyB | hyJ
    · subst x
      subst y
      simp only [dist_self]
      exact add_nonneg hr hsep
    · subst x
      exact hnew y hyJ
  · rcases Finset.mem_insert.mp hy with hyB | hyJ
    · subst y
      rw [dist_comm]
      exact hnew x hxJ
    · exact (dist_le_diameter q J hJ hxJ hyJ).trans (le_add_of_nonneg_right hsep)

/-- A public proof of the actual closest-point step, including its card
increase, weak diameter bound and the strict source bound. -/
theorem nearest_enlargement (q : Configuration) (J : Finset Label)
    (hJ : J.Nonempty) (hproper : J ≠ Finset.univ) (T : ℝ)
    (hclose : separation q J hJ hproper < T * diameter q J hJ) :
    ∃ a ∈ J, ∃ b ∉ J,
      dist (q a) (q b) = separation q J hJ hproper ∧
      (insert b J).card = J.card + 1 ∧
      diameter q J hJ ≤ diameter q (insert b J)
        (hJ.mono (Finset.subset_insert b J)) ∧
      diameter q (insert b J) (hJ.mono (Finset.subset_insert b J)) ≤
        diameter q J hJ + separation q J hJ hproper ∧
      diameter q (insert b J) (hJ.mono (Finset.subset_insert b J)) <
        (1 + T) * diameter q J hJ := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := separation_attained q J hJ hproper
  have hbound := insert_diameter_le_old_plus_nearest q J hJ hproper a b ha hab
  refine ⟨a, ha, b, hb, hab, Finset.card_insert_of_notMem hb,
    diameter_mono q J (insert b J) hJ
      (hJ.mono (Finset.subset_insert b J)) (Finset.subset_insert b J), hbound, ?_⟩
  nlinarith

theorem pair_diameter (q : Configuration) (i j : Label) :
    diameter q {i, j} (by simp) = dist (q i) (q j) := by
  classical
  apply diameter_eq_of_attained
  · intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · simpa only [ha, hb, dist_self] using (dist_nonneg : 0 ≤ dist (q i) (q j))
    · simpa only [ha, hb] using (le_refl (dist (q i) (q j)))
    · simpa only [ha, hb] using (le_of_eq (dist_comm (q j) (q i)))
    · simpa only [ha, hb, dist_self] using (dist_nonneg : 0 ≤ dist (q i) (q j))
  · exact ⟨i, by simp, j, by simp, rfl⟩

theorem four_label_card : (Finset.univ : Finset Label).card = 4 := by
  simp [Label]

theorem proper_of_card_lt_four (J : Finset Label) (hcard : J.card < 4) :
    J ≠ Finset.univ := by
  intro hfull
  rw [hfull, four_label_card] at hcard
  exact (lt_irrefl 4) hcard

theorem full_of_card_four (J : Finset Label) (hcard : J.card = 4) :
    J = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ J)
  simpa only [four_label_card, hcard] using (le_refl 4)

/-- This is the original nearest-crosspair chain, not a postprocessed
diameter of a larger envelope. The isolation branch states the actual δ.
The minimum and maximum witnesses, positivity, and initial labeled pair
are all retained in the complete result type. -/
theorem nearest_chain_selected_cluster (q : Configuration) (hq : CollisionFree q)
    (T : ℝ) (hT : 2 < T) (i j : Label) (hij : i ≠ j) :
    ∃ J : Finset Label, ∃ hJ : J.Nonempty,
      i ∈ J ∧ j ∈ J ∧ 2 ≤ J.card ∧
      0 < diameter q J hJ ∧
      dist (q i) (q j) ≤ diameter q J hJ ∧
      diameter q J hJ ≤ (1 + T) ^ 2 * dist (q i) (q j) ∧
      (∀ a ∈ J, ∀ b ∈ J, dist (q a) (q b) ≤ diameter q J hJ) ∧
      (∃ a ∈ J, ∃ b ∈ J, dist (q a) (q b) = diameter q J hJ) ∧
      (J = Finset.univ ∨ ∃ hproper : J ≠ Finset.univ,
        T * diameter q J hJ ≤ separation q J hJ hproper) := by
  classical
  let d := dist (q i) (q j)
  let A := 1 + T
  have hd : 0 < d := collisionFree_dist_pos hq hij
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hdAd : d ≤ A * d := by nlinarith
  have hAdG : A * d ≤ A ^ 2 * d := by
    calc
      A * d ≤ A * (A * d) := mul_le_mul_of_nonneg_left hdAd (by linarith)
      _ = A ^ 2 * d := by ring
  let J₀ : Finset Label := {i, j}
  have hi₀ : i ∈ J₀ := by simp [J₀]
  have hj₀ : j ∈ J₀ := by simp [J₀]
  have hJ₀ : J₀.Nonempty := ⟨i, hi₀⟩
  have hcard₀ : J₀.card = 2 := by simpa [J₀] using Finset.card_pair hij
  have hproper₀ : J₀ ≠ Finset.univ :=
    proper_of_card_lt_four J₀ (by omega)
  have hr₀ : diameter q J₀ hJ₀ = d := pair_diameter q i j
  by_cases hstop₀ : T * diameter q J₀ hJ₀ ≤ separation q J₀ hJ₀ hproper₀
  · refine ⟨J₀, hJ₀, hi₀, hj₀, by omega, diameter_pos q hq J₀ hJ₀ (by omega),
      dist_le_diameter q J₀ hJ₀ hi₀ hj₀, ?_,
      fun _ ha _ hb => dist_le_diameter q J₀ hJ₀ ha hb,
      diameter_attained q J₀ hJ₀, Or.inr ⟨hproper₀, hstop₀⟩⟩
    simpa only [hr₀] using hdAd.trans hAdG
  · obtain ⟨_, _, b₀, _, _, hcardStep₀, _, _, hgrowth₀⟩ :=
      nearest_enlargement q J₀ hJ₀ hproper₀ T (lt_of_not_ge hstop₀)
    let J₁ := insert b₀ J₀
    have hJ₁ : J₁.Nonempty := hJ₀.mono (Finset.subset_insert b₀ J₀)
    have hi₁ : i ∈ J₁ := Finset.mem_insert_of_mem hi₀
    have hj₁ : j ∈ J₁ := Finset.mem_insert_of_mem hj₀
    have hcard₁ : J₁.card = 3 := by dsimp [J₁]; omega
    have hproper₁ : J₁ ≠ Finset.univ := proper_of_card_lt_four J₁ (by omega)
    have hr₁ : diameter q J₁ hJ₁ < A * d := by
      simpa only [J₁, A, hr₀] using hgrowth₀
    by_cases hstop₁ : T * diameter q J₁ hJ₁ ≤ separation q J₁ hJ₁ hproper₁
    · refine ⟨J₁, hJ₁, hi₁, hj₁, by omega,
        diameter_pos q hq J₁ hJ₁ (by omega),
        dist_le_diameter q J₁ hJ₁ hi₁ hj₁, hr₁.le.trans hAdG,
        fun _ ha _ hb => dist_le_diameter q J₁ hJ₁ ha hb,
        diameter_attained q J₁ hJ₁, Or.inr ⟨hproper₁, hstop₁⟩⟩
    · obtain ⟨_, _, b₁, _, _, hcardStep₁, _, _, hgrowth₁⟩ :=
        nearest_enlargement q J₁ hJ₁ hproper₁ T (lt_of_not_ge hstop₁)
      let J₂ := insert b₁ J₁
      have hJ₂ : J₂.Nonempty := hJ₁.mono (Finset.subset_insert b₁ J₁)
      have hi₂ : i ∈ J₂ := Finset.mem_insert_of_mem hi₁
      have hj₂ : j ∈ J₂ := Finset.mem_insert_of_mem hj₁
      have hcard₂ : J₂.card = 4 := by dsimp [J₂]; omega
      have hfull₂ : J₂ = Finset.univ := full_of_card_four J₂ hcard₂
      have hr₂ : diameter q J₂ hJ₂ ≤ A ^ 2 * d := by
        calc
          diameter q J₂ hJ₂ ≤ A * diameter q J₁ hJ₁ := hgrowth₁.le
          _ ≤ A * (A * d) := mul_le_mul_of_nonneg_left hr₁.le (by linarith)
          _ = A ^ 2 * d := by ring
      exact ⟨J₂, hJ₂, hi₂, hj₂, by omega,
        diameter_pos q hq J₂ hJ₂ (by omega),
        dist_le_diameter q J₂ hJ₂ hi₂ hj₂, hr₂,
        fun _ ha _ hb => dist_le_diameter q J₂ hJ₂ ha hb,
        diameter_attained q J₂ hJ₂, Or.inl hfull₂⟩

end FourBody.SourceFaithfulCluster

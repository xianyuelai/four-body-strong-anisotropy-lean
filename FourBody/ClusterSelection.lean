import FourBody.Labels
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
The finite enlargement step of v2 Proposition 2.2, lines 301--313.
There are exactly two available additions after the initial pair. We retain
an explicit radius bound; passage to the attained finite diameter is stated
separately in the obligation ledger. No separation conclusion is assumed.
-/
namespace FourBody.ClusterSelection
variable {E : Type*} [MetricSpace E]

def BoundedCluster (q : Label → E) (J : Finset Label) (r : ℝ) : Prop :=
  ∀ a ∈ J, ∀ b ∈ J, dist (q a) (q b) ≤ r

def Separated (q : Label → E) (J : Finset Label) (r T : ℝ) : Prop :=
  ∀ a ∈ J, ∀ b, b ∉ J → T * r ≤ dist (q a) (q b)

theorem insert_bound (q : Label → E) (J : Finset Label) (r T : ℝ)
    (hr : 0 ≤ r) (hT : 1 ≤ T) (hbound : BoundedCluster q J r)
    (a b : Label) (ha : a ∈ J) (hclose : dist (q a) (q b) < T * r) :
    BoundedCluster q (insert b J) ((1 + T) * r) := by
  have hlarge : r ≤ (1 + T) * r := by nlinarith
  have hnonneg : 0 ≤ (1 + T) * r := le_trans hr hlarge
  have hnew : ∀ x ∈ J, dist (q b) (q x) ≤ (1 + T) * r := by
    intro x hx
    have ht := dist_triangle (q b) (q a) (q x)
    have hd := hbound a ha x hx
    rw [dist_comm (q b) (q a)] at ht
    linarith
  intro x hx y hy
  rcases Finset.mem_insert.mp hx with hxB | hxJ
  · rcases Finset.mem_insert.mp hy with hyB | hyJ
    · subst x; subst y
      simpa using hnonneg
    · subst x
      exact hnew y hyJ
  · rcases Finset.mem_insert.mp hy with hyB | hyJ
    · subst y
      rw [dist_comm]
      exact hnew x hxJ
    · exact (hbound x hxJ y hyJ).trans hlarge

theorem exists_close_of_not_separated (q : Label → E) (J : Finset Label)
    (r T : ℝ) (h : ¬ Separated q J r T) :
    ∃ a ∈ J, ∃ b, b ∉ J ∧ dist (q a) (q b) < T * r := by
  classical
  unfold Separated at h
  push Not at h
  exact h

/-- Starting from any labeled pair, at most two additions give either all
four labels or a genuinely isolated cluster. The exact factor is (1+T)^2. -/
theorem selected_cluster (q : Label → E) (T : ℝ) (hT : 1 ≤ T)
    (i j : Label) (hij : i ≠ j) :
    ∃ J : Finset Label, ∃ r : ℝ,
      i ∈ J ∧ j ∈ J ∧ 0 ≤ r ∧
      r ≤ (1 + T) ^ 2 * dist (q i) (q j) ∧
      BoundedCluster q J r ∧ (J = Finset.univ ∨ Separated q J r T) := by
  classical
  let d := dist (q i) (q j)
  let A := 1 + T
  have hd : 0 ≤ d := dist_nonneg
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hAd : 0 ≤ A * d := mul_nonneg (le_trans (by norm_num) hA) hd
  have hdAd : d ≤ A * d := by nlinarith
  have hAdG : A * d ≤ A ^ 2 * d := by
    calc
      A * d ≤ A * (A * d) := mul_le_mul_of_nonneg_left hdAd (by linarith)
      _ = A ^ 2 * d := by ring
  let J₀ : Finset Label := {i, j}
  have hi₀ : i ∈ J₀ := by simp [J₀]
  have hj₀ : j ∈ J₀ := by simp [J₀]
  have hcard₀ : J₀.card = 2 := by simpa [J₀] using Finset.card_pair hij
  have hbound₀ : BoundedCluster q J₀ d := by
    intro x hx y hy
    simp only [J₀, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · simpa using hd
    · exact le_rfl
    · simp [d, dist_comm]
    · simpa using hd
  by_cases hsep₀ : Separated q J₀ d T
  · exact ⟨J₀, d, hi₀, hj₀, hd, hdAd.trans hAdG, hbound₀, Or.inr hsep₀⟩
  · obtain ⟨a, ha, b, hb, hclose⟩ := exists_close_of_not_separated q J₀ d T hsep₀
    let J₁ := insert b J₀
    have hi₁ : i ∈ J₁ := Finset.mem_insert_of_mem hi₀
    have hj₁ : j ∈ J₁ := Finset.mem_insert_of_mem hj₀
    have hcard₁ : J₁.card = 3 := by simp [J₁, hb, hcard₀]
    have hbound₁ : BoundedCluster q J₁ (A * d) :=
      insert_bound q J₀ d T hd hT hbound₀ a b ha hclose
    by_cases hsep₁ : Separated q J₁ (A * d) T
    · exact ⟨J₁, A * d, hi₁, hj₁, hAd, hAdG, hbound₁, Or.inr hsep₁⟩
    · obtain ⟨a', ha', b', hb', hclose'⟩ :=
        exists_close_of_not_separated q J₁ (A * d) T hsep₁
      let J₂ := insert b' J₁
      have hcard₂ : J₂.card = 4 := by simp [J₂, hb', hcard₁]
      have hfull : J₂ = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        simp [hcard₂, Label]
      have hbound₂ : BoundedCluster q J₂ (A ^ 2 * d) := by
        convert insert_bound q J₁ (A * d) T hAd hT hbound₁ a' b' ha' hclose' using 1
        dsimp [A]
        ring
      refine ⟨J₂, A ^ 2 * d, Finset.mem_insert_of_mem hi₁,
        Finset.mem_insert_of_mem hj₁, hAd.trans hAdG, le_rfl, hbound₂, Or.inl hfull⟩

theorem finite_diameter (q : Label → E) (J : Finset Label) (hJ : J.Nonempty)
    (r : ℝ) (hbound : BoundedCluster q J r) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ ≤ r ∧ BoundedCluster q J ρ ∧
      ∃ a ∈ J, ∃ b ∈ J, dist (q a) (q b) = ρ := by
  classical
  obtain ⟨a, ha⟩ := hJ
  have hprod : (J.product J).Nonempty :=
    ⟨(a, a), Finset.mem_product.mpr ⟨ha, ha⟩⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (J.product J)
    (fun p : Label × Label => dist (q p.1) (q p.2)) hprod
  rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
  refine ⟨dist (q p.1) (q p.2), dist_nonneg, hbound p.1 hp₁ p.2 hp₂,
    ?_, p.1, hp₁, p.2, hp₂, rfl⟩
  intro x hx y hy
  exact hmax (x, y) (Finset.mem_product.mpr ⟨hx, hy⟩)

/-- The bound can be chosen to be the genuine attained cluster diameter,
with the same isolation and the paper's precise growth factor. -/
theorem selected_cluster_actual_diameter (q : Label → E) (T : ℝ) (hT : 1 ≤ T)
    (i j : Label) (hij : i ≠ j) :
    ∃ J : Finset Label, ∃ r : ℝ,
      i ∈ J ∧ j ∈ J ∧ dist (q i) (q j) ≤ r ∧ 0 ≤ r ∧
      r ≤ (1 + T) ^ 2 * dist (q i) (q j) ∧ BoundedCluster q J r ∧
      (∃ a ∈ J, ∃ b ∈ J, dist (q a) (q b) = r) ∧
      (J = Finset.univ ∨ Separated q J r T) := by
  obtain ⟨J, r, hi, hj, _, hR, hbound, hsep⟩ := selected_cluster q T hT i j hij
  obtain ⟨ρ, hρ, hρr, hρbound, hatt⟩ := finite_diameter q J ⟨i, hi⟩ r hbound
  refine ⟨J, ρ, hi, hj, hρbound i hi j hj, hρ, hρr.trans hR, hρbound, hatt, ?_⟩
  rcases hsep with hfull | hsep
  · exact Or.inl hfull
  · right
    intro a ha b hb
    exact (mul_le_mul_of_nonneg_left hρr (zero_le_one.trans hT)).trans (hsep a ha b hb)

/-- In the actual collision-free setting the selected diameter is positive
and the finite cluster really contains at least two labels. -/
theorem selected_cluster_nontrivial (q : Label → E) (hq : Function.Injective q)
    (T : ℝ) (hT : 1 ≤ T) (i j : Label) (hij : i ≠ j) :
    ∃ J : Finset Label, ∃ r : ℝ,
      i ∈ J ∧ j ∈ J ∧ 2 ≤ J.card ∧ 0 < r ∧
      dist (q i) (q j) ≤ r ∧ r ≤ (1 + T) ^ 2 * dist (q i) (q j) ∧
      BoundedCluster q J r ∧
      (∃ a ∈ J, ∃ b ∈ J, dist (q a) (q b) = r) ∧
      (J = Finset.univ ∨ Separated q J r T) := by
  classical
  obtain ⟨J, r, hi, hj, hd, _, hr, hb, hatt, hsep⟩ :=
    selected_cluster_actual_diameter q T hT i j hij
  have hcard : 2 ≤ J.card := by
    have hsub : ({i,j} : Finset Label) ⊆ J := by
      intro k hk
      rcases Finset.mem_insert.mp hk with hki | hkj
      · simpa only [hki] using hi
      · simpa only [Finset.mem_singleton.mp hkj] using hj
    simpa only [Finset.card_pair hij] using Finset.card_le_card hsub
  have hdist : 0 < dist (q i) (q j) := dist_pos.mpr (fun heq => hij (hq heq))
  exact ⟨J, r, hi, hj, hcard, hdist.trans_le hd, hd, hr, hb, hatt, hsep⟩

end FourBody.ClusterSelection

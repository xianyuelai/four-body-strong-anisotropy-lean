import FourBody.InternalEquationLimits

/-!
# The actual horizontal block-center estimate H = O(ε³)

Frozen Pro v2 SHA256:
97F112DD59B8737FA12B4933067FF404335F41F5640E0FFDBBF74A5D9FDCFFBD.
The coefficient is the literal mass-dependent diameter bound and the
positive cross-gap obtained from the selected sequence. No convergence
of H is assumed: every original x coordinate is O(ε), hence the actual
external horizontal field is O(ε), and the original block mean equation
gives H = ε² Emean_x = O(ε³). All new bodies are uncompiled.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace FourBody.HorizontalCubicBound

def horizontalExteriorConstant (m : Masses) (δ : ℝ) : ℝ :=
  (totalMass m / δ ^ 3) * (2 * SequenceStart.verticalBound m)

theorem horizontalExteriorConstant_pos {m : Masses} (hm : PositiveMasses m)
    {δ : ℝ} (hδ : 0 < δ) : 0 < horizontalExteriorConstant m δ := by
  exact mul_pos (div_pos (totalMass_pos hm) (pow_pos hδ 3))
    (mul_pos (by norm_num) (SequenceStart.verticalBound_pos hm))

theorem horizontal_coordinate_bound {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : IsSolution m s q)
    (i : Label) : |q i 0| ≤ SequenceStart.verticalBound m * epsilon s := by
  simpa only [SequenceStart.horizontal_root_factor hm hs] using
    (solution_coordinate_abs_bounds hm hs hq i).1

/-- Actual physical pair estimate. Positivity and cross separation will
be discharged from the original selected sequence below. -/
theorem physical_pair_horizontal_bound {m : Masses} (hm : PositiveMasses m)
    {s : ℝ} (hs : 0 < s) {q : Configuration} (hq : IsSolution m s q)
    {δ : ℝ} (hδ : 0 < δ) (i j : Label) (hsep : δ ≤ dist (q i) (q j)) :
    |Reuse.physicalNewtonForce (m j) (q j) (q i) 0| ≤
      (m j / δ ^ 3) * (2 * SequenceStart.verticalBound m * epsilon s) := by
  have hdist : 0 < dist (q i) (q j) := hδ.trans_le hsep
  have hcoefficient : 0 ≤ m j / dist (q i) (q j) ^ 3 :=
    div_nonneg (hm j).le (pow_pos hdist 3).le
  have hcoeff_le : m j / dist (q i) (q j) ^ 3 ≤ m j / δ ^ 3 :=
    div_le_div_of_nonneg_left (hm j).le (pow_pos hδ 3)
      (pow_le_pow_left₀ hδ.le hsep 3)
  have hdiff : |q i 0 - q j 0| ≤
      2 * SequenceStart.verticalBound m * epsilon s := by
    calc
      |q i 0 - q j 0| ≤ |q i 0| + |q j 0| := abs_sub _ _
      _ ≤ SequenceStart.verticalBound m * epsilon s +
          SequenceStart.verticalBound m * epsilon s :=
        add_le_add (horizontal_coordinate_bound hm hs hq i)
          (horizontal_coordinate_bound hm hs hq j)
      _ = 2 * SequenceStart.verticalBound m * epsilon s := by ring
  rw [Reuse.physicalNewtonForce, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul, abs_mul, abs_of_nonneg hcoefficient]
  exact mul_le_mul hcoeff_le hdiff (abs_nonneg _)
    (div_nonneg (hm j).le (pow_pos hδ 3).le)

/-- A single actual common cross gap bounds the whole finite exterior
horizontal field. Internal labels contribute zero to this field. -/
theorem external_horizontal_bound {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) {s : ℝ} (hs : 0 < s)
    {q : Configuration} (hq : IsSolution m s q) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j : Label, blockOf d i ≠ blockOf d j → δ ≤ dist (q i) (q j))
    (i : Label) :
    |NewtonFieldLimits.physicalExternalField m d q i 0| ≤
      horizontalExteriorConstant m δ * epsilon s := by
  classical
  have hcoord : NewtonFieldLimits.physicalExternalField m d q i 0 =
      ∑ j : Label, if blockOf d j ≠ blockOf d i then
        Reuse.physicalNewtonForce (m j) (q j) (q i) 0 else 0 := by
    simp only [NewtonFieldLimits.physicalExternalField, WithLp.ofLp_sum,
      Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _hj
    split_ifs <;> rfl
  rw [hcoord]
  calc
    |∑ j : Label, if blockOf d j ≠ blockOf d i then
        Reuse.physicalNewtonForce (m j) (q j) (q i) 0 else 0| ≤
        ∑ j : Label, |if blockOf d j ≠ blockOf d i then
          Reuse.physicalNewtonForce (m j) (q j) (q i) 0 else 0| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le
        (Finset.univ : Finset Label)
        (fun j => if blockOf d j ≠ blockOf d i then
          Reuse.physicalNewtonForce (m j) (q j) (q i) 0 else 0)
    _ ≤ ∑ j : Label,
        (m j / δ ^ 3) * (2 * SequenceStart.verticalBound m * epsilon s) := by
      apply Finset.sum_le_sum
      intro j _hj
      by_cases hblock : blockOf d j ≠ blockOf d i
      · simp only [if_pos hblock]
        exact physical_pair_horizontal_bound hm hs hq hδ i j
            (hsep i j (Ne.symm hblock))
      · simp only [hblock, if_false, abs_zero]
        exact mul_nonneg (div_nonneg (hm j).le (pow_pos hδ 3).le)
          (mul_nonneg (mul_nonneg (by norm_num) (SequenceStart.verticalBound_pos hm).le)
            (SequenceStart.epsilon_pos hs).le)
    _ = horizontalExteriorConstant m δ * epsilon s := by
      rw [← Finset.sum_mul, ← Finset.sum_div]
      unfold horizontalExteriorConstant totalMass
      ring

/-- Literal positive mass averages preserve a coordinate absolute bound. -/
theorem block_mean_abs_bound {m : Masses} (hm : PositiveMasses m)
    (d : OrderedClusterDatum) (field : Configuration) (a : BlockIndex d)
    (k : Axis) (K : ℝ) (hfield : ∀ i : Label, |field i k| ≤ K) :
    |datumBlockMean m d field a k| ≤ K := by
  classical
  have hcoord : datumBlockMean m d field a k =
      ∑ i ∈ datumBlockLabels d a, (m i / datumBlockMass m d a) * field i k := by
    rw [InternalCoordinates.datumBlockMean_eq_weighted_sum]
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hcoord]
  calc
    |∑ i ∈ datumBlockLabels d a, (m i / datumBlockMass m d a) * field i k| ≤
        ∑ i ∈ datumBlockLabels d a, |(m i / datumBlockMass m d a) * field i k| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le (datumBlockLabels d a)
        (fun i => (m i / datumBlockMass m d a) * field i k)
    _ ≤ ∑ i ∈ datumBlockLabels d a, (m i / datumBlockMass m d a) * K := by
      apply Finset.sum_le_sum
      intro i _hi
      have hw : 0 ≤ m i / datumBlockMass m d a :=
        div_nonneg (hm i).le (datumBlockMass_pos hm d a).le
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (hfield i) hw
    _ = K := by
      rw [← Finset.sum_mul, InternalCoordinates.normalized_block_weights_sum hm,
        one_mul]

/-- One sequence-derived cross gap gives the O(ε) exterior mean estimate
on one eventual tail and simultaneously on all actual blocks. -/
theorem exists_eventual_external_horizontal_bound {m : Masses}
    (hm : PositiveMasses m) {s : ℕ → ℝ} {q : ℕ → Configuration}
    {φ : ℕ → ℕ} {y : Label → ℝ}
    (hq : ∀ ν, IsSolution m (s ν) (q ν))
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ ν in atTop,
      (∀ i : Label, |NewtonFieldLimits.physicalExternalField m
        (VerticalPartition.verticalPartitionDatum y) (q (φ ν)) i 0| ≤
          A * epsilon (s (φ ν))) ∧
      (∀ a : BlockIndex (VerticalPartition.verticalPartitionDatum y),
        |NewtonFieldLimits.physicalExternalMean m (VerticalPartition.verticalPartitionDatum y)
          (q (φ ν)) a 0| ≤ A * epsilon (s (φ ν))) := by
  obtain ⟨δ, hδ, hsep⟩ := CrossSeparation.exists_eventual_cross_separation hlim
  refine ⟨horizontalExteriorConstant m δ, horizontalExteriorConstant_pos hm hδ, ?_⟩
  filter_upwards [hsep] with ν hν
  have hs : 0 < s (φ ν) := lt_trans (by norm_num) (hlim.2.1 ν)
  have hfield := fun i => external_horizontal_bound hm
    (VerticalPartition.verticalPartitionDatum y) hs (hq (φ ν)) hδ hν i
  refine ⟨hfield, ?_⟩
  intro a
  exact block_mean_abs_bound hm _ _ a 0 _ hfield

/-- The source's precise eventual cubic estimate in the actual H=ξ/ε
coordinates. The coordinates themselves are the true mean-inverse output. -/
def HorizontalCentersCubicBound (m : Masses) (s : ℕ → ℝ)
    (φ : ℕ → ℕ) (d : OrderedClusterDatum) (h : ℕ → BlowupCoordinates m d) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ᶠ ν in atTop, ∀ a : BlockIndex d,
    |outerH (h ν) a| ≤ A * (epsilon (s (φ ν))) ^ 3

/-- Exact binding to the already frozen Proposition 3.2 specification;
the local spelling merely exposes the same s,φ parameters. -/
theorem horizontalCentersCubicBound_iff_statement (m : Masses) (s : ℕ → ℝ)
    (φ : ℕ → ℕ) (d : OrderedClusterDatum) (h : ℕ → BlowupCoordinates m d) :
    HorizontalCentersCubicBound m s φ d h ↔
      FourBody.HorizontalCentersCubicBound m d (fun ν => epsilon (s (φ ν))) h := Iff.rfl

theorem horizontal_centers_cubic_bound {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration} {φ : ℕ → ℕ} {y : Label → ℝ}
    (hq : ∀ ν, IsSolution m (s ν) (q ν))
    (hlim : SequenceStart.InitialVerticalLimit m s q φ y)
    (h : ℕ → BlowupCoordinates m (VerticalPartition.verticalPartitionDatum y))
    (hh : ∀ ν, CoordinatesOfConfiguration m (VerticalPartition.verticalPartitionDatum y)
      (epsilon (s (φ ν))) (q (φ ν)) (h ν)) :
    HorizontalCentersCubicBound m s φ (VerticalPartition.verticalPartitionDatum y) h := by
  obtain ⟨A, hA, hmean⟩ := exists_eventual_external_horizontal_bound hm hq hlim
  refine ⟨A, hA, ?_⟩
  filter_upwards [hmean] with ν hν
  intro a
  have hs : 0 < s (φ ν) := lt_trans (by norm_num) (hlim.2.1 ν)
  rw [PhysicalSequenceRows.horizontal_mean_row hm hs (hq (φ ν)) (hh ν) a,
    abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc
    (epsilon (s (φ ν))) ^ 2 *
        |NewtonFieldLimits.physicalExternalMean m (VerticalPartition.verticalPartitionDatum y)
          (q (φ ν)) a 0| ≤
        (epsilon (s (φ ν))) ^ 2 * (A * epsilon (s (φ ν))) :=
      mul_le_mul_of_nonneg_left (hν.2 a) (sq_nonneg _)
    _ = A * (epsilon (s (φ ν))) ^ 3 := by ring

theorem horizontal_centers_tendsto_zero {m : Masses} {s : ℕ → ℝ}
    {φ : ℕ → ℕ} {d : OrderedClusterDatum} {h : ℕ → BlowupCoordinates m d}
    (he : Tendsto (fun ν => epsilon (s (φ ν))) atTop (nhds 0))
    (hcubic : HorizontalCentersCubicBound m s φ d h) (a : BlockIndex d) :
    Tendsto (fun ν => outerH (h ν) a) atTop (nhds 0) := by
  obtain ⟨A, _hA, hA⟩ := hcubic
  apply squeeze_zero_norm' (hA.mono (fun ν hν => by
    simpa only [Real.norm_eq_abs] using hν a))
  simpa only [zero_pow (by norm_num : 3 ≠ 0), mul_zero] using
    (tendsto_const_nhds (x := A)).mul (he.pow 3)

/-- Existence uses ONLY the arbitrary original solution sequence inputs.
Every actual hν, gap, field estimate and H bound is constructed internally. -/
theorem exists_actual_cubic_mean_coordinates {m : Masses} (hm : PositiveMasses m)
    {s : ℕ → ℝ} {q : ℕ → Configuration}
    (hs : Tendsto s atTop atTop) (hq : ∀ ν, IsSolution m (s ν) (q ν)) :
    ∃ φ : ℕ → ℕ, ∃ y : Label → ℝ, ∃ P₀ : Label → Point,
      ∃ h : ℕ → BlowupCoordinates m (VerticalPartition.verticalPartitionDatum y),
        SequenceStart.InitialVerticalLimit m s q φ y ∧
        InternalSubsequence.InternalLimitData m s q φ y P₀ ∧
        InternalEquationLimits.InternalEquationAtLimit m y P₀ ∧
        (∀ ν, CoordinatesOfConfiguration m (VerticalPartition.verticalPartitionDatum y)
          (epsilon (s (φ ν))) (q (φ ν)) (h ν)) ∧
        HorizontalCentersCubicBound m s φ (VerticalPartition.verticalPartitionDatum y) h ∧
        (∀ a : BlockIndex (VerticalPartition.verticalPartitionDatum y),
          Tendsto (fun ν => outerH (h ν) a) atTop (nhds 0)) := by
  obtain ⟨φ, y, P₀, hlim, hdata, heq, _houter⟩ :=
    InternalEquationLimits.exists_internal_equation_limit hm hs hq
  obtain ⟨h, hh⟩ := VerticalPartition.exists_selected_mean_coordinates hm hq hlim.2.1
    (VerticalPartition.verticalPartitionDatum y)
  have hcubic := horizontal_centers_cubic_bound hm hq hlim h hh
  exact ⟨φ, y, P₀, h, hlim, hdata, heq, hh, hcubic,
    horizontal_centers_tendsto_zero hlim.2.2.2.2.1 hcubic⟩

end FourBody.HorizontalCubicBound

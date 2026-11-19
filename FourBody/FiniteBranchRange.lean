import FourBody.CommonSeedGaps

/-!
Concrete finite intersection of positive ranges on all 192 actual ordered
cluster data. This is the elementary threshold step in v2 Section 5;
analytic branches themselves are not assumed or created by this lemma.

Initially prepared as a proof candidate. Actual build/audit status is
recorded in strict receipts; this module alone does not attest
whole-paper acceptance.
-/

noncomputable section
namespace FourBody

theorem finitePositiveCommonRange (r : OrderedClusterDatum → ℝ)
    (hr : ∀ d, 0 < r d) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧ ∀ d, eta < r d := by
  classical
  have hcard : 0 < Fintype.card OrderedClusterDatum := by
    rw [card_orderedClusterDatum]
    norm_num
  have hdata : Nonempty OrderedClusterDatum := Fintype.card_pos_iff.mp hcard
  have := hdata
  let values : Finset ℝ := Finset.univ.image r
  have hvalues : values.Nonempty := Finset.univ_nonempty.image r
  let rho : ℝ := values.min' hvalues
  have hpos : 0 < rho := by
    obtain ⟨d, _, heq⟩ := Finset.mem_image.mp (Finset.min'_mem values hvalues)
    change 0 < values.min' hvalues
    rw [← heq]
    exact hr d
  let eta : ℝ := min (1 / 2) (rho / 2)
  have heta : 0 < eta := lt_min (by norm_num) (half_pos hpos)
  refine ⟨eta, heta, ?_, ?_⟩
  · exact (min_le_left _ _).trans_lt (by norm_num : (1 / (2 : ℝ)) < 1)
  · intro d
    have hle : rho ≤ r d := Finset.min'_le values _
      (Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩)
    have hhalf : rho / 2 < r d := by linarith
    exact (min_le_right _ _).trans_lt hhalf

end FourBody

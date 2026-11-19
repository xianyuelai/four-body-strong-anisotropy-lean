import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Minimal extraction of the genuine Newton target field, signed divided
differences, joint smoothness/analyticity at positive distances, and actual
Frechet derivative. Source proof bodies are unchanged. Plane is the same
EuclideanSpace Real (Fin 2) as the four-body Point. The old five-body
configuration, polar coordinates, charts, and main theorem are not imported.
newtonTargetField points from target toward source; FourBody.force uses
the opposite displacement, so its derivative requires a minus sign.
-/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace FourBody.Reuse
abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem norm_hasFDerivAt (q : Plane) (hq : q ≠ 0) :
    HasFDerivAt (fun z : Plane => ‖z‖) (‖q‖⁻¹ • innerSL ℝ q) q := by
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have h := (hasStrictFDerivAt_norm_sq q).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  have hnorm := h.congr_of_eventuallyEq
    (Eventually.of_forall fun z => (Real.sqrt_sq (norm_nonneg z)).symm)
  apply hnorm.congr_fderiv
  ext v
  simp only [smul_apply, smul_eq_mul, Real.sqrt_sq (norm_nonneg q)]
  field_simp
  ring

def newtonTargetField (source target : Plane) : Plane :=
  (‖source-target‖^3)⁻¹ • (source-target)

def dividedInverseCube (source qa qb direction : Plane) : ℝ :=
  -(inner ℝ direction (qa+qb-(2 : ℝ) • source))*(‖source-qa‖^2+‖source-qa‖*‖source-qb‖+‖source-qb‖^2)/
    ((‖source-qa‖+‖source-qb‖)*‖source-qa‖^3*‖source-qb‖^3)

def dividedNewtonTargetField (source qa qb direction : Plane) : Plane :=
  dividedInverseCube source qa qb direction • (source-qb)-
    (‖source-qa‖^3)⁻¹ • direction

theorem newtonSquaredDistance_difference (source qa qb : Plane) :
    ‖source-qb‖^2-‖source-qa‖^2=inner ℝ (qb-qa) (qa+qb-(2 : ℝ) • source) := by
  rw [norm_sub_sq_real, norm_sub_sq_real]
  simp only [inner_sub_left, inner_sub_right, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  rw [real_inner_comm qa qb, real_inner_comm source qa, real_inner_comm source qb]
  ring

/-- The difference quotient is rationalized before any t is set to zero. -/
theorem dividedInverseCube_eq (source qa qb direction : Plane) (t : ℝ) (ht : t≠0)
    (ha : source≠qa) (hb : source≠qb) (hgap : qb-qa=t • direction) :
    dividedInverseCube source qa qb direction =
      ((‖source-qb‖^3)⁻¹-(‖source-qa‖^3)⁻¹)/t := by
  have hda : 0<‖source-qa‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ha)
  have hdb : 0<‖source-qb‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hb)
  have hsum : ‖source-qa‖+‖source-qb‖≠0 := ne_of_gt (add_pos hda hdb)
  have hsq := newtonSquaredDistance_difference source qa qb
  rw [hgap, real_inner_smul_left] at hsq
  have hfactor : (‖source-qb‖-‖source-qa‖)*(‖source-qa‖+‖source-qb‖)=
      t*inner ℝ direction (qa+qb-(2 : ℝ) • source) := by nlinarith [hsq]
  unfold dividedInverseCube
  field_simp [ht, ne_of_gt hda, ne_of_gt hdb, hsum]
  nlinarith [congrArg (fun a : ℝ => a*(‖source-qa‖^2+‖source-qa‖*‖source-qb‖+‖source-qb‖^2)) hfactor]

theorem dividedNewtonTargetField_eq (source qa qb direction : Plane) (t : ℝ)
    (ht : t≠0) (ha : source≠qa) (hb : source≠qb) (hgap : qb-qa=t • direction) :
    dividedNewtonTargetField source qa qb direction =
      t⁻¹ • (newtonTargetField source qb-newtonTargetField source qa) := by
  rw [dividedNewtonTargetField, dividedInverseCube_eq source qa qb direction t ht ha hb hgap]
  have hdir : direction=t⁻¹ • (qb-qa) := by
    rw [hgap, smul_smul, inv_mul_cancel₀ ht, one_smul]
  rw [hdir]
  unfold newtonTargetField
  simp only [div_eq_mul_inv, smul_smul, smul_sub]
  module

abbrev DividedFieldVariables := (Plane×Plane)×(Plane×Plane)

theorem dividedInverseCube_joint_contDiffAt (n : ℕ∞ω) (v : DividedFieldVariables)
    (ha : v.1.1≠v.1.2) (hb : v.1.1≠v.2.1) :
    ContDiffAt ℝ n (fun w : DividedFieldVariables =>
      dividedInverseCube w.1.1 w.1.2 w.2.1 w.2.2) v := by
  have hda : 0<‖v.1.1-v.1.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ha)
  have hdb : 0<‖v.1.1-v.2.1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hb)
  have hs : ‖v.1.1-v.1.2‖+‖v.1.1-v.2.1‖≠0 := ne_of_gt (add_pos hda hdb)
  have hna : ContDiffAt ℝ n (fun w : DividedFieldVariables => ‖w.1.1-w.1.2‖) v := by
    exact (contDiffAt_fst.fst.sub contDiffAt_fst.snd).norm ℝ (sub_ne_zero.mpr ha)
  have hnb : ContDiffAt ℝ n (fun w : DividedFieldVariables => ‖w.1.1-w.2.1‖) v := by
    exact (contDiffAt_fst.fst.sub contDiffAt_snd.fst).norm ℝ (sub_ne_zero.mpr hb)
  have hd : (‖v.1.1-v.1.2‖+‖v.1.1-v.2.1‖)*‖v.1.1-v.1.2‖^3*‖v.1.1-v.2.1‖^3≠0 :=
    mul_ne_zero (mul_ne_zero hs (pow_ne_zero 3 (ne_of_gt hda))) (pow_ne_zero 3 (ne_of_gt hdb))
  have hvec : ContDiff ℝ n (fun w : DividedFieldVariables => w.1.2+w.2.1-(2 : ℝ) • w.1.1) := by
    fun_prop
  have hinner : ContDiffAt ℝ n (fun w : DividedFieldVariables =>
      inner ℝ w.2.2 (w.1.2+w.2.1-(2 : ℝ) • w.1.1)) v :=
    contDiffAt_snd.snd.inner ℝ hvec.contDiffAt
  unfold dividedInverseCube
  exact (hinner.neg.mul (((hna.pow 2).add (hna.mul hnb)).add (hnb.pow 2))).div
    (((hna.add hnb).mul (hna.pow 3)).mul (hnb.pow 3)) hd

theorem dividedNewtonTargetField_joint_contDiffAt (n : ℕ∞ω) (v : DividedFieldVariables)
    (ha : v.1.1≠v.1.2) (hb : v.1.1≠v.2.1) :
    ContDiffAt ℝ n (fun w : DividedFieldVariables =>
      dividedNewtonTargetField w.1.1 w.1.2 w.2.1 w.2.2) v := by
  have hcoef := dividedInverseCube_joint_contDiffAt n v ha hb
  have hna : ContDiffAt ℝ n (fun w : DividedFieldVariables => ‖w.1.1-w.1.2‖) v :=
    (contDiffAt_fst.fst.sub contDiffAt_fst.snd).norm ℝ (sub_ne_zero.mpr ha)
  have hn : ‖v.1.1-v.1.2‖^3≠0 := pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr ha))
  unfold dividedNewtonTargetField
  exact (hcoef.smul (contDiffAt_fst.fst.sub contDiffAt_snd.fst)).sub
    (((hna.pow 3).inv hn).smul contDiffAt_snd.snd)

-- Use the normed-space instances also in derivative statements whose
-- displayed formula does not itself mention a norm.
local instance newtonPlaneAddCommGroup : AddCommGroup Plane := (inferInstance : NormedAddCommGroup Plane).toAddCommGroup
local instance newtonPlaneModule : Module ℝ Plane := (inferInstance : NormedSpace ℝ Plane).toModule
local instance newtonPlaneTopology : TopologicalSpace Plane :=
  (inferInstance : PseudoMetricSpace Plane).toUniformSpace.toTopologicalSpace

def newtonTargetDerivative (source target : Plane) : Plane →L[ℝ] Plane :=
  (3/‖source-target‖^5) • ((innerSL ℝ (source-target)).smulRight (source-target))-
    (‖source-target‖^3)⁻¹ • ContinuousLinearMap.id ℝ Plane

theorem newtonTargetDerivative_apply (source target direction : Plane) :
    newtonTargetDerivative source target direction=
      (3/‖source-target‖^5*inner ℝ (source-target) direction) • (source-target)-
        (‖source-target‖^3)⁻¹ • direction := by
  change (3/‖source-target‖^5) • (inner ℝ (source-target) direction • (source-target))-
    (‖source-target‖^3)⁻¹ • direction = _
  rw [smul_smul]

theorem newtonTargetField_hasFDerivAt (source target : Plane) (hsep : source≠target) :
    HasFDerivAt (newtonTargetField source) (newtonTargetDerivative source target) target := by
  have hdiff : HasFDerivAt (fun q : Plane => source-q) (-(ContinuousLinearMap.id ℝ Plane)) target := by
    convert! (-(ContinuousLinearMap.id ℝ Plane)).hasFDerivAt.const_add source using 1
  have hnorm := (norm_hasFDerivAt (source-target) (sub_ne_zero.mpr hsep)).comp target hdiff
  have hn : ‖source-target‖≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hsep)
  have hinv := (hasDerivAt_inv (pow_ne_zero 3 hn)).comp_hasFDerivAt target (hnorm.pow 3)
  have hd := hinv.smul hdiff
  apply hd.congr_fderiv
  ext v k
  simp only [newtonTargetDerivative,add_apply,sub_apply,
    smul_apply,neg_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply,
    PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,PiLp.neg_apply,
    inner_neg_right,smul_eq_mul]
  norm_num
  field_simp
  ring

theorem dividedInverseCube_diagonal (source target direction : Plane) (hsep : source≠target) :
    dividedInverseCube source target target direction=
      3/‖source-target‖^5*inner ℝ (source-target) direction := by
  have hn : ‖source-target‖≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hsep)
  unfold dividedInverseCube
  simp only [inner_add_right,inner_sub_right,real_inner_smul_right,inner_sub_left]
  rw [real_inner_comm source direction,real_inner_comm target direction]
  field_simp
  ring

/-- The extension's diagonal value is the derivative of the actual
Newton field. This identifies the zero-scale row with a genuine derivative. -/
theorem dividedNewtonTargetField_diagonal (source target direction : Plane) (hsep : source≠target) :
    dividedNewtonTargetField source target target direction=
      (fderiv ℝ (newtonTargetField source) target) direction := by
  rw [(newtonTargetField_hasFDerivAt source target hsep).fderiv,
    newtonTargetDerivative_apply,dividedNewtonTargetField,dividedInverseCube_diagonal source target direction hsep]


/-! This joint-field bridge uses the same norm/noncollision argument as
the extracted joint divided-field proof. It is additional migration code,
so it must be checked in the current project as well. -/
theorem newtonTargetField_joint_contDiffAt (n : ℕ∞ω) (v : Plane × Plane)
    (hsep : v.1 ≠ v.2) :
    ContDiffAt ℝ n (fun w : Plane × Plane => newtonTargetField w.1 w.2) v := by
  have hn : ContDiffAt ℝ n (fun w : Plane × Plane => ‖w.1-w.2‖) v :=
    (contDiffAt_fst.sub contDiffAt_snd).norm ℝ (sub_ne_zero.mpr hsep)
  unfold newtonTargetField
  exact ((hn.pow 3).inv (pow_ne_zero 3
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hsep)))).smul
      (contDiffAt_fst.sub contDiffAt_snd)

theorem newtonTargetField_joint_analyticAt (v : Plane × Plane)
    (hsep : v.1 ≠ v.2) :
    AnalyticAt ℝ (fun w : Plane × Plane => newtonTargetField w.1 w.2) v :=
  (newtonTargetField_joint_contDiffAt ω v hsep).analyticAt

end FourBody.Reuse

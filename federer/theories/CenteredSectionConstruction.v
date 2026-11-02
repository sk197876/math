(** Private existence proof for the centred scalar sections in Federer
    (1969), 2.10.30, p. 195. Choose half the finite scalar outer length as
    radius when the original section is nonempty. Empty sections remain
    empty, so null nonempty sections are not lost. The witness is hidden by
    CenteredSectionSealed.v. Source context: CenteredSectionUP.v *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CenteredSectionUP ScalarBoundedLength
  LebesgueScalarMeasure MeasureUP MeasureBasic MetricDiameter CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [centered_section_exists]: supporting existence of the unique
    centred segment prescribed on each line by 2.10.30, p. 195 This
    construction proves the specification; it introduces no unproved choice
    or measure axiom. *)
Theorem centered_section_exists (R : realType) (A : set (real_line_metric R)) :
  metric_set_bounded A -> exists B, is_centered_section A B.
Proof.
move=> hb; case: (pselect (A !=set0))=> [hA|hA].
- pose v := lebesgue_scalar_measure A.
  have hv0 : (0<=v)%E := measure_nonnegative (lebesgue_scalar_is_measure R) A.
  have hvfin : v \is a fin_num.
    by rewrite (ge0_fin_numE hv0); exact: scalar_bounded_length_finite hb.
  have hv : v=(fine v)%:E by rewrite fineK.
  have hf : 0<=fine v by move: hv0; rewrite hv lee_fin.
  pose r := fine v/2.
  have hr : 0<=r by rewrite /r divr_ge0 // ler0n.
  have hrr : -r<=r by lra.
  have hB : `[-r,r] !=set0.
    exists 0; rewrite /= in_itv /=; apply/andP; split; lra.
  exists `[-r,r]; constructor.
  + by split=> _.
  + by move=> _; exists r.
  + rewrite lebesgue_scalar_segment // opprK.
    have he : r+r=fine v.
      have h2 : (2 : R)!=0 by rewrite pnatr_eq0.
      have hk : (fine v/2)*2=fine v by rewrite divfK.
      rewrite /r; lra.
    by rewrite he -hv.
- have hz : A=set0.
    apply/seteqP; split=> x; last by case.
    by move=> hx; exfalso; apply: hA; exists x.
  exists set0; rewrite hz; constructor.
  + by split=> [[x []]|[x []]].
  + by move=> [x []].
  + by [].
Qed.

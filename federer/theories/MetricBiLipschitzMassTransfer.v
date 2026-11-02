(** Federer (1969), 3.2.18, p. 255:
    transfer positive finite mass from a
    selected image piece to its source.
    The two Lipschitz comparisons from 2.10.11
    apply before any measurability assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP HausdorffMeasure MetricBiLipschitzUP MetricBiLipschitzHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_bilipschitz_finite_positive_transfer]:
    the finite positive source-mass reduction
    when combining 3.2.2 and 2.2.3
    in Federer 3.2.18, p. 255.
    Neither the source subset nor its image
    is required measurable for these inequalities. *)
Theorem metric_bilipschitz_finite_positive_transfer (R : realType)
    (X Y : metricType R) (S A : set X) (f : X -> Y) (lambda : R) m (x0 : X) :
  is_metric_bilipschitz_bound S f lambda -> A `<=` S -> (0<lambda)%R ->
  0<@hausdorff_measure R Y m (f @` A) ->
  @hausdorff_measure R Y m (f @` A)< +oo ->
  0<@hausdorff_measure R X m A /\ @hausdorff_measure R X m A< +oo.
Proof.
move=> hB hAS hLam hPos hFin.
have [hForward hInverse] := @metric_bilipschitz_hausdorff_bounds R X Y S f lambda x0 m A hB hAS.
have hmX := @hausdorff_measure_is_measure R X m.
have hmY := @hausdorff_measure_is_measure R Y m.
have hImageFin : @hausdorff_measure R Y m (f @` A) \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative hmY _)).
have hProductFin : (lambda^+m)%R%:E* @hausdorff_measure R Y m (f @` A)< +oo.
  rewrite -(fineK hImageFin) -EFinM; exact: ltry.
split; last exact: le_lt_trans hInverse hProductFin.
rewrite ltNge; apply/negP=> hZeroLe.
have hZero : @hausdorff_measure R X m A=0.
  apply/eqP; rewrite eq_le hZeroLe (measure_nonnegative hmX); reflexivity.
rewrite hZero mule0 in hForward.
by have := lt_le_trans hPos hForward; rewrite ltxx.
Qed.

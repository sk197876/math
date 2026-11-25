(** Federer (1969), 2.10.24, p. 188: supporting compact-generator reduction
    for Hausdorff approximating measures in a boundedly compact space. At a
    finite cutoff every cover member has compact closure, with unchanged
    diameter and Hausdorff gauge, as in 2.10.2(1), p. 171. This permits
    applying the actual continuity-below theorem 2.10.22, pp. 184–186. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MetricDiameterUP MetricDiameter MetricDiameterClosure MetricClosedBalls LipschitzFunctionCompact
  CompactSetDistanceProfile HausdorffLengthUP HausdorffDiameterCost MetricScaleEnvelopeUP MetricScaleCutoffCost MetricScaleWeightedBound MetricScaleMeasureBound
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_diameter_closure_compact]: supporting
    bounded compactness step for the Hausdorff application
    in 2.10.24, p. 188. The source set need
    not be closed or measurable. Its nonempty closure
    lies in a compact finite-radius closed ball. *)
Lemma finite_diameter_closure_compact (R : realType) (X : metricType R) (S : set X) (d : R) :
  metric_boundedly_compact X -> S!=set0 -> (0<=d)%R -> extended_metric_diameter S<=d%:E -> compact (closure S).
Proof.
move=> hX [a ha] hd hdiam.
have hsub : closure S `<=` metric_closed_ball a d.
  move=> x hx; have hh := @metric_diameter_upper R X (closure S) _ (extended_metric_diameter_specification _) a x
    (subset_closure ha) hx.
  rewrite extended_metric_diameter_closure in hh.
  have hb := le_trans hh hdiam; by move: hb; rewrite lee_fin.
have he : metric_closed_ball a d `&` closure S=closure S.
  apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hsub x hx.
have hh := compact_closedI (hX a d hd) (@closed_closure X S).
by rewrite he in hh.
Qed.

(** Source for [hausdorff_compact_scale_agreement]: supporting
    fixed finite-cutoff compact-cover equality used for
    2.10.24, p. 188. Both approximations are given
    by their abstract infimum laws. The proof compares
    their measures on generators; closures preserve exact
    cutoffs and costs, so no regularity or extra error
    assumption is imposed on either approximation. *)
Theorem hausdorff_compact_scale_agreement (R : realType) (X : metricType R) (m : nat) (d : R)
    (nu xi : set X -> \bar R) :
  metric_boundedly_compact X -> (0<=d)%R ->
  is_metric_scale_envelope (fun j : @nonempty_metric_sets R X=>val j)
    (fun j=>hausdorff_diameter_cost m (val j)) d%:E nu ->
  is_metric_scale_envelope (fun C : compact_metric_set X=>val C)
    (fun C=>hausdorff_diameter_cost m (val C)) d%:E xi ->
  forall A, nu A=xi A.
Proof.
move=> hX hd hn hxi A.
have hnm := metric_scale_envelope_is_measure hn (fun j=>hausdorff_diameter_cost_nonnegative m (val j)).
have hxm := metric_scale_envelope_is_measure hxi (fun C=>hausdorff_diameter_cost_nonnegative m (val C)).
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@measure_bounded_by_metric_scale_envelope R X (compact_metric_set X) (fun C=>val C)
    (fun C=>hausdorff_diameter_cost m (val C)) d%:E xi nu hxi hnm)=> C hCd.
  pose j : @nonempty_metric_sets R X := exist _ (val C) (mem_set (set_valP C).2).
  exact: (@metric_scale_generator_bound R X (@nonempty_metric_sets R X) (fun j=>val j)
    (fun j=>hausdorff_diameter_cost m (val j)) d%:E nu j hn (hausdorff_diameter_cost_nonnegative m (val j)) hCd).
- apply: (@measure_bounded_by_metric_scale_envelope R X (@nonempty_metric_sets R X) (fun j=>val j)
    (fun j=>hausdorff_diameter_cost m (val j)) d%:E nu xi hn hxm)=> j hjd.
  have hcomp := @finite_diameter_closure_compact R X (val j) d hX (set_valP j) hd hjd.
  have hne : closure (val j)!=set0 by have [x hx] := set_valP j; exists x; exact: subset_closure hx.
  pose C : compact_metric_set X := exist _ (closure (val j)) (mem_set (conj hcomp hne)).
  have hCd : extended_metric_diameter (val C)<=d%:E by rewrite /= extended_metric_diameter_closure.
  have hh := @metric_scale_generator_bound R X (compact_metric_set X) (fun C=>val C)
    (fun C=>hausdorff_diameter_cost m (val C)) d%:E xi C hxi (hausdorff_diameter_cost_nonnegative m (val C)) hCd.
  change (is_true (xi (closure (val j))<=hausdorff_diameter_cost m (closure (val j)))) in hh.
  rewrite hausdorff_diameter_cost_closure in hh; apply: le_trans _ hh.
  apply: (@measure_mono R X xi hxm)=> x hx; exact: subset_closure hx.
Qed.

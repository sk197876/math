(** Federer 2.10.19(2), p. 181: adjoining the empty Hausdorff generator
    preserves every scale and the final measure. Generalize the existing
    empty-completion connection to any nonnegative set cost. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import HausdorffLengthUP HausdorffAllSets MetricScaleEnvelopeUP
  MetricScaleEnvelope MetricScaleMeasureBound MetricScaleWeightedBound
  MetricScaleCutoffCost CaratheodoryLimitUP MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_scale_adjoin_empty_values]: supporting
    generator-family connection for Federer 2.10.19(2), p. 181. A
    nonnegative empty-generator cost changes neither the infimum nor
    the empty target value. The cost may be one in degree zero. All
    cutoffs, including zero and infinity, are retained. *)
Theorem metric_scale_adjoin_empty_values (R : realType) (X : metricType R)
    (c : set X -> \bar R) (delta : \bar R) (nu xi : set X -> \bar R) :
    (forall S, 0<=c S) ->
    is_metric_scale_envelope (fun j : nonempty_metric_sets X => val j)
      (fun j => c (val j)) delta nu ->
    is_metric_scale_envelope (fun j : all_sets_hausdorff_generators X => val j)
      (fun j => c (val j)) delta xi -> forall A, nu A=xi A.
Proof.
move=> hc hnu hxi A.
have hcn (j : nonempty_metric_sets X) : 0<=c (val j) := hc _.
have hca (j : all_sets_hausdorff_generators X) : 0<=c (val j) := hc _.
have hmnu := metric_scale_envelope_is_measure hnu hcn.
have hmxi := metric_scale_envelope_is_measure hxi hca.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (measure_bounded_by_metric_scale_envelope hxi hmnu) => j hd.
  case: (eqVneq (val j : set X) set0) => [he|hne].
  + rewrite he (measure_empty hmnu); exact: hc.
  + have hneP : (val j : set X) !=set0 := (set0P _).1 hne.
    pose k : nonempty_metric_sets X := @exist _ (fun S : set X => S \in [set S | S!=set0])
      (val j) (mem_set hneP).
    exact: (@metric_scale_generator_bound R X (@nonempty_metric_sets R X)
      (fun k => val k) (fun k => c (val k)) delta nu k hnu (hcn k) hd).
- apply: (measure_bounded_by_metric_scale_envelope hnu hmxi) => j hd.
  pose k : all_sets_hausdorff_generators X := @exist _
    (fun S : set X => S \in [set: set X]) (val j) (mem_set I).
  exact: (@metric_scale_generator_bound R X (@all_sets_hausdorff_generators R X)
    (fun k => val k) (fun k => c (val k)) delta xi k hxi (hca k) hd).
Qed.

(** Source for [metric_scale_adjoin_empty_specification]: supporting
    specification transfer for Federer 2.10.19(2), p. 181. The actual
    original scale measure satisfies the all-set laws because the two
    independently specified covering infima agree. *)
Theorem metric_scale_adjoin_empty_specification (R : realType) (X : metricType R)
    (c : set X -> \bar R) (delta : \bar R) (nu : set X -> \bar R) :
    (forall S, 0<=c S) ->
    is_metric_scale_envelope (fun j : nonempty_metric_sets X => val j)
      (fun j => c (val j)) delta nu ->
    is_metric_scale_envelope (fun j : all_sets_hausdorff_generators X => val j)
      (fun j => c (val j)) delta nu.
Proof.
move=> hc hn.
pose xi := metric_scale_envelope (fun j : all_sets_hausdorff_generators X => val j)
  (fun j => c (val j)) delta.
have hx := @metric_scale_envelope_specification R X (@all_sets_hausdorff_generators R X)
  (fun j => val j) (fun j => c (val j)) delta.
have he : nu=xi.
  apply: funext => A; exact: (@metric_scale_adjoin_empty_values R X c delta nu xi hc hn hx A).
by rewrite he.
Qed.

(** Source for [caratheodory_adjoin_empty_specification]: supporting
    final measure identification in Federer 2.10.19(2), p. 181. Equality
    at every scale preserves the independent covering-supremum laws. *)
Theorem caratheodory_adjoin_empty_specification (R : realType) (X : metricType R)
    (c : set X -> \bar R) (psi : set X -> \bar R) :
    (forall S, 0<=c S) ->
    is_caratheodory_limit (fun j : nonempty_metric_sets X => val j)
      (fun j => c (val j)) psi ->
    is_caratheodory_limit (fun j : all_sets_hausdorff_generators X => val j)
      (fun j => c (val j)) psi.
Proof.
move=> hc hH; constructor.
- move=> A d xi hd hxi.
  pose nu := metric_scale_envelope (fun j : nonempty_metric_sets X => val j)
    (fun j => c (val j)) d.
  have hn := @metric_scale_envelope_specification R X (@nonempty_metric_sets R X)
    (fun j => val j) (fun j => c (val j)) d.
  rewrite -(@metric_scale_adjoin_empty_values R X c d nu xi hc hn hxi A).
  exact: (@caratheodory_limit_upper R X (@nonempty_metric_sets R X)
    (fun j => val j) (fun j => c (val j)) psi hH A d nu hd hn).
- move=> A b hb; apply: (caratheodory_limit_least hH) => d nu hd hn.
  exact: hb d nu hd (@metric_scale_adjoin_empty_specification R X c d nu hc hn).
Qed.

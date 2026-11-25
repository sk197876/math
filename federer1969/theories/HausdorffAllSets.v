(** Empty-generator completion supporting Federer (1969), 2.10.19(2), p.
    181. The Hausdorff generators in 2.10.2(1), p. 171, are nonempty,
    whereas the printed 2.10.17(3), p. 179, uses intersection closure.
    Adding the empty set changes no covering infimum, even at degree zero
    where its auxiliary cost is one. This equivalent generator completion
    avoids treating an empty intersection as a nonempty generator. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MetricDiameter HausdorffLengthUP HausdorffMeasure
  HausdorffDiameterCost MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleCutoffCost
  MetricScaleWeightedBound MetricScaleMeasureBound CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [all_sets_hausdorff_generators]: supporting
    addition of the empty generator for 2.10.19(2),
    p. 181. The cost on nonempty sets is unchanged. *)
Definition all_sets_hausdorff_generators (R : realType) (X : metricType R) : choiceType :=
  [the choiceType of set_type (@setT (set X))].

(** Source for [is_all_sets_hausdorff_scale]: abstract scale
    specification supporting 2.10.19(2), p. 181,
    after adjoining the empty generator. Empty covers
    still give the empty target mass zero in degree zero. *)
Definition is_all_sets_hausdorff_scale (R : realType) (X : metricType R)
    (m : nat) (delta : \bar R) (nu : set X -> \bar R) :=
  is_metric_scale_envelope (fun j : all_sets_hausdorff_generators X => val j)
    (fun j => hausdorff_diameter_cost m (val j)) delta nu.

(** Source for [hausdorff_all_sets_scale_values]: supporting
    equality of every scale with the original nonempty
    family in 2.10.19(2), p. 181. Compare the
    abstract infima through their measure and generator
    bounds; an empty generator costs a nonnegative amount. *)
Lemma hausdorff_all_sets_scale_values (R : realType) (X : metricType R)
    (m : nat) (delta : \bar R) (nu xi : set X -> \bar R) :
  is_metric_scale_envelope (fun j : nonempty_metric_sets X => val j)
    (fun j => hausdorff_diameter_cost m (val j)) delta nu ->
  is_all_sets_hausdorff_scale m delta xi -> forall A, nu A=xi A.
Proof.
move=> hnu hxi A.
have hc (j : all_sets_hausdorff_generators X) : 0<=hausdorff_diameter_cost m (val j).
  exact: hausdorff_diameter_cost_nonnegative.
have hcn (j : nonempty_metric_sets X) : 0<=hausdorff_diameter_cost m (val j).
  exact: hausdorff_diameter_cost_nonnegative.
have hmnu := metric_scale_envelope_is_measure hnu hcn.
have hmxi := metric_scale_envelope_is_measure hxi hc.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (measure_bounded_by_metric_scale_envelope hxi hmnu)=> j hd.
  case: (eqVneq (val j : set X) set0)=> [he|hne].
  + rewrite he (measure_empty hmnu); exact: hausdorff_diameter_cost_nonnegative.
  + have hneP : (val j : set X) !=set0 := (set0P _).1 hne.
    pose k : nonempty_metric_sets X := @exist _ (fun S : set X => S \in [set S | S!=set0]) (val j) (mem_set hneP).
    exact: (@metric_scale_generator_bound R X (@nonempty_metric_sets R X)
      (fun k => val k) (fun k => hausdorff_diameter_cost m (val k)) delta nu k hnu (hcn k) hd).
- apply: (measure_bounded_by_metric_scale_envelope hnu hmxi)=> j hd.
  pose k : all_sets_hausdorff_generators X := @exist _ (fun S : set X => S \in [set: set X]) (val j) (mem_set I).
  exact: (@metric_scale_generator_bound R X (@all_sets_hausdorff_generators R X)
    (fun k => val k) (fun k => hausdorff_diameter_cost m (val k)) delta xi k hxi (hc k) hd).
Qed.

(** Source for [hausdorff_all_sets_scale_specification]: supporting
    transfer of the actual scale measure to the
    empty-completed family in 2.10.19(2), p. 181. *)
Lemma hausdorff_all_sets_scale_specification (R : realType) (X : metricType R)
    (m : nat) (delta : \bar R) (nu : set X -> \bar R) :
  is_metric_scale_envelope (fun j : nonempty_metric_sets X => val j)
    (fun j => hausdorff_diameter_cost m (val j)) delta nu -> is_all_sets_hausdorff_scale m delta nu.
Proof.
move=> hn.
pose xi := metric_scale_envelope (fun j : all_sets_hausdorff_generators X => val j)
  (fun j => hausdorff_diameter_cost m (val j)) delta.
have hx := @metric_scale_envelope_specification R X (@all_sets_hausdorff_generators R X)
  (fun j => val j) (fun j => hausdorff_diameter_cost m (val j)) delta.
have he : nu=xi by apply: funext=> A; exact: hausdorff_all_sets_scale_values hn hx A.
by rewrite he.
Qed.

(** Source for [hausdorff_all_sets_limit_specification]: supporting
    identification of the final measure with actual H^m
    in 2.10.19(2), p. 181. It follows from the
    equality at every scale and the supremum laws. *)
Lemma hausdorff_all_sets_limit_specification (R : realType) (X : metricType R) (m : nat) :
  is_caratheodory_limit (fun j : all_sets_hausdorff_generators X => val j)
    (fun j => hausdorff_diameter_cost m (val j)) (@hausdorff_measure R X m).
Proof.
have hH := @hausdorff_measure_specification R X m.
constructor.
- move=> A d xi hd hxi.
  pose nu := metric_scale_envelope (fun j : nonempty_metric_sets X => val j)
    (fun j => hausdorff_diameter_cost m (val j)) d.
  have hn := @metric_scale_envelope_specification R X (@nonempty_metric_sets R X)
    (fun j => val j) (fun j => hausdorff_diameter_cost m (val j)) d.
  rewrite -(hausdorff_all_sets_scale_values hn hxi A).
  exact: (@caratheodory_limit_upper R X (@nonempty_metric_sets R X)
    (fun j => val j) (fun j => hausdorff_diameter_cost m (val j)) (hausdorff_measure m) hH A d nu hd hn).
- move=> A b hb; apply: (caratheodory_limit_least hH)=> d nu hd hn.
  exact: hb d nu hd (hausdorff_all_sets_scale_specification hn).
Qed.

(** Federer (1969), 2.9.19, p. 164: identify induced-measure masses with
    increments at continuity endpoints, using 2.5.17, p. 111. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveArcLength StieltjesImageMeasures
  StieltjesInducedPairLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [stieltjes_induced_pair_closed_interval_increment]: direct
    use of 2.5.17, p. 111, in Federer 2.9.19, p. 164: at continuity
    endpoints, g(b)-g(a) is the positive induced closed-interval mass minus
    the negative one. *)
Lemma stieltjes_induced_pair_closed_interval_increment (R : realType)
    (g : R -> R) (psip psim : set R -> \bar R) (a b : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim -> a<b ->
  g @ a --> g a -> g @ b --> g b ->
  (g b-g a)%:E=(psip `[a,b]-psim `[a,b])%E.
Proof.
move=> hg hp hab hca hcb.
have [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [hincr _]]]]]]]]]]]] :=
  @induced_measure_pair_laws R g hg psip psim hp.
exact: (hincr a b hab hca hcb).2.
Qed.

(** Source for [stieltjes_monotone_closed_interval_increment]: the monotone
    increment/mass identity used in Federer 2.9.19, p. 164 The negative
    induced measure vanishes by 2.5.17, p. 111, so the positive mass equals
    g(b)-g(a) at continuity endpoints. *)
Lemma stieltjes_monotone_closed_interval_increment (R : realType)
    (g : R -> R) (psip psim : set R -> \bar R) (a b : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  (forall s t : R, s<=t -> g s<=g t) ->
  is_induced_measure_pair g psip psim -> a<b ->
  g @ a --> g a -> g @ b --> g b ->
  psip `[a,b]=(g b-g a)%:E.
Proof.
move=> hg hmono hp hab hca hcb.
have hzero := (@induced_measure_pair_monotone R g hg hmono psip psim hp).1.
have he := @stieltjes_induced_pair_closed_interval_increment R g psip psim a b hg hp hab hca hcb.
by rewrite hzero sube0 in he.
Qed.

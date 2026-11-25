(** Federer (1969), 2.10.22, pp. 184–185: indexed covering bounds for
    optional source rows. None is an inactive empty contribution, not an
    asserted compact generator. A supplied default is used only to make the
    index map total; it never contributes to the cover or its cost. This
    supports finite covers and their compact array extraction. Source
    context and the cost- ordering proof route: SummablePositiveMaximum.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import SummableCostEnumerationUP NonnegativeSum NonnegativeSumSupport
  MetricDiameter MetricScaleEnvelopeUP MetricScaleIndexedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [optional_generator_set]: supporting
    inactive-slot carrier in the finite/countable
    cover extraction of 2.10.22, pp. 184–185.
    Only Some carries an actual family member. *)
Definition optional_generator_set (X : choiceType) (J : Type)
    (S : J -> set X) (o : option J) : set X :=
  if o is Some j then S j else set0.

(** Source for [metric_scale_optional_cover_bound]: supporting
    covering estimate in 2.10.22, pp. 184–185,
    with explicit zero-cost inactive positions. The
    original generator family remains unchanged. *)
Lemma metric_scale_optional_cover_bound (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> R) (delta : \bar R) (nu : set X -> \bar R)
    (u : nat -> option J) (d : J) (A : set X) :
  is_metric_scale_envelope S (fun j=>(c j)%:E) delta nu ->
  (forall n j, u n=Some j -> (0<=c j)%R) ->
  (forall n j, u n=Some j -> extended_metric_diameter (S j)<=delta) ->
  A `<=` \bigcup_n optional_generator_set S (u n) ->
  nu A<=nonnegative_sum setT (fun n=>(optional_generator_cost c (u n))%:E).
Proof.
move=> hn hc hd hcover.
pose D : set nat := [set n | exists j, u n=Some j].
pose v n := if u n is Some j then j else d.
have hv n j (hj : u n=Some j) : v n=j by rewrite /v hj.
have hcost n : D n -> 0<=(c (v n))%:E.
  move=> [j hj]; rewrite (hv n j hj) lee_fin; exact: hc n j hj.
have hdiam n : D n -> extended_metric_diameter (S (v n))<=delta.
  move=> [j hj]; rewrite (hv n j hj); exact: hd n j hj.
have hcov : A `<=` \bigcup_(n in D) S (v n).
  move=> x hx; have [n hnT hnx] := hcover x hx.
  case he: (u n) hnx=> [j|] hnx; last by case: hnx.
  exists n; first by exists j.
  by rewrite (hv n j he).
have hh := @metric_scale_envelope_indexed_cover R X J [the choiceType of (nat : Type)]
  S (fun j=>(c j)%:E) delta nu hn A D v (countableP _) hcost hdiam hcov.
have heq : nonnegative_sum D (fun n=>(c (v n))%:E)=
    nonnegative_sum D (fun n=>(optional_generator_cost c (u n))%:E).
  apply: nonnegative_sum_ext=> n [j hj].
  by rewrite (hv n j hj) hj /optional_generator_cost.
rewrite heq in hh; apply: le_trans hh _; apply: nonnegative_sum_subset=> n hnD; exact: Logic.I.
Qed.

(** An indexed form of the covering bound in Federer (1969), 2.10.1, p. 170,
    permitting repeated generators. It supports the Borel partition sums in
    2.10.8, p. 175. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum NonnegativeSumImageBound
  MetricDiameter MetricScaleEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_scale_envelope_indexed_cover]:
    the covering inequality of Federer 2.10.1, p. 170,
    with repeated generator indices allowed. Passing to
    their image can only decrease the nonnegative sum. *)
Lemma metric_scale_envelope_indexed_cover (R : realType) (X : metricType R)
    (J K : choiceType) (S : J -> set X) (c : J -> \bar R)
    (delta : \bar R) (nu : set X -> \bar R) :
  is_metric_scale_envelope S c delta nu ->
  forall (A : set X) (D : set K) (u : K -> J),
  countable D -> (forall k, D k -> 0<=c (u k)) ->
  (forall k, D k -> extended_metric_diameter (S (u k))<=delta) ->
  A `<=` \bigcup_(k in D) S (u k) -> nu A<=nonnegative_sum D (fun k => c (u k)).
Proof.
move=> hn A D u hD hc hd hcov.
have hG : countable (u @` D) := sub_countable (card_image_le u D) hD.
have hdiam : forall j, (u @` D) j -> extended_metric_diameter (S j)<=delta.
  move=> j [k hk <-]; exact: hd hk.
have hcover : A `<=` \bigcup_(j in u @` D) S j.
  move=> x hx; have [k hk hxk] := hcov x hx.
  exists (u k); last exact hxk; by exists k.
apply: le_trans (@metric_scale_envelope_lower R X J S c delta nu hn A (u @` D) hG hdiam hcover) _.
exact: nonnegative_sum_image_bound hc.
Qed.

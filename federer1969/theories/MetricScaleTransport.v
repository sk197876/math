(** Federer (1969), 2.10.2(1), p. 171: passing to closed covers preserves
    the Hausdorff measure. This supporting cover-transport lemma also
    underlies the Lipschitz comparison used in 2.10.11, p. 176. The present
    statement abstracts the nonexpanding case; it does not assert the full
    multiplicity inequality. *)
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

(** Source for [metric_scale_envelope_transport]: supporting
    comparison of countable covering infima for Federer
    2.10.2(1), p. 171. Image repetitions can only
    decrease the nonnegative sum; transported generators
    contain the image, and have no larger diameter or cost. *)
Theorem metric_scale_envelope_transport (R : realType) (X Y : metricType R)
    (J K : choiceType) (S : J -> set X) (T : K -> set Y)
    (c : J -> \bar R) (d : K -> \bar R) (f : X -> Y) (u : J -> K)
    (delta : \bar R) (nu : set X -> \bar R) (xi : set Y -> \bar R) :
  is_metric_scale_envelope S c delta nu ->
  is_metric_scale_envelope T d delta xi ->
  (forall k, 0<=d k) ->
  (forall j x, S j x -> T (u j) (f x)) ->
  (forall j, extended_metric_diameter (T (u j))<=extended_metric_diameter (S j)) ->
  (forall j, d (u j)<=c j) ->
  forall A, xi (f @` A)<=nu A.
Proof.
move=> hn hx hd hmap hdiam hcost A.
apply: (metric_scale_envelope_greatest hn)=> G hG hsize hcov.
have hU : countable (u @` G) := sub_countable (card_image_le u G) hG.
have hUs k : (u @` G) k -> extended_metric_diameter (T k)<=delta.
  move=> [j hj <-]; exact: le_trans (hdiam j) (hsize j hj).
have hUc : f @` A `<=` \bigcup_(k in u @` G) T k.
  move=> y [x hxA <-]; have [j hj hSj] := hcov x hxA.
  exists (u j); first by exists j.
  exact: hmap j x hSj.
apply: le_trans (@metric_scale_envelope_lower R Y K T d delta xi hx (f @` A)
  (u @` G) hU hUs hUc) _.
apply: le_trans (@nonnegative_sum_image_bound R J K G u d (fun j _ => hd (u j))) _.
apply: nonnegative_sum_mono=> j _; exact: hcost.
Qed.

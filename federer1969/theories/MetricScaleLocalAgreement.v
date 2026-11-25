(** Federer (1969), 2.10.17(3), p. 179: when the generator family is closed
    under intersection and intersecting with S does not increase costs,
    covers of A intersect S may be intersected with S. Thus phi_delta(A
    intersect S)=phi_infinity(A intersect S) for a generator S of diameter
    at most delta. We retain the printed intersection closure, including
    empty intersections *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelopeLaws
  NonnegativeSum NonnegativeSumImageBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_intersection_cost_family]: direct indexed
    specification of the intersection and cost hypothesis
    of 2.10.17(3), p. 179. The witness records the
    actual intersection as a generator, independently
    of any chosen intersection-index construction. *)
Definition is_intersection_cost_family (R : realType) (X : Type) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) :=
  forall j k, exists l, S l=S j `&` S k /\ c l<=c k.

(** Source for [metric_scale_intersection_agreement]: supporting local scale
    equality in the proof of 2.10.17(3), p. 179 Replace an arbitrary
    countable cover by its intersections with the fixed small generator;
    repetitions only decrease the nonnegative image sum. *)
Theorem metric_scale_intersection_agreement (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c : J -> \bar R)
    (delta : \bar R) (nu omega : set X -> \bar R) :
  (forall j, 0<=c j) -> is_intersection_cost_family S c ->
  is_metric_scale_envelope S c delta nu -> is_metric_scale_envelope S c +oo omega ->
  forall j A, extended_metric_diameter (S j)<=delta -> nu (A `&` S j)=omega (A `&` S j).
Proof.
move=> hc hclosed hn ho j A hd; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (metric_scale_envelope_greatest ho)=> G hG _ hcover.
  pose l k := projT1 (cid (hclosed j k)).
  have hl k : S (l k)=S j `&` S k /\ c (l k)<=c k := projT2 (cid (hclosed j k)).
  pose H := l @` G.
  have hH : countable H := sub_countable (card_image_le l G) hG.
  have hdiam k : H k -> extended_metric_diameter (S k)<=delta.
    move=> [u hu <-]; rewrite (hl u).1.
    apply: le_trans _ hd; apply: extended_metric_diameter_mono; by move=> x [hx _].
  have hcov : A `&` S j `<=` \bigcup_(k in H) S k.
    move=> x hx; have [k hk hSk] := hcover x hx.
    exists (l k); first by exists k.
    by rewrite (hl k).1; split; first exact hx.2.
  have hh := @metric_scale_envelope_lower R X J S c delta nu hn (A `&` S j) H hH hdiam hcov.
  apply: le_trans hh _.
  apply: le_trans (@nonnegative_sum_image_bound R J J G l c (fun k hk => hc (l k))) _.
  apply: nonnegative_sum_mono=> k hk; exact (hl k).2.
- exact (@metric_scale_envelope_antitone_cutoff R X J S c delta +oo nu omega hn ho (leey delta) (A `&` S j)).
Qed.

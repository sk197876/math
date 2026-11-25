(** Federer (1969), 2.10.47, p. 205: the nested compact sets E_j preserve
    the values gamma_i(E_j) for h <= i <= j. The intersection then has a
    finite upper bound and a positive lower bound by the final assertion of
    2.10.20, p. 182. Indices below are shifted so that h is zero. This file
    specifies the pruning invariant and proves its final consequences; it
    does not assume or claim the existence of the dyadic pruning required by
    the full theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic ExtendedRealBounds ExtendedRealLimitBounds
  MetricScaleEnvelopeUP InteriorRefiningMetricCost CompactScaleContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_compact_content_pruning]: abstract invariant
    of the sequence in 2.10.47, p. 205: all earlier
    contents of a retained compact set have the same value a.
    This is a predicate to be proved by a construction. *)
Record is_compact_content_pruning (R : realType) (X : metricType R)
    (gamma : nat -> set X -> \bar R) (a : \bar R) (E : nat -> set X) : Prop := {
  (** Source for [content_pruning_compact]: compactness of every
      retained E_j, 2.10.47, p. 205. *)
  content_pruning_compact : forall j, compact (E j);
  (** Source for [content_pruning_nested]: the displayed decreasing
      sequence E_h, E_(h+1), ..., 2.10.47, p. 205. *)
  content_pruning_nested : forall i j, (i<=j)%N -> E j `<=` E i;
  (** Source for [content_pruning_mass]: the last displayed
      identity before the definition of B in 2.10.47,
      p. 205, with the initial index shifted to zero. *)
  content_pruning_mass : forall i j, (i<=j)%N -> gamma i (E j)=a
}.

(** Source for [content_pruning_intersection_compact]: supporting
    compactness and containment of B = intersection E_j in
    2.10.47, p. 205. No nonemptiness premise is needed. *)
Lemma content_pruning_intersection_compact (R : realType) (X : metricType R)
    gamma a E : @is_compact_content_pruning R X gamma a E ->
  compact (\bigcap_j E j) /\ (\bigcap_j E j) `<=` E 0%N.
Proof.
move=> hE.
have hsub : (\bigcap_j E j) `<=` E 0%N by move=> x hx; exact: hx 0%N Logic.I.
have hclosed : closed (\bigcap_j E j).
  apply: closed_bigI=> j _.
  exact (compact_closed (@metric_hausdorff R X) (@content_pruning_compact R X gamma a E hE j)).
split; last exact hsub.
exact (@subclosed_compact X (\bigcap_j E j) (E 0%N) hclosed
  (@content_pruning_compact R X gamma a E hE 0%N) hsub).
Qed.

(** Source for [content_pruning_intersection_upper]: supporting
    upper bound H^m(B) <= lim gamma_i(B) <= a in
    2.10.47, p. 205. The comparison with the contents
    is explicit; its dyadic geometric proof is separate. *)
Lemma content_pruning_intersection_upper (R : realType) (X : metricType R)
    (gamma : nat -> set X -> \bar R) a E (mu : set X -> \bar R) :
  is_compact_content_pruning gamma a E -> (forall i, is_measure (gamma i)) ->
  (forall A, A `<=` E 0%N -> mu A<=extended_real_sup [set t | exists i, t=gamma i A]) ->
  mu (\bigcap_j E j)<=a.
Proof.
move=> hE hm hcomp.
have hsub : (\bigcap_j E j) `<=` E 0%N by move=> x hx; exact: hx 0%N Logic.I.
apply: le_trans (hcomp _ hsub) _.
apply: extended_real_sup_least=> t [i ->].
rewrite -(content_pruning_mass hE (lexx i)).
apply: (@measure_mono R X (gamma i) (hm i))=> x hx; exact: hx i Logic.I.
Qed.

(** Source for [content_pruning_finite_positive_intersection]:
    final two bounds for B in 2.10.47, p. 205.
    A common positive lower bound at the larger cutoff
    survives the compact intersection at the smaller cutoff
    by the already proved 2.10.20, p. 182. The content
    construction and its geometric comparisons remain premises
    of this supporting lemma, not additional project axioms. *)
Theorem content_pruning_finite_positive_intersection (R : realType) (X : metricType R)
    (gamma : nat -> set X -> \bar R) a E (mu : set X -> \bar R)
    (J : choiceType) (S : J -> set X) (c : J -> \bar R)
    xi delta (small large : set X -> \bar R) b :
  is_compact_content_pruning gamma a E -> (forall i, is_measure (gamma i)) ->
  (forall A, A `<=` E 0%N -> mu A<=extended_real_sup [set t | exists i, t=gamma i A]) ->
  a< +oo -> 0<b ->
  is_metric_scale_envelope S c xi small -> is_metric_scale_envelope S c delta large ->
  (forall j, 0<=c j) -> is_interior_refining_metric_cost S c xi delta ->
  (forall A, small A<=mu A) -> (forall j, b<=large (E j)) ->
  exists B, [/\ compact B, B `<=` E 0%N, 0<mu B & mu B< +oo ].
Proof.
move=> hE hm hcomp ha hb hs hl hc href hsmall hlow.
pose B := \bigcap_j E j.
have [hB hsub] := content_pruning_intersection_compact hE.
have hu := content_pruning_intersection_upper hE hm hcomp.
have [l [hlim hle]] := @metric_scale_compact_interior_refinement R X J S c xi delta small large E
  hs hl hc href (content_pruning_compact hE) (content_pruning_nested hE).
have hbL := extended_order_limit_lower_bound hlim.2 hlow.
exists B; split=> //.
- exact: lt_le_trans hb (le_trans hbL (le_trans hle (hsmall B))).
- exact: le_lt_trans hu ha.
Qed.

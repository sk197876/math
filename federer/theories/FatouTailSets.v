(** Federer (1969), proof of 2.4.6, p. 84: B_i,n consists of the points of
    A_i at which every f_k, k>=n, exceeds t*y_i. These measurable sets
    increase to A_i; we retain Federer's strict inequality, which gives the
    same exhaustion because t<1 and y_i>0. The common domain is explicit for
    partial functions. Source context: ExtendedLowerLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology CountableOrderIntervals PartialFunctionUP
  PartialFunctionLimitExtremaUP PartialLowerLimitStrict MeasureUP MeasureFiniteClosure
  MeasureCountableClosure MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [fatou_tail_set]: direct set B_i,n from
    Federer 2.4.6, p. 84, for a fixed A_i and
    threshold t*y_i. *)
Definition fatou_tail_set (R : realType) (X : Type)
    (f : nat -> partial_function X (extended_real_line R)) (A : set X) (b : \bar R) n :=
  A `&` \bigcap_(k in [set k | (n <= k)%N]) partial_function_preimage (f k) [set z | b < z].

(** Source for [fatou_tail_set_increasing]: the increasing
    property of B_i,n stated in Federer 2.4.6, p. 84. *)
Lemma fatou_tail_set_increasing (R : realType) (X : Type)
    (f : nat -> partial_function X (extended_real_line R)) (A : set X) b n m :
  (n <= m)%N -> fatou_tail_set f A b n `<=` fatou_tail_set f A b m.
Proof.
move=> hnm x [hx hh]; split=> // k hmk; exact: hh k (leq_trans hnm hmk).
Qed.

(** Source for [fatou_tail_set_measurable]: measurability of
    B_i,n in Federer 2.4.6, p. 84, by countable
    intersection of measurable inverse images. *)
Lemma fatou_tail_set_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R)) (A : set X) b n :
  (forall k, is_measure_measurable_function mu (f k)) -> measure_measurable mu A ->
  measure_measurable mu (fatou_tail_set f A b n).
Proof.
move=> hf hA; apply: (@measure_measurable_intersection R X mu hm _ _ hA).
apply: (@measure_measurable_countable_intersection R X [the choiceType of (nat : Type)] mu hm
  [set k | (n <= k)%N] _ (countableP _))=> k _.
apply: (measurable_function_open_preimage (hf k)); exact: order_strict_upper_ray_open.
Qed.

(** Source for [fatou_tail_set_exhaustion]: the union assertion
    for B_i,n in Federer 2.4.6, p. 84; the strict
    threshold is below every lower-limit value on A. *)
Lemma fatou_tail_set_exhaustion (R : realType) (X : Type)
    (f : nat -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) (A : set X) b :
  is_partial_function_lower_limit f g ->
  (forall x, A x -> forall n, partial_function_domain (f n) x) ->
  (forall x, A x -> exists y, partial_function_graph g x y /\ b < y) ->
  (\bigcup_n fatou_tail_set f A b n) = A.
Proof.
move=> hg hd hA; apply/seteqP; split=> x.
- by move=> [n _ [hx _]].
- move=> hx; have [y [hy hby]] := hA x hx.
  have [N hN] := @partial_lower_limit_strict_eventual_bound R X f g x y b hg hy hby.
  exists N=> //; split=> // k hk; have [z hz] := hd x hx k.
  exists z; split=> //; exact: hN k hk z hz.
Qed.

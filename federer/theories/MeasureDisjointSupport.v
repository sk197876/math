(** Federer (1969), 2.1.6(2), p. 59: a disjoint family in a finite measure
    space has only countably many members of positive measure. The proof
    uses numerical summation 2.1.1(12), p. 53, and finite additivity
    2.1.3(3), pp. 54-55. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumCountable
  MeasureUP MeasureBasic MeasureFiniteAdditivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.
Local Open Scope ereal_scope.

(** Source for [measure_disjoint_sum_bound]: Federer 2.1.6(2),
    p. 59, supporting finite-subsums proof: the sum of the measures
    of any disjoint measurable family is bounded by the measure of
    a containing set. No countability is imposed on the family. *)
Lemma measure_disjoint_sum_bound (R : realType) (I J : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (X : set I)
    (D : set J) (F : J -> set I) :
  (forall j, D j -> F j `<=` X) ->
  (forall j, D j -> measure_measurable mu (F j)) ->
  (forall j k, D j -> D k -> j <> k -> F j `&` F k = set0) ->
  nonnegative_sum D (fun j => mu (F j)) <= mu X.
Proof.
move=> hX hF hd; apply: nonnegative_sum_least=> B hB.
have hmB j : j \in B -> measure_measurable mu (F j) by move=> hj; exact: hF (hB j hj).
have hdB j k : j \in B -> k \in B -> j != k -> forall x, F j x -> F k x -> False.
  move=> hj hk /eqP hne x hxj hxk; have hx : (F j `&` F k) x by split.
  by rewrite (hd j k (hB j hj) (hB k hk) hne) in hx.
rewrite -(@measure_finite_disjoint_additivity R I J mu hm F B hmB hdB).
apply: (@measure_mono R I mu hm _ X)=> x [j hj hx].
exact: (hX j (hB j hj) x hx).
Qed.

(** Source for [measure_disjoint_positive_countable]: Federer
    2.1.6(2), p. 59, first countability assertion in the successor
    proof. Finite total measure and disjoint measurable members imply
    countably many positive members, by 2.1.1(12), p. 53. *)
Theorem measure_disjoint_positive_countable (R : realType) (I J : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (X : set I)
    (D : set J) (F : J -> set I) : mu X < +oo ->
  (forall j, D j -> F j `<=` X) ->
  (forall j, D j -> measure_measurable mu (F j)) ->
  (forall j k, D j -> D k -> j <> k -> F j `&` F k = set0) ->
  countable (D `&` [set j | 0 < mu (F j)]).
Proof.
move=> hf hX hF hd.
have hs : nonnegative_sum D (fun j => mu (F j)) < +oo.
  exact: le_lt_trans (measure_disjoint_sum_bound hm hX hF hd) hf.
have hn j : D j -> 0 <= mu (F j) by move=> _; exact: (measure_nonnegative hm).
have hc := @nonnegative_sum_countable_support R J D (fun j => mu (F j)) hn hs.
apply: sub_countable _ hc; apply: subset_card_le=> j [hj hp]; split=> //.
by apply/eqP=> he; move: hp; rewrite /= he ltxx.
Qed.

(** Federer (1969), 2.1.3(3), p. 55: additivity of countable disjoint
    measurable families. The arbitrary countable-index formulation implies
    the printed sequence statement and includes empty families. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum MeasureUP MeasureBasic
  MeasureIndexedCover MeasureFiniteAdditivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_countable_disjoint_additivity]: Federer 2.1.3(3), p.
    55. The lower bound is proved on every finite subfamily using the book's
    finite-union induction; the upper bound is the measure covering law. *)
Theorem measure_countable_disjoint_additivity (R : realType)
    (I J : choiceType) (mu : set I -> \bar R) (hm : is_measure mu)
    (D : set J) (F : J -> set I) :
  countable D ->
  (forall j, D j -> measure_measurable mu (F j)) ->
  (forall j k, D j -> D k -> j != k -> forall x, F j x -> F k x -> False) ->
  mu (\bigcup_(j in D) F j) = nonnegative_sum D (fun j => mu (F j)).
Proof.
move=> hD hF hd; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@measure_indexed_cover R I J mu hm _ D F hD)=> x hx; exact hx.
- apply: nonnegative_sum_least=> B hB.
  have hFB : forall j, j \in B -> measure_measurable mu (F j).
    move=> j hj; exact: hF (hB j hj).
  have hdB : forall j k, j \in B -> k \in B -> j != k ->
      forall x, F j x -> F k x -> False.
    move=> j k hj hk; exact: hd (hB j hj) (hB k hk).
  rewrite -(@measure_finite_disjoint_additivity R I J mu hm F B hFB hdB).
  apply: (@measure_mono R I mu hm _ _)=> x [j hj hxj].
  by exists j; first exact: hB.
Qed.

(** Source for [measure_sequence_disjoint_additivity]: Federer
    2.1.3(3), p. 55, printed sequence formulation. Natural indices
    start at zero in Rocq, corresponding to the book's positive indices. *)
Corollary measure_sequence_disjoint_additivity (R : realType)
    (I : choiceType) (mu : set I -> \bar R) (hm : is_measure mu)
    (F : nat -> set I) :
  (forall n, measure_measurable mu (F n)) ->
  (forall n m, n != m -> forall x, F n x -> F m x -> False) ->
  mu (\bigcup_n F n) = nonnegative_sum setT (fun n => mu (F n)).
Proof.
move=> hF hd.
apply: (@measure_countable_disjoint_additivity R I _ mu hm setT F (countableP _)).
- by move=> n _; exact: hF.
- by move=> n m _ _; exact: hd.
Qed.

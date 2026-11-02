(** Uniqueness from the supremum definition of Federer (1969), 2.10.1, p.
    170. This lets later specializations identify independently specified
    measures. Source context: CaratheodoryLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_limit_unique]: the infima and
    their supremum uniquely determine every measure value
    in Federer 2.10.1, p. 170. *)
Lemma caratheodory_limit_unique (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu rho : set X -> \bar R) :
  is_caratheodory_limit S cost mu -> is_caratheodory_limit S cost rho ->
  forall A, mu A=rho A.
Proof.
move=> hm hr A; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (caratheodory_limit_least hm)=> delta nu hd hn.
  exact (@caratheodory_limit_upper R X J S cost rho hr A delta nu hd hn).
- apply: (caratheodory_limit_least hr)=> delta nu hd hn.
  exact (@caratheodory_limit_upper R X J S cost mu hm A delta nu hd hn).
Qed.

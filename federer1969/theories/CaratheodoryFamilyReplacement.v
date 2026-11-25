(** Supporting replacement of individual generators for Federer (1969),
    2.10.2, p. 171. Choose a containing target generator with no larger
    diameter or cost, and apply the already proved cover transport. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricDiameter CaratheodoryLimitUP CaratheodoryTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_family_replacement]: supporting
    quantified-generator comparison for the alternative
    covering families of Federer 2.10.2, p. 171.
    Repetitions are handled by the existing numerical-sum
    image bound; no injectivity of the choices is imposed. *)
Theorem caratheodory_family_replacement (R : realType) (X : metricType R)
    (J K : choiceType) (S : J -> set X) (T : K -> set X)
    (c : J -> \bar R) (d : K -> \bar R) (mu nu : set X -> \bar R) :
  is_caratheodory_limit S c mu -> is_caratheodory_limit T d nu ->
  (forall k, 0<=d k) ->
  (forall j, exists k, S j `<=` T k /\
    extended_metric_diameter (T k)<=extended_metric_diameter (S j) /\ d k<=c j) ->
  forall A, nu A<=mu A.
Proof.
move=> hm hn hd hex A.
pose u j := projT1 (cid (hex j)).
have hu j : S j `<=` T (u j) /\
    extended_metric_diameter (T (u j))<=extended_metric_diameter (S j) /\ d (u j)<=c j.
  exact: projT2 (cid (hex j)).
have hh := @caratheodory_limit_transport R X X J K S T c d id u mu nu hm hn hd
  (fun j x hx => (hu j).1 x hx) (fun j => (hu j).2.1) (fun j => (hu j).2.2) A.
by rewrite image_id in hh.
Qed.

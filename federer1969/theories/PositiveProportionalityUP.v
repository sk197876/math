(** Federer (1969), 2.4.15, p. 89: almost positive proportionality in the
    bracketed equality criterion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_positive_multiple_locus]: supporting graph
    formulation of positive proportionality in Federer 2.4.15, p. 89 Both
    function values must be defined at the point. *)
Definition partial_positive_multiple_locus (R : realType) (X : Type)
    (V : lmodType R) (c : R) (f g : partial_function X V) :=
  [set x | exists u v, partial_function_graph f x u /\ partial_function_graph g x v /\ u=c *: v].

(** Source for [measure_almost_positively_proportional]: direct
    specification of the bracketed condition in Federer 2.4.15, p. 89. One
    global nonnegative coefficient and one orientation are chosen before the
    almost-everywhere quantifier; zero is allowed. *)
Definition measure_almost_positively_proportional (R : realType) (X : choiceType)
    (V : lmodType R) (mu : set X -> \bar R) (f g : partial_function X V) :=
  exists c : R, 0 <= c /\
    (measure_almost_everywhere mu (partial_positive_multiple_locus c f g) \/
     measure_almost_everywhere mu (partial_positive_multiple_locus c g f)).

(** Federer (1969), 2.1.6(2), pp. 58-59: the successor of an Ulam cardinal.
    Cardinal representatives are sets and comparison means existence of an
    injection. The specification below expresses strict comparison with no
    intermediate cardinal, rather than constructing von Neumann ordinals.
    Kelley, General Topology, Appendix, pp. 275-276 (Dover 2017 reprint of
    1955), gives the cardinal-comparison background. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [is_cardinal_successor]: Federer 2.1.6(2),
    pp. 58-59, hypothesis that beta is the successor of alpha.
    This abstract specification says A is strictly smaller than B
    and any cardinal bounded by B but not by A equals B. It
    introduces no project axiom and assumes no ordinal construction. *)
Definition is_cardinal_successor (I J : choiceType) (A : set I) (B : set J) :=
  A #<= B /\ ~ (B #<= A) /\
  forall (K : choiceType) (C : set K), C #<= B -> ~ (C #<= A) -> B #<= C.

(** Source for [well_order_prefix]: Federer 2.1.6(2), p. 59,
    the set of predecessors of x, written x itself in the book's
    von Neumann ordinal convention. Here it is explicit for a
    reflexive ordering relation r on an ambient type. *)
Definition well_order_prefix (J : choiceType) (D : set J) (r : rel J) x :=
  [set y | D y /\ r y x /\ y <> x].

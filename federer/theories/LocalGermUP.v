(** Federer (1969), 3.4.5, p. 319: germs are specified by
    agreement on a neighbourhood of the original centre. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [locally_equal_at]: the equivalence relation
    defining function germs in 3.4.5, p. 319. An open
    neighbourhood suffices, since every neighbourhood contains one. *)
Definition locally_equal_at (X:topologicalType) (Y:Type) (a:X)
    (f g:X->Y):Prop:=
  exists U:set X,open U /\ U a /\ forall x,U x ->f x=g x.

(** Source for [is_local_germ_space]: the resulting equivalence
    classes in 3.4.5, p. 319, specified before construction.
    Representatives may carry their actual-domain and analyticity proofs;
    equality is exactly local agreement, and every germ has a representative. *)
Record is_local_germ_space (X:topologicalType) (Y:Type) (P:choiceType)
    (value:P->X->Y) (a:X) (G:choiceType) (germ:P->G):Prop:={
  (** Source for [local_germ_equality]: exactly the defining
      neighbourhood equivalence of 3.4.5, p. 319. *)
  local_germ_equality:forall f g,germ f=germ g <->locally_equal_at a (value f) (value g);
  (** Source for [local_germ_representative]: every equivalence
      class has a representative, implicit in 3.4.5, p. 319. *)
  local_germ_representative:forall alpha:G,exists f,germ f=alpha
}.

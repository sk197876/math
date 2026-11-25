(** Federer (1969), 3.4.8(11), p. 333:
    the zero-dimensional point germ contributes
    one stratum exactly when the centre
    is outside the original S0. These
    identities use the actual centre membership. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermSealed SetGermLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [set_germ_point_difference_inside]:
    an original S0 containing the centre
    removes the point germ, supporting
    3.4.8(11), p. 333. *)
Lemma set_germ_point_difference_inside (X:topologicalType) (a:X) (S:set X):
  S a ->@SetGerms.meet X a (@set_germ X a [set a])
    (@SetGerms.neg X a (@set_germ X a S)) = @set_germ X a set0.
Proof.
move=>hSa.
rewrite (@set_germ_complement_equation X a _ _ _ (@SetGerms.laws X a))
  (@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a)).
congr (@set_germ X a _);apply/seteqP;split.
- by move=>x [-> hNot];exact:hNot hSa.
- by move=>x hEmpty.
Qed.

(** Source for [set_germ_point_difference_outside]:
    an original S0 omitting the centre
    leaves exactly the point germ,
    supporting 3.4.8(11), p. 333. *)
Lemma set_germ_point_difference_outside (X:topologicalType) (a:X) (S:set X):
  ~S a ->@SetGerms.meet X a (@set_germ X a [set a])
    (@SetGerms.neg X a (@set_germ X a S)) = @set_germ X a [set a].
Proof.
move=>hSa.
rewrite (@set_germ_complement_equation X a _ _ _ (@SetGerms.laws X a))
  (@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a)).
congr (@set_germ X a _);apply/seteqP;split.
- by move=>x [hx _].
- by move=>x ->;split.
Qed.

(** General topology supporting Federer (1969),
    3.4.10, p. 337: a point of
    a set has a nonempty set germ. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [set_germ_centre_member_nonempty]: the
    nonempty local dimensions in the supremum
    of 3.4.10, p. 337. This
    supporting fact uses only actual neighbourhood equality. *)
Theorem set_germ_centre_member_nonempty (X:topologicalType) (a:X) (S:set X):
  S a ->@set_germ X a S<>@set_germ X a set0.
Proof.
move=>ha /set_germ_equality_original [W [hW [haW hEqual]]].
have h:(set0 `&` W) a by rewrite -hEqual;split.
exact:h.1.
Qed.

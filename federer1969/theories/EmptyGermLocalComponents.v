(** Federer (1969), 3.4.8(11), p. 333:
    an empty critical germ has a neighbourhood
    meeting no components. This boundary case
    needs no convention for its dimension. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import SetGermUP SetGermExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [empty_germ_local_component_finiteness]:
    the empty-germ case in the local
    critical-component induction, 3.4.8(11), p. 333. *)
Theorem empty_germ_local_component_finiteness (X:topologicalType) (a:X) (H:set X):
  @set_germ X a H = @set_germ X a set0 ->
  exists U:set X,open U /\ U a /\
    finite_set (connected_component H @` (H `&` U)).
Proof.
move=>hGerm.
have [U [hU [ha hEmpty]]]:=(@set_germ_equality_original X a H set0).1 hGerm.
exists U;split;first exact:hU.
split;first exact:ha.
have hImage:connected_component H @` (H `&` U) = set0.
  apply/seteqP;split;last by [].
  move=>C [x hx hC].
  have hFalse:(set0 `&` U) x by rewrite -hEmpty.
  exact:hFalse.1.
rewrite hImage;exact:finite_set0.
Qed.

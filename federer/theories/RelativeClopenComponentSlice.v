(** General topology supporting Federer (1969), 3.4.9,
    p. 337: a relatively open and closed piece
    inside a compact set inherits the finite count
    of ambient components meeting that compact set. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import RelativeClopenComponents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [relative_clopen_component_slice_finite]: the finite
    component assertion for the restricted original strata
    in 3.4.9, p. 337. The already proved
    component identity avoids any new connectivity argument. *)
Theorem relative_clopen_component_slice_finite (X:topologicalType) (S T O K:set X):
  open O ->S=T `&` O ->T `&` closure S `<=` S ->S `<=` K ->
  finite_set (connected_component T @` (T `&` K)) ->
  finite_set (connected_component S @` S).
Proof.
move=>hO hEquation hClosed hSK hFinite.
apply:(sub_finite_set _ hFinite)=>C [a ha <-].
have haT:T a by rewrite hEquation in ha;exact:ha.1.
rewrite (relative_clopen_component_equation hO hEquation hClosed ha).
exists a;first by split=>//;exact:hSK a ha.
reflexivity.
Qed.

(** General topology supporting Federer (1969), 3.1.23,
    p. 237: a continuous map equal to identity outside a
    compact subset is proper. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import ProperMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_identity_support_proper]: the assertion
    that the supported straightening map is proper, Federer
    3.1.23, p. 237. A compact-set inverse image
    is a closed subset of the union of that compact set
    with the compact support. Only Hausdorff topology is used. *)
Theorem compact_identity_support_proper (X:topologicalType) (K:set X) (f:X->X) :
  hausdorff_space X -> compact K -> continuous f ->
  (forall x,~K x -> f x=x) -> is_proper_map f.
Proof.
move=>hX hK hf hfix L hL.
have hLc:closed L:=compact_closed hX hL.
have hpre:closed (f @^-1` L).
  apply: preimage_closed; last exact hLc.
  by move=>x _; exact: hf.
apply: (@subclosed_compact X (f @^-1` L) (K `|` L) hpre (compactU hK hL)).
move=>x hx; case:(pselect (K x))=>[hk|hk]; first by left.
right; by rewrite -(hfix x hk).
Qed.

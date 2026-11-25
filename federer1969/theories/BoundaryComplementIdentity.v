(** Federer (1969), 3.2.43, printed p. 278:
    both strict distance strips use the same actual boundary,
    since a set and its complement have equal boundaries. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [topological_boundary_complement]: general
    topology supporting the two boundary-tube inclusions in
    Federer 3.2.43, p. 278. Boundary means closure minus
    interior, exactly as in the printed proof. *)
Lemma topological_boundary_complement (X:topologicalType) (S:set X):
  closure (~`S) `\` interior (~`S)=closure S `\` interior S.
Proof.
have hInterior:interior S=~`closure (~`S).
  by rewrite -interiorC setCK.
rewrite hInterior interiorC.
apply/seteqP; split=>x [hFirst hSecond].
- split; first exact:contrapT hSecond.
  by move=>hNoClosure; exact:hNoClosure hFirst.
- split; first exact:contrapT hSecond.
  by move=>hNoClosure; exact:hNoClosure hFirst.
Qed.

(** Federer (1969), 2.3.2, p. 74: supporting Borel domain calculations for
    partial arithmetic. These are finite Boolean forms of the local
    Borel-family laws of 2.2.1, pp. 59–60. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_boolean_negation]: supporting complement calculation
    for the defined arithmetic domains in Federer 2.3.2, p. 74 *)
Lemma borel_boolean_negation (X : topologicalType) (p : X -> bool) :
  borel_set [set x | p x] -> borel_set [set x | ~~ p x].
Proof.
move=> hp; have he : [set x | ~~ p x] = ~` [set x | p x].
  apply/seteqP; split=> x; [by move/negP|by move=> hn; apply/negP].
rewrite he; exact: borel_set_complement hp.
Qed.

(** Source for [borel_boolean_conjunction]: supporting finite intersection
    calculation for Federer 2.3.2, p. 74. *)
Lemma borel_boolean_conjunction (X : topologicalType) (p q : X -> bool) :
  borel_set [set x | p x] -> borel_set [set x | q x] -> borel_set [set x | p x && q x].
Proof.
move=> hp hq; have he : [set x | p x && q x] = [set x | p x] `&` [set x | q x].
  apply/seteqP; split=> x; [by move/andP|by move=> h; apply/andP].
rewrite he; exact: (borel_family_binary_intersection (borel_sets_family X) hp hq).
Qed.

(** Source for [borel_boolean_disjunction]: supporting finite union
    calculation for Federer 2.3.2, p. 74. *)
Lemma borel_boolean_disjunction (X : topologicalType) (p q : X -> bool) :
  borel_set [set x | p x] -> borel_set [set x | q x] -> borel_set [set x | p x || q x].
Proof.
move=> hp hq; have he : [set x | p x || q x] = [set x | p x] `|` [set x | q x].
  apply/seteqP; split=> x; [by move/orP|by move=> h; apply/orP].
rewrite he; exact: (borel_family_binary_union (borel_sets_family X) hp hq).
Qed.

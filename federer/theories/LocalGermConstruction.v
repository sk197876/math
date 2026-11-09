(** Federer (1969), 3.4.5, p. 319: a private quotient
    construction proves existence of the independently specified germs.
    The generic set quotient is the same background mechanism used
    for the module quotient of 1.1.1; no analytic theorem is imported. *)
From HB Require Import structures.
From mathcomp Require Import all_boot boolp classical_sets topology generic_quotient.
From Federer Require Import LocalGermUP LocalGermEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope quotient_scope.
Section Construction.
Variable X:topologicalType.
Variable Y:Type.
Variable P:choiceType.
Variable value:P->X->Y.
Variable a:X.

(** Source for [local_germ_relation]: the Boolean presentation
    of the original equivalence relation, 3.4.5, p. 319,
    used only to construct the background set quotient. *)
Definition local_germ_relation (f g:P):= `[<locally_equal_at a (value f) (value g)>].

(** Source for [local_germ_relation_refl]: the quotient
    relation is reflexive, 3.4.5, p. 319. *)
Lemma local_germ_relation_refl:reflexive local_germ_relation.
Proof. move=>f;apply/asboolP;exact:locally_equal_refl. Qed.

(** Source for [local_germ_relation_sym]: the quotient
    relation is symmetric, 3.4.5, p. 319. *)
Lemma local_germ_relation_sym:symmetric local_germ_relation.
Proof.
move=>f g;apply/idP/idP=>/asboolP h;apply/asboolP;exact:locally_equal_sym h.
Qed.

(** Source for [local_germ_relation_trans]: the quotient
    relation is transitive, 3.4.5, p. 319. *)
Lemma local_germ_relation_trans:transitive local_germ_relation.
Proof.
move=>g f h /asboolP hF /asboolP hG;apply/asboolP.
exact:locally_equal_trans hF hG.
Qed.
Canonical local_germ_equivalence:=EquivRel local_germ_relation
  local_germ_relation_refl local_germ_relation_sym local_germ_relation_trans.

(** Source for [local_germ_quotient]: an existence witness for
    the equivalence classes in 3.4.5, p. 319. Its
    representation is hidden from downstream proofs by the seal. *)
Definition local_germ_quotient:={eq_quot local_germ_relation}.
HB.instance Definition _:=Choice.copy local_germ_quotient {eq_quot local_germ_relation}.

(** Source for [local_germ_quotient_projection]: the private
    representative-to-class map of 3.4.5, p. 319. *)
Definition local_germ_quotient_projection (f:P):local_germ_quotient:=\pi_local_germ_quotient f.

(** Source for [local_germ_quotient_laws]: the private quotient
    satisfies exactly the independent germ laws, 3.4.5, p. 319. *)
Lemma local_germ_quotient_laws:
  is_local_germ_space value a local_germ_quotient_projection.
Proof.
constructor.
- move=>f g;split=>h.
  + apply/asboolP;apply/(eqmodP local_germ_equivalence);exact:h.
  + apply/(eqmodP local_germ_equivalence)/asboolP;exact:h.
- move=>alpha;exists (repr alpha);exact:reprK.
Qed.
End Construction.

(** Source for [local_germ_space_exists]: existence of the
    equivalence classes specified in 3.4.5, p. 319.
    No function regularity or algebraic theorem is assumed. *)
Theorem local_germ_space_exists (X:topologicalType) (Y:Type)
    (P:choiceType) (value:P->X->Y) (a:X):
  exists (G:choiceType) (germ:P->G),is_local_germ_space value a germ.
Proof.
exists [the choiceType of @local_germ_quotient X Y P value a].
exists (@local_germ_quotient_projection X Y P value a).
exact:local_germ_quotient_laws.
Qed.

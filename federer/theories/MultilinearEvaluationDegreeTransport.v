(** Federer (1969), 4.1.1, p. 346: degree
    bookkeeping for the Taylor difference quotient.
    These equalities transport natural-number arities
    only and preserve every mathematical evaluation. *)
From mathcomp Require Import all_boot all_algebra.
From Federer Require Import Hom MultilinearSuccessorArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [multilinear_evaluation_degree_transport]:
    equal natural-number degrees describe the same
    evaluation, supporting the derivative grouping
    used by Federer 4.1.1, p. 346. *)
Lemma multilinear_evaluation_degree_transport (K:fieldType) (X Y:lmodType K)
    (Z:nat->lmodType K) (ev:forall k,{ffun 'I_k->X}->Hom (Z k) Y)
    (z:forall k,Z k) m n (h:m=n) (u:{ffun 'I_m->X}):
  @ev m u (z m)=@ev n (multilinear_arguments_cast h u) (z n).
Proof. subst n; by rewrite multilinear_arguments_cast_reflexive. Qed.

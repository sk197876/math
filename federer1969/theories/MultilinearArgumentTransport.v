(** Federer (1969), 3.1.11, p. 219:
    changing the written arity by an equality
    preserves the abstract multilinear-space laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom ContinuousMultilinearUP MultilinearSuccessorArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [continuous_multilinear_argument_transport]:
    the same multilinear argument space may
    be written with equal natural-number arities,
    supporting the recursive identification in
    Federer 3.1.11, p. 219. *)
Lemma continuous_multilinear_argument_transport (R : realType)
    (X Y Z : lmodType R) (NX : X->R) (NY : Y->R)
    m n (h : m=n) (e : {ffun 'I_n->X}->Hom Z Y) (ZN : Z->R) :
  is_continuous_multilinear_space NX NY e ZN ->
  is_continuous_multilinear_space NX NY
    (fun u : {ffun 'I_m->X}=>e (multilinear_arguments_cast h u)) ZN.
Proof.
subst n; move=>he.
have heq : (fun u : {ffun 'I_m->X}=>e (multilinear_arguments_cast (erefl m) u))=e.
  apply: funext=>u; by rewrite multilinear_arguments_cast_reflexive.
by rewrite heq.
Qed.

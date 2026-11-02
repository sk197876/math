(** Federer (1969), 2.6.6, p. 120: a finite product does not depend on the
    order of its factors. This supporting finite-list argument applies
    commuting operators on an invariant domain; no algebraic laws outside
    that domain are assumed. Source context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section Folds.
Variables (I : eqType) (T : Type) (K : set T) (U : I -> T -> T).
Hypothesis hU : forall i f, K f -> K (U i f).
Hypothesis hcomm : forall i j f, K f -> U i (U j f)=U j (U i f).

(** Source for [operator_fold_preserves_domain]: iterated finite
    coordinate integration preserves K(X), supporting Federer 2.6.6,
    p. 120. This lemma isolates the finite-list induction. *)
Lemma operator_fold_preserves_domain (s : seq I) (f : T) : K f -> K (foldr U f s).
Proof. move=> hf; elim: s=> [|i s ih] //=; exact: hU i _ ih. Qed.

(** Source for [operator_commutes_with_fold]: moving one coordinate
    integration across a finite family, supporting consistency in
    Federer 2.6.6, p. 120. *)
Lemma operator_commutes_with_fold (i : I) (s : seq I) (f : T) :
  K f -> U i (foldr U f s)=foldr U (U i f) s.
Proof.
move=> hf; elim: s=> [|j s ih] //=.
by rewrite (@hcomm i j _ (operator_fold_preserves_domain s hf)) ih.
Qed.

(** Source for [operator_folds_commute]: two finite blocks of
    coordinate integrations may be interchanged, supporting the
    finite-product construction in Federer 2.6.6, p. 120. *)
Lemma operator_folds_commute (s t : seq I) (f : T) :
  K f -> foldr U (foldr U f t) s=foldr U (foldr U f s) t.
Proof.
move=> hf; elim: s=> [|i s ih] //=.
by rewrite ih (operator_commutes_with_fold i t (operator_fold_preserves_domain s hf)).
Qed.

(** Source for [operator_fold_permutation]: independence of the
    enumeration of a finite coordinate set in Federer 2.6.6, p. 120.
    The proof uses only domain-preserving pairwise commutation. *)
Theorem operator_fold_permutation (s t : seq I) (f : T) :
  K f -> perm_eq s t -> foldr U f s=foldr U f t.
Proof.
move=> hf; apply: catCA_perm_subst=> s1 s2 s3.
rewrite !foldr_cat; exact: (@operator_folds_commute s1 s2 (foldr U f s3) (operator_fold_preserves_domain s3 hf)).
Qed.
End Folds.

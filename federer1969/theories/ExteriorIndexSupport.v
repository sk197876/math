(** Federer (1969), 1.7.5, pp. 32-33: the sets S(nu) grouping pairs of
    exterior indices in the general wedge estimate. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ExteriorIndices LambdaComplements.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [exterior_index_support]: Federer 1.7.5,
    pp. 32-33, S(nu): the two increasing index sets are
    disjoint and their union is the increasing output index. *)
Definition exterior_index_support n p q (lambda : Lambda n p)
    (mu : Lambda n q) (nu : Lambda n (p+q)) :=
  (Lambda_set lambda :|: Lambda_set mu == Lambda_set nu) && uniq (val lambda ++ val mu).

(** Source for [exterior_index_union_exists]: Federer 1.7.5,
    p. 32, supporting existence of the output index of a
    nonzero basis product, obtained by sorting the disjoint union. *)
Lemma exterior_index_union_exists n p q (lambda : Lambda n p) (mu : Lambda n q) :
  uniq (val lambda ++ val mu) -> exists nu : Lambda n (p+q),
    Lambda_set lambda :|: Lambda_set mu = Lambda_set nu /\
    perm_eq (val lambda ++ val mu) (val nu).
Proof.
move=> hu.
pose S := [set i : 'I_n in val lambda ++ val mu].
have hc : #|S| = (p+q)%N.
  rewrite /S cardsE (card_uniqP hu) size_cat !size_tuple; by [].
have [nu hn] := Lambda_set_surjective hc.
exists nu; split.
- rewrite hn; apply/setP=> i; by rewrite /S /Lambda_set !inE mem_cat.
- apply: uniq_perm; [exact hu | exact: Lambda_uniq |].
  move=> i; have hh := congr1 (fun A : {set 'I_n} => i \in A) hn.
  by rewrite /Lambda_set /S !inE in hh; symmetry.
Qed.

(** Source for [exterior_index_support_unique]: Federer
    1.7.5, pp. 32-33, a fixed pair of input indices
    contributes to at most one output coordinate. *)
Lemma exterior_index_support_unique n p q (lambda : Lambda n p) (mu : Lambda n q)
    (nu rho : Lambda n (p+q)) :
  exterior_index_support lambda mu nu -> exterior_index_support lambda mu rho -> nu = rho.
Proof.
move=> /andP[/eqP hn _] /andP[/eqP hr _].
apply: Lambda_set_injective; by rewrite -hn -hr.
Qed.

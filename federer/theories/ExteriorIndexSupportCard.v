(** Federer (1969), 1.7.5, pp. 32-33: counting the index pairs in S(nu). The
    upper bound suffices for the estimate; it is obtained by choosing the
    first subset. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ExteriorIndices LambdaComplements ExteriorIndexSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [exterior_index_support_complement]: Federer
    1.7.5, pp. 32-33, supporting uniqueness of the second
    index after fixing the output and the first index: it is the
    set difference of the output and first index sets. *)
Lemma exterior_index_support_complement n p q (lambda : Lambda n p)
    (mu : Lambda n q) (nu : Lambda n (p+q)) :
  exterior_index_support lambda mu nu ->
  Lambda_set mu = Lambda_set nu :\: Lambda_set lambda.
Proof.
move=> /andP[/eqP hu hd].
rewrite Lambda_disjointE in hd; apply/setP=> i; rewrite -hu in_setD in_setU.
case ha: (i \in Lambda_set lambda); case hb: (i \in Lambda_set mu) => //=.
have hh := (subsetP hd) i hb; by rewrite in_setC ha in hh.
Qed.

(** Source for [exterior_index_support_card_bound]: Federer
    1.7.5, p. 33, the number of contributing pairs for
    a fixed output is at most binomial(p+q,p), independently
    of the dimension of the ambient index set. *)
Theorem exterior_index_support_card_bound n p q (nu : Lambda n (p+q)) :
  #|[pred lm : (Lambda n p * Lambda n q)%type |
      exterior_index_support lm.1 lm.2 nu]| <= 'C(p+q,p).
Proof.
pose S := [set lm : (Lambda n p * Lambda n q)%type | exterior_index_support lm.1 lm.2 nu].
pose T := [set lambda : Lambda n p | Lambda_set lambda \subset Lambda_set nu].
have hinj : {in S &, injective (@fst (Lambda n p) (Lambda n q))}.
  move=> [a b] [c d] /=; rewrite /S !inE /= => hb hd hac.
  subst c; congr (_, _); apply: Lambda_set_injective.
  by rewrite (exterior_index_support_complement hb) (exterior_index_support_complement hd).
have hsub : (@fst (Lambda n p) (Lambda n q)) @: S \subset T.
  apply/subsetP=> a /imsetP[[b c] hbc ->]; rewrite /T inE.
  move: hbc; rewrite /S inE => /andP[/eqP hh _].
  by rewrite -hh subsetUl.
have hcT : #|T| = 'C(p+q,p).
  have hh : #|T| = #|[pred lambda : Lambda n p | Lambda_set lambda \subset Lambda_set nu]|.
    apply: eq_card => lambda; by rewrite /T inE.
  rewrite hh.
  by rewrite card_Lambda_subset Lambda_set_card.
have hcS : #|[pred lm : (Lambda n p * Lambda n q)%type | exterior_index_support lm.1 lm.2 nu]| = #|S|.
  apply: eq_card => lm; by rewrite /S inE.
rewrite hcS.
rewrite -(card_in_imset hinj) -hcT; exact: subset_leq_card.
Qed.

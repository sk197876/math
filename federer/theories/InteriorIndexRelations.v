(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import GrassmannTrace.
From Federer Require Import InteriorComplements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Federer 1.5.2: a union of increasing basis indices equals im mu
    exactly when the remaining index is the complement of im lambda. *)
(** Source for [Lambda_concat_subset]: Federer (1969), 1.5.2, p. 22, the two
    inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma Lambda_concat_subset n p q r (lambda : Lambda n p) (mu : Lambda n q)
  (kappa : Lambda n r) : perm_eq (val lambda ++ val kappa) (val mu) ->
  Lambda_set lambda \subset Lambda_set mu.
Proof.
move=> hp; apply/subsetP=> i; rewrite /Lambda_set !inE => hi.
rewrite -(perm_mem hp) mem_cat hi; by [].
Qed.
(** Source for [Lambda_concat_union]: Federer (1969), 1.5.2, p. 22, the two
    inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma Lambda_concat_union n p q r (lambda : Lambda n p) (mu : Lambda n q)
  (kappa : Lambda n r) : perm_eq (val lambda ++ val kappa) (val mu) ->
  Lambda_set lambda :|: Lambda_set kappa = Lambda_set mu.
Proof.
move=> hp; apply/setP=> i; rewrite /Lambda_set !inE -mem_cat.
by rewrite (perm_mem hp).
Qed.
(** Source for [nu_permutation]: Federer (1969), 1.5.2, p. 22, the two
    inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma nu_permutation n p q (lambda : Lambda n p) (mu : Lambda n q)
  (hsub : Lambda_set lambda \subset Lambda_set mu) :
  perm_eq (val lambda ++ val (nu hsub)) (val mu).
Proof.
apply: uniq_perm; [exact: nu_disjoint|exact: Lambda_uniq|].
move=> i; have h := congr1 (fun S : {set 'I_n} => i \in S) (nu_union hsub).
by rewrite /Lambda_set !inE mem_cat in h *.
Qed.
(** Source for [Lambda_concat_complement]: Federer (1969), 1.5.2, p. 22, the
    two inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma Lambda_concat_complement n p q (lambda : Lambda n p) (mu : Lambda n q)
  (hsub : Lambda_set lambda \subset Lambda_set mu) (kappa : Lambda n (q-p)) :
  perm_eq (val lambda ++ val kappa) (val mu) = (kappa == nu hsub).
Proof.
apply/idP/idP.
- move=> hp; apply/eqP; apply: complementary_index_unique.
  exact: Lambda_concat_union hp.
- move/eqP=> ->; exact: nu_permutation.
Qed.
(** Source for [Lambda_concat_not_subset]: Federer (1969), 1.5.2, p. 22, the
    two inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma Lambda_concat_not_subset n p q r (lambda : Lambda n p) (mu : Lambda n q)
  (kappa : Lambda n r) : ~~ (Lambda_set lambda \subset Lambda_set mu) ->
  ~~ perm_eq (val lambda ++ val kappa) (val mu).
Proof. move=> hn; apply/negP=> hp; exact (elimT negP hn (Lambda_concat_subset hp)). Qed.

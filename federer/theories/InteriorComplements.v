(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import GrassmannTrace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Federer 1.5.2: the increasing complementary index nu with
    im lambda union im nu = im mu. Its image is im mu minus im lambda. *)
Section RelativeComplement.
Variables n p q : nat.
Variable lambda : Lambda n p.
Variable mu : Lambda n q.
Hypothesis hsub : Lambda_set lambda \subset Lambda_set mu.
(** Source for [complement_card]: Federer (1969), 1.5.2, p. 22, the two
    inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma complement_card : #|Lambda_set mu :\: Lambda_set lambda| = q-p.
Proof. by rewrite (cardsDS hsub) !Lambda_set_card. Qed.
(** Source for [complementary_index_exists]: Federer (1969), 1.5.2, p. 22,
    the two inclusion cases and the definitions of M and N. In words: A
    basis interior product vanishes unless the contracted index set is
    contained in the other; otherwise it is the complementary basis product
    with the appropriate crossing-count sign. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Lemma complementary_index_exists : exists nu : Lambda n (q-p),
  Lambda_set nu = Lambda_set mu :\: Lambda_set lambda.
Proof. exact: Lambda_set_surjective complement_card. Qed.
(** Source for [nu]: Federer (1969), 1.5.2, p. 22, the two inclusion cases
    and the definitions of M and N. In words: A basis interior product
    vanishes unless the contracted index set is contained in the other;
    otherwise it is the complementary basis product with the appropriate
    crossing-count sign. Definition or construction used to formalise this
    passage. *)
Definition nu : Lambda n (q-p) := sval (constructive_indefinite_description complementary_index_exists).
(** Source for [nu_image]: Federer (1969), 1.5.2, p. 22, the two inclusion
    cases and the definitions of M and N. In words: A basis interior product
    vanishes unless the contracted index set is contained in the other;
    otherwise it is the complementary basis product with the appropriate
    crossing-count sign. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma nu_image : Lambda_set nu = Lambda_set mu :\: Lambda_set lambda.
Proof. exact: (svalP (constructive_indefinite_description complementary_index_exists)). Qed.
(** Source for [nu_disjoint]: Federer (1969), 1.5.2, p. 22, the two
    inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma nu_disjoint : uniq (val lambda ++ val nu).
Proof. by rewrite Lambda_disjointE nu_image subsetDr. Qed.
(** Source for [nu_union]: Federer (1969), 1.5.2, p. 22, the two inclusion
    cases and the definitions of M and N. In words: A basis interior product
    vanishes unless the contracted index set is contained in the other;
    otherwise it is the complementary basis product with the appropriate
    crossing-count sign. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma nu_union : Lambda_set lambda :|: Lambda_set nu = Lambda_set mu.
Proof.
rewrite nu_image; apply/setP=> i.
change ((i \in Lambda_set lambda :|: (Lambda_set mu :\: Lambda_set lambda)) = (i \in Lambda_set mu)).
rewrite in_setU in_setD.
case hi: (i \in Lambda_set lambda) => /=; last by [].
have hm := subsetP hsub i hi; by rewrite hm.
Qed.
(** Source for [complementary_index_unique]: Federer (1969), 1.5.2, p. 22,
    the two inclusion cases and the definitions of M and N. In words: A
    basis interior product vanishes unless the contracted index set is
    contained in the other; otherwise it is the complementary basis product
    with the appropriate crossing-count sign. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Lemma complementary_index_unique (kappa : Lambda n (q-p)) :
  Lambda_set lambda :|: Lambda_set kappa = Lambda_set mu -> kappa = nu.
Proof.
move=> hu; apply: Lambda_set_injective; rewrite nu_image.
have hs : Lambda_set mu :\: Lambda_set lambda \subset Lambda_set kappa.
  apply/subsetP=> i; rewrite -hu in_setD in_setU.
  by case: (i \in Lambda_set lambda); case: (i \in Lambda_set kappa).
have hc : #|Lambda_set mu :\: Lambda_set lambda| = #|Lambda_set kappa|.
  by rewrite complement_card Lambda_set_card.
by apply/eqP; rewrite eq_sym eqEcard hs hc leqnn.
Qed.
(** Source for [complementary_degrees]: Federer (1969), 1.5.2, p. 22, the
    two inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma complementary_degrees : (p <= q)%N.
Proof. have := subset_leq_card hsub; by rewrite !Lambda_set_card. Qed.
End RelativeComplement.

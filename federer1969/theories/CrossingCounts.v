(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import GrassmannTrace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Federer 1.5.2: count the crossings between two increasing blocks.
    These are the pair counts used for the exponents M and N. *)
(** Source for [crossing_count]: Federer (1969), 1.5.2, p. 22, the two
    inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Definition or construction used to
    formalise this passage. *)
Definition crossing_count (s t : seq nat) :=
  \sum_(i <- s) count (fun j => j < i) t.
(** Source for [inversions_cat]: Federer (1969), 1.5.2, p. 22, the two
    inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma inversions_cat s t : inversions (s++t) =
  inversions s + inversions t + crossing_count s t.
Proof.
elim: s => [|i s ih]; first by rewrite /crossing_count big_nil /= addn0.
rewrite /crossing_count big_cons /= count_cat ih /crossing_count -!addnA.
by rewrite (addnCA (count (fun j => j < i) t) (inversions s))
  (addnCA (count (fun j => j < i) t) (inversions t)).
Qed.
(** Source for [crossing_count_card]: Federer (1969), 1.5.2, p. 22, the two
    inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma crossing_count_card (T : finType) (s t : seq T) (R : rel T) :
  uniq s -> uniq t ->
  \sum_(i <- s) count (R i) t =
    #|[set ij : (T*T)%type | [&& ij.1 \in s, ij.2 \in t & R ij.1 ij.2]]|.
Proof.
move=> hs ht; rewrite (big_uniq _ hs).
have hcount i : count (R i) t = \sum_(j : T | (j \in t) && R i j) 1.
  rewrite -sum1_count -big_filter (big_uniq _ (filter_uniq _ ht)).
  apply: eq_bigl => j; by rewrite mem_filter andbC.
under eq_bigr do rewrite hcount.
rewrite pair_big_dep -sum1_card.
apply: eq_bigl => ij; by rewrite inE andbA.
Qed.
(** Source for [crossing_count_Lambda]: Federer (1969), 1.5.2, p. 22, the
    two inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma crossing_count_Lambda n p q (lambda : Lambda n p) (kappa : Lambda n q) :
  crossing_count (map val (val lambda)) (map val (val kappa)) =
    #|[set ij : ('I_n*'I_n)%type |
      [&& ij.1 \in Lambda_set lambda, ij.2 \in Lambda_set kappa & ij.2 < ij.1]]|.
Proof.
rewrite /crossing_count big_map.
under eq_bigr do rewrite count_map.
rewrite (crossing_count_card (fun i j : 'I_n => j < i) (Lambda_uniq lambda) (Lambda_uniq kappa)).
apply: eq_card => ij; by rewrite !inE.
Qed.
(** Source for [Lambda_inversions]: Federer (1969), 1.5.2, p. 22, the two
    inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma Lambda_inversions n p (lambda : Lambda n p) : inversions (map val (val lambda)) = 0.
Proof.
apply: inversions_sorted; have := valP lambda.
by rewrite ltn_sorted_uniq_leq => /andP [].
Qed.
(** Source for [Lambda_concat_inversions]: Federer (1969), 1.5.2, p. 22, the
    two inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma Lambda_concat_inversions n p q (lambda : Lambda n p) (kappa : Lambda n q) :
  inversions (map val (val lambda ++ val kappa)) =
    #|[set ij : ('I_n*'I_n)%type |
      [&& ij.1 \in Lambda_set lambda, ij.2 \in Lambda_set kappa & ij.2 < ij.1]]|.
Proof.
by rewrite map_cat inversions_cat !Lambda_inversions add0n crossing_count_Lambda.
Qed.

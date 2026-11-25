(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import DualExterior.
From Federer Require Import SharedIndices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Federer 1.4.5, trace contraction: exactly binomial(n-m,j)
    increasing j-indices are disjoint from a given m-index. *)
(** Source for [Lambda_uniq]: Federer (1969), 1.4.5, pp. 20-21, last display
    of p. 20 and its hypotheses at the top of p. 21. In words: Multiplying a
    degree-m diagonal tensor by Gamma of the identity on the j-th exterior
    power multiplies its trace by binomial(n-m,j), for 0<=j<=n-m. Supporting
    lemma for this passage; not separately stated in the book. The local
    LaTeX erratum (May 1987), p. 1, entry for book p. 20 line 32, corrects
    the identity to the identity on the j-th exterior power. *)
Lemma Lambda_uniq n m (lambda : Lambda n m) : uniq (val lambda).
Proof. apply/tuple_uniqP; exact: Lambda_tnth_injective. Qed.
(** Source for [Lambda_set]: Federer (1969), 1.4.5, pp. 20-21, last display
    of p. 20 and its hypotheses at the top of p. 21. In words: Multiplying a
    degree-m diagonal tensor by Gamma of the identity on the j-th exterior
    power multiplies its trace by binomial(n-m,j), for 0<=j<=n-m. Definition
    or construction used to formalise this passage. The local LaTeX erratum
    (May 1987), p. 1, entry for book p. 20 line 32, corrects the identity to
    the identity on the j-th exterior power. *)
Definition Lambda_set n m (lambda : Lambda n m) : {set 'I_n} := [set i in val lambda].
(** Source for [Lambda_set_card]: Federer (1969), 1.4.5, pp. 20-21, last
    display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma Lambda_set_card n m (lambda : Lambda n m) : #|Lambda_set lambda| = m.
Proof.
rewrite /Lambda_set cardsE (card_uniqP (Lambda_uniq lambda)); exact: size_tuple.
Qed.
(** Source for [Lambda_set_injective]: Federer (1969), 1.4.5, pp. 20-21,
    last display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma Lambda_set_injective n m : injective (@Lambda_set n m).
Proof.
move=> lambda mu h; apply: Lambda_perm_equal.
apply: uniq_perm; [exact: Lambda_uniq | exact: Lambda_uniq |].
move=> i; have hi := congr1 (fun S : {set 'I_n} => i \in S) h.
by rewrite /Lambda_set !inE in hi.
Qed.
(** Source for [ordinal_set_sorted]: Federer (1969), 1.4.5, pp. 20-21, last
    display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma ordinal_set_sorted n (S : {set 'I_n}) : sorted ltn (map val (enum S)).
Proof.
rewrite -[enum _](eq_filter (mem_enum _)).
rewrite -(eq_filter (mem_map val_inj _)) -filter_map.
by rewrite (sorted_filter ltn_trans) // unlock val_ord_enum iota_ltn_sorted.
Qed.
(** Source for [Lambda_set_surjective]: Federer (1969), 1.4.5, pp. 20-21,
    last display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma Lambda_set_surjective n m (S : {set 'I_n}) : #|S| = m ->
  exists lambda : Lambda n m, Lambda_set lambda = S.
Proof.
move=> hs.
have hl : size (enum S) == m by rewrite -cardE hs eqxx.
pose t : m.-tuple 'I_n := Tuple hl.
have ht : sorted ltn (map val t) := ordinal_set_sorted S.
exists (Sub t ht); apply/setP=> i; by rewrite /Lambda_set inE mem_enum.
Qed.
(** Source for [card_Lambda_subset]: Federer (1969), 1.4.5, pp. 20-21, last
    display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Theorem card_Lambda_subset n j (S : {set 'I_n}) :
  #|[pred kappa : Lambda n j | Lambda_set kappa \subset S]| = 'C(#|S|,j).
Proof.
pose B : {set Lambda n j} := [set kappa | Lambda_set kappa \subset S].
pose C : {set {set 'I_n}} := [set T : {set 'I_n} | (T \subset S) && (#|T| == j)].
have hBC : (@Lambda_set n j) @: B = C.
  apply/setP=> T; rewrite /C inE; apply/imsetP/andP.
  - move=> [k hk ->]; split; first by move: hk; rewrite /B inE.
    by rewrite Lambda_set_card eqxx.
  - move=> [hTS /eqP hT]; have [k hk] := Lambda_set_surjective hT.
    exists k; [by rewrite /B inE hk | exact (esym hk)].
have hc : #|(@Lambda_set n j) @: B| = #|B| := card_imset B (@Lambda_set_injective n j).
rewrite hBC in hc.
have hB : #|[pred kappa : Lambda n j | Lambda_set kappa \subset S]| = #|B|.
  apply: eq_card => kappa; by rewrite /B !inE.
rewrite hB.
rewrite -hc; exact: cards_draws.
Qed.
(** Source for [Lambda_disjointE]: Federer (1969), 1.4.5, pp. 20-21, last
    display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma Lambda_disjointE n m j (lambda : Lambda n m) (kappa : Lambda n j) :
  uniq (val lambda ++ val kappa) = (Lambda_set kappa \subset ~: Lambda_set lambda).
Proof.
rewrite cat_uniq !Lambda_uniq /= andbT.
rewrite -all_predC; apply/allP/subsetP.
- move=> h i; rewrite /Lambda_set !inE => hi.
  exact: h i hi.
- move=> h i hi; have := h i; rewrite /Lambda_set !inE; exact.
Qed.
(** Source for [card_Lambda_complement]: Federer (1969), 1.4.5, pp. 20-21,
    last display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Formalises the indicated part of the passage under the
    hypotheses in the statement below. The local LaTeX erratum (May 1987),
    p. 1, entry for book p. 20 line 32, corrects the identity to the
    identity on the j-th exterior power. *)
Theorem card_Lambda_complement n m j (lambda : Lambda n m) :
  #|[pred kappa : Lambda n j | uniq (val lambda ++ val kappa)]| = 'C(n-m,j).
Proof.
transitivity #|[pred kappa : Lambda n j | Lambda_set kappa \subset ~: Lambda_set lambda]|.
- apply: eq_card => kappa; exact: Lambda_disjointE.
- rewrite card_Lambda_subset (cardsCs (~: Lambda_set lambda)) setCK card_ord Lambda_set_card.
  by [].
Qed.

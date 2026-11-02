(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import DualExterior.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Federer 1.4.5, trace contraction: appending the same increasing
    sequence to two basis indices cannot turn distinct indices into
    permutations of one another. Repeated indices vanish separately. *)
(** Source for [tuple_matching_permutation]: Federer (1969), 1.4.5, pp.
    20-21, last display of p. 20 and its hypotheses at the top of p. 21. In
    words: Multiplying a degree-m diagonal tensor by Gamma of the identity
    on the j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma tuple_matching_permutation (I : eqType) m (s t : m.-tuple I) (sigma : 'S_m) :
  (forall i, tnth s i = tnth t (sigma i)) -> perm_eq s t.
Proof.
move=> h.
have hp : perm_eq (permutation_sequence sigma) (enum 'I_m).
  apply: uniq_perm; [exact: permutation_sequence_uniq | exact: enum_uniq |].
  by move=> i; rewrite permutation_sequence_mem mem_enum.
have hs : val s = map (tnth t) (permutation_sequence sigma).
  rewrite -[LHS]map_tnth_enum -(map_comp (tnth t) sigma (enum 'I_m)).
  apply: eq_map => i; exact: h.
rewrite hs -(map_tnth_enum t); exact: perm_map hp.
Qed.
(** Source for [Lambda_perm_equal]: Federer (1969), 1.4.5, pp. 20-21, last
    display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma Lambda_perm_equal n m (lambda mu : Lambda n m) :
  perm_eq (val lambda) (val mu) -> lambda = mu.
Proof.
move=> hp; apply: val_inj; apply: val_inj; apply: (inj_map val_inj).
apply: (irr_sorted_eq ltn_trans ltnn (valP lambda) (valP mu)).
apply: perm_mem; exact: perm_map hp.
Qed.
(** Source for [Lambda_shared_permutation]: Federer (1969), 1.4.5, pp.
    20-21, last display of p. 20 and its hypotheses at the top of p. 21. In
    words: Multiplying a degree-m diagonal tensor by Gamma of the identity
    on the j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma Lambda_shared_permutation n m j (lambda mu : Lambda n m)
    (kappa : Lambda n j) (sigma : 'S_(m+j)) :
  (forall i, tnth (cat_tuple (val lambda) (val kappa)) i =
    tnth (cat_tuple (val mu) (val kappa)) (sigma i)) -> lambda = mu.
Proof.
move=> h; have hp := tuple_matching_permutation h.
change (is_true (perm_eq (val lambda ++ val kappa) (val mu ++ val kappa))) in hp.
rewrite perm_cat2r in hp; exact: Lambda_perm_equal hp.
Qed.
(** Source for [Lambda_shared_delta]: Federer (1969), 1.4.5, pp. 20-21, last
    display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma Lambda_shared_delta n m j (lambda mu : Lambda n m)
    (kappa : Lambda n j) (sigma : 'S_(m+j)) :
  uniq (val lambda ++ val kappa) ->
  all (fun i => tnth (cat_tuple (val lambda) (val kappa)) i ==
    tnth (cat_tuple (val mu) (val kappa)) (sigma i)) (enum 'I_(m+j)) =
  ((lambda == mu) && (sigma == 1%g)).
Proof.
move=> hu; apply/idP/idP.
- move/allP=> h.
  have hp i : tnth (cat_tuple (val lambda) (val kappa)) i =
      tnth (cat_tuple (val mu) (val kappa)) (sigma i).
    apply/eqP; apply: h; by rewrite mem_enum.
  have hl := Lambda_shared_permutation hp.
  have hs : sigma = 1%g.
    apply/permP=> i; rewrite perm1.
    have hi : injective (tnth (cat_tuple (val lambda) (val kappa))).
      apply/tuple_uniqP; exact: hu.
    apply: hi; have hh := hp i; by rewrite -hl in hh; symmetry.
  by rewrite hl hs !eqxx.
- move/andP=> [/eqP -> /eqP ->]; apply/allP=> i _; by rewrite perm1 eqxx.
Qed.

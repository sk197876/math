(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From mathcomp Require Import all_boot all_order.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Infrastructure for Federer 1.3.4: put the indices of a product into
    increasing order, counting the adjacent interchanges. *)
(** Source for [insert_index]: Federer (1969), 1.3.4, p. 16, basis expansion
    and signed permutation formula. In words: Expanding the images of a
    basis in the top exterior power yields the determinant as the signed sum
    of products of coefficients, indexed by permutations. Definition or
    construction used to formalise this passage. *)
Fixpoint insert_index i s :=
  if s is j :: t then
    if i <= j then i :: s else j :: insert_index i t
  else [:: i].
(** Source for [order_indices]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Definition or construction used to formalise this passage. *)
Fixpoint order_indices s :=
  if s is i :: t then insert_index i (order_indices t) else [::].

(** Source for [insert_index_perm]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma insert_index_perm i s : perm_eq (insert_index i s) (i :: s).
Proof.
elim: s => [|j s ih] /=; first exact: perm_refl.
case: ifP => hij; first exact: perm_refl.
by apply/permP=> P; rewrite /= (permP ih P) /= addnCA.
Qed.
(** Source for [order_indices_perm]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma order_indices_perm s : perm_eq (order_indices s) s.
Proof.
elim: s => [|i s ih] /=; first exact: perm_refl.
apply: perm_trans (insert_index_perm i _) _; by rewrite perm_cons.
Qed.

(** Source for [insert_index_all]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma insert_index_all (P : pred nat) i s :
  all P (insert_index i s) = P i && all P s.
Proof. exact: perm_all (insert_index_perm i s). Qed.

(** Source for [insert_index_sorted]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma insert_index_sorted i s : sorted leq s -> sorted leq (insert_index i s).
Proof.
elim: s => [|j s ih] /=; first by [].
rewrite (path_sortedE leq_trans) => /andP [hjs hs].
case hij: (i <= j).
- change (path leq i (j :: s)).
  rewrite /= hij (path_sortedE leq_trans) hjs hs; by [].
- change (path leq j (insert_index i s)).
  rewrite (path_sortedE leq_trans) (ih hs) insert_index_all hjs !andbT.
  apply: ltnW; by rewrite ltnNge hij.
Qed.
(** Source for [order_indices_sorted]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma order_indices_sorted s : sorted leq (order_indices s).
Proof. elim: s => [|i s ih] //=; exact: insert_index_sorted. Qed.

(** Source for [order_indices_eq]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma order_indices_eq s t : sorted leq t -> perm_eq s t -> order_indices s = t.
Proof.
move=> ht hp; apply: (sorted_eq leq_trans anti_leq (order_indices_sorted s) ht).
exact: perm_trans (order_indices_perm s) hp.
Qed.

(** Source for [sorted_count_smaller_zero]: Federer (1969), 1.3.4, p. 16,
    basis expansion and signed permutation formula. In words: Expanding the
    images of a basis in the top exterior power yields the determinant as
    the signed sum of products of coefficients, indexed by permutations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma sorted_count_smaller_zero i j s : i <= j -> sorted leq (j :: s) ->
  count (fun k => k < i) (j :: s) = 0.
Proof.
move=> hij; rewrite /= (path_sortedE leq_trans) => /andP [hjs hs].
have hz : ~~ has (fun k => k < i) (j :: s).
  apply/hasPn=> k hk.
  have hjk : j <= k.
    move: hk; rewrite in_cons => /orP [/eqP ->|hk]; first exact: leqnn.
    exact: (allP hjs k hk).
  by rewrite ltnNge (leq_trans hij hjk).
move: hz; by rewrite has_count lt0n negbK => /eqP.
Qed.

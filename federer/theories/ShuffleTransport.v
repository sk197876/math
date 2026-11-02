(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order fingroup perm.
From Federer Require Import Shuffles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Infrastructure for Federer 1.3.3. Transport a shuffle along equality
    of its total length. Its natural-number entries remain unchanged. *)
(** Source for [permutation_values_cast]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma permutation_values_cast m n (h : m = n) (s : 'S_m) :
  map val (permutation_sequence (cast_perm h s)) = map val (permutation_sequence s).
Proof. by subst n; rewrite cast_perm_id. Qed.

(** Source for [shuffle_in_cast]: Federer (1969), 1.3.3, p. 15, definition
    of Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma shuffle_in_cast m n p (h : m = n) (s : 'S_m) :
  shuffle_in p (cast_perm h s) = shuffle_in p s.
Proof.
by rewrite /shuffle_in !map_take !map_drop permutation_values_cast.
Qed.

(** Source for [cast_shuffle]: Federer (1969), 1.3.3, p. 15, definition of
    Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Definition or construction used to
    formalise this passage. *)
Definition cast_shuffle m n p (h : m = n) (s : {s : 'S_m | shuffle_in p s}) :
  {s : 'S_n | shuffle_in p s} :=
  Sub (cast_perm h (val s)) (eq_ind_r is_true (valP s) (shuffle_in_cast p h (val s))).

(** Source for [cast_shuffleK]: Federer (1969), 1.3.3, p. 15, definition of
    Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma cast_shuffleK m n p (h : m = n) :
  cancel (@cast_shuffle m n p h) (@cast_shuffle n m p (esym h)).
Proof. by move=> s; apply: val_inj; rewrite /= cast_permK. Qed.
(** Source for [cast_shuffleKV]: Federer (1969), 1.3.3, p. 15, definition of
    Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma cast_shuffleKV m n p (h : m = n) :
  cancel (@cast_shuffle n m p (esym h)) (@cast_shuffle m n p h).
Proof. by move=> s; apply: val_inj; rewrite /= cast_permKV. Qed.

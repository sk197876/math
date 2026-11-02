(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From Stdlib Require Import Lia.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingCoordinates.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(** Federer 1.4.4, infinite-dimensional assertion Positions are zero-based,
    as in the preceding source files. *)
(** Source for [block_tuple]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition block_tuple m j : m.-tuple nat :=
  Tuple (introT eqP (size_iota (m*j) m)).
(** Source for [block_tupleE]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma block_tupleE m j : val (block_tuple m j) = iota (m*j) m.
Proof. by []. Qed.
(** Source for [block_tuple_sorted]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma block_tuple_sorted m j : sorted ltn (block_tuple m j).
Proof. exact: iota_ltn_sorted. Qed.
(** Source for [block_lambda]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition block_lambda m j : Lambda_infty m := Sub (block_tuple m j) (block_tuple_sorted m j).
(** Source for [mixed_block]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition mixed_block m i j := (m.+2*i) :: iota (m.+2*j).+1 m.+1.
(** Source for [mixed_block_size]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma mixed_block_size m i j : size (mixed_block m i j) = m.+2.
Proof. by rewrite /mixed_block /= size_iota. Qed.
(** Source for [mixed_block_diagonal]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma mixed_block_diagonal m j : mixed_block m j j = block_tuple m.+2 j.
Proof. by rewrite /mixed_block block_tupleE /=. Qed.
(** Source for [multiple_in_block]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma multiple_in_block m i k : (m.+2*i) \in block_tuple m.+2 k -> i=k.
Proof.
change ((m.+2*i) \in iota (m.+2*k) m.+2 -> i=k).
rewrite mem_iota => /andP [/leP h1 /ltP h2].
have hm : 0 < m.+2 by [].
move/ltP: hm => hm; rewrite !mulnE !addnE in h1 h2; nia.
Qed.
(** Source for [successor_multiple_in_block]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma successor_multiple_in_block m j k : (m.+2*j).+1 \in block_tuple m.+2 k -> j=k.
Proof.
change ((m.+2*j).+1 \in iota (m.+2*k) m.+2 -> j=k).
rewrite mem_iota => /andP [/leP h1 /ltP h2].
have hm : 1 < m.+2 by [].
move/ltP: hm => hm; rewrite !mulnE !addnE in h1 h2; nia.
Qed.
(** Source for [mixed_block_not_permutation]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Theorem mixed_block_not_permutation m i j : i != j -> forall k,
  ~~ perm_eq (mixed_block m i j) (block_tuple m.+2 k).
Proof.
move=> hij k; apply/negP => hp.
have hm : (m.+2*i) \in block_tuple m.+2 k.
  by rewrite -(perm_mem hp) /mixed_block in_cons eqxx.
have hn : (m.+2*j).+1 \in block_tuple m.+2 k.
  by rewrite -(perm_mem hp) /mixed_block in_cons mem_iota leqnn addnS ltnS leq_addr orbT.
have hi := multiple_in_block hm; have hj := successor_multiple_in_block hn.
by rewrite hi hj eqxx in hij.
Qed.

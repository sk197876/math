(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order fingroup perm.
From Federer Require Import ExteriorIndices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Federer 1.3.3: a shuffle of type (p,q) is a permutation increasing on
    each of the two consecutive blocks. The entries are ordinal indices,
    so index i denotes Federer's i+1. *)
(** Source for [permutation_sequence]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Definition or construction used
    to formalise this passage. *)
Definition permutation_sequence n (s : 'S_n) : n.-tuple 'I_n := [tuple s i | i < n].
(** Source for [shuffle_in]: Federer (1969), 1.3.3, p. 15, definition of
    Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Definition or construction used to
    formalise this passage. *)
Definition shuffle_in n p (s : 'S_n) :=
  sorted ltn (map val (take p (permutation_sequence s))) &&
  sorted ltn (map val (drop p (permutation_sequence s))).
(** Source for [Sh]: Federer (1969), 1.3.3, p. 15, definition of Sh(p,q),
    shuffle expansion, and definition of index. In words: A (p,q)-shuffle is
    increasing in each consecutive block; the diagonal of a product is the
    sum over all shuffles of the two selected products, weighted by
    permutation index. Definition or construction used to formalise this
    passage. *)
Definition Sh p q := {s : 'S_(p+q) | shuffle_in p s}.
HB.instance Definition _ p q := Finite.copy (Sh p q)
  {s : 'S_(p+q) | shuffle_in p s}.

(** Infrastructure for the distributive expansion in Federer 1.3.3:
    selecting the left or right summand in every factor. *)
(** Source for [selection_flip]: Federer (1969), 1.3.3, p. 15, definition of
    Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Definition or construction used to
    formalise this passage. *)
Fixpoint selection_flip n : selection_index n -> selection_index n :=
  match n as k return selection_index k -> selection_index k with
  | 0 => fun _ => tt
  | k.+1 => fun b => (~~ b.1, @selection_flip k b.2)
  end.
Arguments selection_flip n b : clear implicits.
(** Source for [selection_flipK]: Federer (1969), 1.3.3, p. 15, definition
    of Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma selection_flipK n : involutive (selection_flip n).
Proof.
elim: n => [|n ih]; first by case.
by case=> [b t] /=; rewrite negbK ih.
Qed.

(** Source for [selected_flip_mem]: Federer (1969), 1.3.3, p. 15, definition
    of Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma selected_flip_mem n (b : selection_index n) i :
  (i \in selected_indices n (selection_flip n b)) = (i \notin selected_indices n b).
Proof.
elim: n b i => [b i|n ih [b t] i]; first by have h := valP i; rewrite ltn0 in h.
case: (unliftP ord0 i) => [j ->|->].
- by rewrite !selected_mem_lift; exact: ih.
- by rewrite !selected_mem_zero.
Qed.
(** Source for [selected_uniq]: Federer (1969), 1.3.3, p. 15, definition of
    Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma selected_uniq n (b : selection_index n) : uniq (selected_indices n b).
Proof.
have h := @sorted_uniq (Equality.clone nat _) ltn ltn_trans ltnn _ (@selected_sorted n b).
by rewrite (map_inj_uniq val_inj) in h.
Qed.

(** Source for [selection_partition]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Definition or construction used
    to formalise this passage. *)
Definition selection_partition n (b : selection_index n) :=
  selected_indices n b ++ selected_indices n (selection_flip n b).
(** Source for [selection_partition_uniq]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma selection_partition_uniq n (b : selection_index n) : uniq (selection_partition b).
Proof.
rewrite /selection_partition cat_uniq !selected_uniq /= andbT.
apply/hasPn=> i hi; by move: hi; rewrite selected_flip_mem.
Qed.
(** Source for [selection_partition_perm]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma selection_partition_perm n (b : selection_index n) :
  perm_eq (selection_partition b) (enum 'I_n).
Proof.
apply: uniq_perm; [exact: selection_partition_uniq | exact: enum_uniq |].
by move=> i; rewrite /selection_partition mem_cat selected_flip_mem orbN mem_enum.
Qed.
(** Source for [selection_partition_size]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma selection_partition_size n (b : selection_index n) : size (selection_partition b) == n.
Proof. by rewrite (perm_size (selection_partition_perm b)) size_enum_ord. Qed.
(** Source for [selection_partition_tuple]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Definition or construction used
    to formalise this passage. *)
Definition selection_partition_tuple n (b : selection_index n) : n.-tuple 'I_n :=
  Tuple (selection_partition_size b).
(** Source for [selection_partition_injective]: Federer (1969), 1.3.3, p.
    15, definition of Sh(p,q), shuffle expansion, and definition of index.
    In words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma selection_partition_injective n (b : selection_index n) :
  injective (tnth (selection_partition_tuple b)).
Proof. apply/tuple_uniqP; exact: selection_partition_uniq. Qed.
(** Source for [selection_permutation]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Definition or construction used
    to formalise this passage. *)
Definition selection_permutation n (b : selection_index n) : 'S_n :=
  perm (@selection_partition_injective n b).
(** Source for [selection_permutationE]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma selection_permutationE n (b : selection_index n) i :
  selection_permutation b i = tnth (selection_partition_tuple b) i.
Proof. exact: permE. Qed.
(** Source for [selection_permutation_tuple]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma selection_permutation_tuple n (b : selection_index n) :
  permutation_sequence (selection_permutation b) = selection_partition_tuple b.
Proof. by apply: eq_from_tnth => i; rewrite tnth_mktuple selection_permutationE. Qed.
(** Source for [selection_permutation_shuffle]: Federer (1969), 1.3.3, p.
    15, definition of Sh(p,q), shuffle expansion, and definition of index.
    In words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma selection_permutation_shuffle n (b : selection_index n) :
  shuffle_in (size (selected_indices n b)) (selection_permutation b).
Proof.
rewrite /shuffle_in selection_permutation_tuple /= /selection_partition
  (@take_size_cat 'I_n (size (selected_indices n b)) (selected_indices n b)
    (selected_indices n (selection_flip n b)) (erefl _))
  (@drop_size_cat 'I_n (size (selected_indices n b)) (selected_indices n b)
    (selected_indices n (selection_flip n b)) (erefl _)).
by rewrite !selected_sorted.
Qed.

(** Source for [permutation_sequence_uniq]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma permutation_sequence_uniq n (s : 'S_n) : uniq (permutation_sequence s).
Proof.
apply/tuple_uniqP=> i j.
rewrite /permutation_sequence !tnth_mktuple; exact: perm_inj.
Qed.
(** Source for [permutation_sequence_mem]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma permutation_sequence_mem n (s : 'S_n) i : i \in permutation_sequence s.
Proof. apply/tnthP; exists ((s^-1)%g i); by rewrite tnth_mktuple permKV. Qed.
(** Source for [permutation_drop_mem]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma permutation_drop_mem n p (s : 'S_n) i :
  (i \in drop p (permutation_sequence s)) = (i \notin take p (permutation_sequence s)).
Proof.
have hall : (i \in take p (permutation_sequence s)) || (i \in drop p (permutation_sequence s)).
  by rewrite -mem_cat cat_take_drop permutation_sequence_mem.
have hdis : i \in drop p (permutation_sequence s) -> i \notin take p (permutation_sequence s).
  have h : uniq (take p (permutation_sequence s) ++ drop p (permutation_sequence s)).
    by rewrite cat_take_drop; exact: permutation_sequence_uniq.
  rewrite cat_uniq in h.
  have /and3P [_ /hasPn hd _] := h.
  exact: hd.
case ht: (i \in take p (permutation_sequence s)); case hd: (i \in drop p (permutation_sequence s)) => //.
- by have := hdis hd; rewrite ht.
- by move: hall; rewrite ht hd.
Qed.

(** Source for [selected_indices_eq]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma selected_indices_eq n (b : selection_index n) (s : seq 'I_n) :
  sorted ltn (map val s) ->
  (forall i, (i \in selected_indices n b) = (i \in s)) -> selected_indices n b = s.
Proof.
move=> hs hm.
have hb : selection_of n (fun i => i \in s) = b.
  rewrite -(selection_ofK b); apply: selection_of_ext => i; exact: esym (hm i).
by rewrite -hb selected_sequenceK.
Qed.

(** Finite indexing of all shuffles of all possible types for a fixed
    total length n. The first coordinate is the type p; q=n-p. *)
(** Source for [shuffle_index]: Federer (1969), 1.3.3, p. 15, definition of
    Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Definition or construction used to
    formalise this passage. *)
Definition shuffle_index n :=
  {ps : ('I_n.+1 * 'S_n)%type | shuffle_in (val ps.1) ps.2}.
HB.instance Definition _ n := Finite.copy (shuffle_index n)
  {ps : ('I_n.+1 * 'S_n)%type | shuffle_in (val ps.1) ps.2}.
(** Source for [selected_size_index]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma selected_size_index n (b : selection_index n) : size (selected_indices n b) < n.+1.
Proof. by rewrite ltnS; exact: selected_size. Qed.
(** Source for [selection_shuffle]: Federer (1969), 1.3.3, p. 15, definition
    of Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Definition or construction used to
    formalise this passage. *)
Definition selection_shuffle n (b : selection_index n) : shuffle_index n :=
  Sub (Ordinal (selected_size_index b), selection_permutation b) (selection_permutation_shuffle b).
(** Source for [shuffle_selection]: Federer (1969), 1.3.3, p. 15, definition
    of Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Definition or construction used to
    formalise this passage. *)
Definition shuffle_selection n (t : shuffle_index n) : selection_index n :=
  selection_of n (fun i => i \in take (val (val t).1) (permutation_sequence (val t).2)).

(** Source for [shuffle_selection_left]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma shuffle_selection_left n (t : shuffle_index n) :
  selected_indices n (shuffle_selection t) = take (val (val t).1) (permutation_sequence (val t).2).
Proof. apply: selected_sequenceK; exact: (andP (valP t)).1. Qed.
(** Source for [shuffle_selection_right]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma shuffle_selection_right n (t : shuffle_index n) :
  selected_indices n (selection_flip n (shuffle_selection t)) =
  drop (val (val t).1) (permutation_sequence (val t).2).
Proof.
apply: selected_indices_eq; first exact: (andP (valP t)).2.
by move=> i; rewrite selected_flip_mem /shuffle_selection selected_mem_selection_of permutation_drop_mem.
Qed.
(** Source for [shuffle_selection_partition]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma shuffle_selection_partition n (t : shuffle_index n) :
  selection_partition (shuffle_selection t) = permutation_sequence (val t).2.
Proof. by rewrite /selection_partition shuffle_selection_left shuffle_selection_right cat_take_drop. Qed.
(** Source for [shuffle_selection_permutation]: Federer (1969), 1.3.3, p.
    15, definition of Sh(p,q), shuffle expansion, and definition of index.
    In words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma shuffle_selection_permutation n (t : shuffle_index n) :
  selection_permutation (shuffle_selection t) = (val t).2.
Proof.
have ht : selection_partition_tuple (shuffle_selection t) = permutation_sequence (val t).2.
  apply: val_inj; exact: shuffle_selection_partition.
by apply/permP=> i; rewrite selection_permutationE ht tnth_mktuple.
Qed.
(** Source for [selection_shuffleK]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Lemma selection_shuffleK n : cancel (@selection_shuffle n) (@shuffle_selection n).
Proof.
move=> b; change (selection_of n (fun i => i \in take (size (selected_indices n b))
  (permutation_sequence (selection_permutation b))) = b).
rewrite selection_permutation_tuple /= /selection_partition.
rewrite (@take_size_cat 'I_n (size (selected_indices n b)) (selected_indices n b)
  (selected_indices n (selection_flip n b)) (erefl _)).
exact: selection_ofK.
Qed.
(** Source for [shuffle_selectionK]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Lemma shuffle_selectionK n : cancel (@shuffle_selection n) (@selection_shuffle n).
Proof.
move=> t; apply: val_inj.
have hp : (val (selection_shuffle (shuffle_selection t))).1 = (val t).1.
  apply: val_inj; change (size (selected_indices n (shuffle_selection t)) = val (val t).1).
  rewrite shuffle_selection_left size_take_min size_tuple.
  apply: minn_idPl; have h := valP (val t).1; by rewrite ltnS in h.
have hs := @shuffle_selection_permutation n t.
case: t hp hs => [[p s] ht] /= hp hs.
by rewrite hp hs.
Qed.

(** The exponent in Federer's index is the number of inversions. This
    recursive count records, for each entry, the smaller entries to its
    right. It is identified with the pair count before the shuffle theorem. *)
(** Source for [inversions]: Federer (1969), 1.3.3, p. 15, sentence
    immediately after the shuffle formula. In words: The index of a
    permutation is (-1) raised to its number of inversions, namely pairs i<j
    whose images occur in the opposite order. Definition or construction
    used to formalise this passage. *)
Fixpoint inversions (s : seq nat) : nat :=
  if s is i :: t then (count (fun j => j < i) t + inversions t)%N else 0%N.
(** Source for [selection_inversions]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Definition or construction used
    to formalise this passage. *)
Definition selection_inversions n (b : selection_index n) :=
  inversions (map val (selection_partition b)).

(** Source for [inversions_zero]: Federer (1969), 1.3.3, p. 15, sentence
    immediately after the shuffle formula. In words: The index of a
    permutation is (-1) raised to its number of inversions, namely pairs i<j
    whose images occur in the opposite order. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma inversions_zero s : inversions (0 :: s) = inversions s.
Proof.
have h : (fun j => j < 0) =1 pred0 by move=> j; exact: ltn0.
by rewrite /= (eq_count h) count_pred0.
Qed.
(** Source for [inversions_successors]: Federer (1969), 1.3.3, p. 15,
    sentence immediately after the shuffle formula. In words: The index of a
    permutation is (-1) raised to its number of inversions, namely pairs i<j
    whose images occur in the opposite order. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma inversions_successors s : inversions (map succn s) = inversions s.
Proof.
elim: s => [|i s ih] //=; rewrite count_map ih.
congr (_ + _); apply: eq_count => j; by rewrite /= ltnS.
Qed.
(** Source for [inversions_insert_zero]: Federer (1969), 1.3.3, p. 15,
    sentence immediately after the shuffle formula. In words: The index of a
    permutation is (-1) raised to its number of inversions, namely pairs i<j
    whose images occur in the opposite order. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma inversions_insert_zero s t : all (fun i => 0 < i) s ->
  inversions (s ++ 0 :: t) = (size s + inversions (s ++ t))%N.
Proof.
elim: s => [|i s ih] /=; first by move=> _; exact: inversions_zero.
move/andP=> [hi hs]; rewrite !count_cat /= hi (ih hs).
by rewrite !addnS !addSn !addnA [count _ s + count _ t + size s]addnC addnA.
Qed.

(** Source for [selection_inversions_cons]: Federer (1969), 1.3.3, p. 15,
    sentence immediately after the shuffle formula. In words: The index of a
    permutation is (-1) raised to its number of inversions, namely pairs i<j
    whose images occur in the opposite order. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma selection_inversions_cons n (b : bool) (t : selection_index n) :
  @selection_inversions n.+1 (b,t) =
  if b then @selection_inversions n t else (size (selected_indices n t) + @selection_inversions n t)%N.
Proof.
rewrite /selection_inversions /selection_partition !map_cat /= !selected_values.
case: b => /=.
- rewrite -map_cat.
  rewrite (map_comp succn (fun i : 'I_n => val i)).
  change (inversions (0 :: map succn (map val (selected_indices n t ++
    selected_indices n (selection_flip n t)))) =
    inversions (map val (selected_indices n t) ++ map val (selected_indices n (selection_flip n t)))).
  by rewrite inversions_zero inversions_successors map_cat.
- rewrite (map_comp succn (fun i : 'I_n => val i) (selected_indices n t))
    (map_comp succn (fun i : 'I_n => val i) (selected_indices n (selection_flip n t))).
  rewrite inversions_insert_zero; last by apply/allP=> i /mapP [j _ ->]; rewrite ltn0Sn.
  by rewrite size_map size_map -map_cat inversions_successors.
Qed.

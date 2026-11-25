(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import Exterior.
From Federer Require Import PermutationBlocks.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Federer 1.4.2, iteration of shuffles: separate the first block and
    sort its complement. The remaining permutation acts only inside the
    complement. This gives the unique binary decomposition used below. *)
Section FirstBlock.
Variables p q : nat.
Local Notation N := (p+q).
(** Source for [first_selection]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition first_selection (sigma : 'S_N) :=
  selection_of N (fun i => i \in take p (permutation_sequence sigma)).
(** Source for [first_selected]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma first_selected sigma : sorted ltn (map val (take p (permutation_sequence sigma))) ->
  selected_indices N (first_selection sigma) = take p (permutation_sequence sigma).
Proof. exact: selected_sequenceK. Qed.
(** Source for [first_selected_size]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma first_selected_size sigma : sorted ltn (map val (take p (permutation_sequence sigma))) ->
  size (selected_indices N (first_selection sigma)) = p.
Proof.
move=> hs; rewrite (first_selected hs) size_take_min size_tuple.
exact: (minn_idPl (leq_addr q p)).
Qed.
(** Source for [first_shuffleP]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma first_shuffleP sigma : sorted ltn (map val (take p (permutation_sequence sigma))) ->
  shuffle_in p (selection_permutation (first_selection sigma)).
Proof.
move=> hs; have h := selection_permutation_shuffle (first_selection sigma).
by rewrite (first_selected_size hs) in h.
Qed.
(** Source for [first_shuffle]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition first_shuffle sigma hs : Sh p q :=
  Sub (selection_permutation (first_selection sigma)) (first_shuffleP hs).
Arguments first_shuffle sigma hs : clear implicits.
(** Source for [first_shuffle_take]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma first_shuffle_take sigma hs :
  take p (permutation_sequence (val (first_shuffle sigma hs))) = take p (permutation_sequence sigma).
Proof.
change (take p (permutation_sequence (selection_permutation (first_selection sigma))) =
  take p (permutation_sequence sigma)).
rewrite selection_permutation_tuple.
change (take p (selected_indices N (first_selection sigma) ++
  selected_indices N (selection_flip N (first_selection sigma))) = take p (permutation_sequence sigma)).
rewrite take_size_cat; first exact: first_selected hs.
exact: first_selected_size hs.
Qed.
End FirstBlock.

Section RemainingBlock.
Variables p q : nat.
Local Notation N := (p+q).
Variables sigma tau : 'S_N.
Hypothesis hfirst : take p (permutation_sequence tau) = take p (permutation_sequence sigma).
(** Source for [permutation_tail_mem]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma permutation_tail_mem (r : 'S_N) (i : 'I_q) : r (rshift p i) \in drop p (permutation_sequence r).
Proof.
rewrite permutation_drop; apply/mapP; exists i; first exact: mem_enum.
by [].
Qed.
(** Source for [tail_index_bound]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma tail_index_bound (i : 'I_q) :
  index (sigma (rshift p i)) (drop p (permutation_sequence tau)) < q.
Proof.
have hm : sigma (rshift p i) \in drop p (permutation_sequence tau).
  by rewrite permutation_drop_mem hfirst -permutation_drop_mem; exact: permutation_tail_mem.
have hb : index (sigma (rshift p i)) (drop p (permutation_sequence tau)) <
    size (drop p (permutation_sequence tau)) by rewrite index_mem.
by rewrite size_drop size_tuple addKn in hb.
Qed.
(** Source for [tail_reorder_fun]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition tail_reorder_fun (i : 'I_q) : 'I_q := Ordinal (tail_index_bound i).
(** Source for [permutation_tail_nth]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma permutation_tail_nth (r : 'S_N) (i : 'I_q) (d : 'I_N) :
  nth d (drop p (permutation_sequence r)) i = r (rshift p i).
Proof.
rewrite permutation_drop (nth_map i) ?size_enum_ord ?ltn_ord //.
by rewrite nth_ord_enum.
Qed.
(** Source for [tail_reorder_funE]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma tail_reorder_funE i : tau (rshift p (tail_reorder_fun i)) = sigma (rshift p i).
Proof.
have hm : sigma (rshift p i) \in drop p (permutation_sequence tau).
  by rewrite permutation_drop_mem hfirst -permutation_drop_mem; exact: permutation_tail_mem.
rewrite -(permutation_tail_nth tau (tail_reorder_fun i) (sigma (rshift p i))).
exact: nth_index hm.
Qed.
(** Source for [tail_reorder_injective]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma tail_reorder_injective : injective tail_reorder_fun.
Proof.
move=> i j hij; have he := congr1 (fun k : 'I_q => tau (rshift p k)) hij.
rewrite !tail_reorder_funE in he.
exact (@rshift_inj p q i j (perm_inj he)).
Qed.
(** Source for [tail_reorder]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition tail_reorder : 'S_q := perm tail_reorder_injective.
(** Source for [tail_reorderE]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma tail_reorderE i : tau (rshift p (tail_reorder i)) = sigma (rshift p i).
Proof. by rewrite permE tail_reorder_funE. Qed.
(** Source for [prefix_equality]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma prefix_equality i : tau (lshift q i) = sigma (lshift q i).
Proof.
have hpref (r : 'S_N) : nth (sigma (lshift q i)) (take p (permutation_sequence r)) i = r (lshift q i).
  rewrite nth_take ?ltn_ord //.
  exact: (nth_mktuple r (sigma (lshift q i)) (lshift q i)).
have he := congr1 (fun t => nth (sigma (lshift q i)) t i) hfirst.
rewrite !hpref in he.
exact: he.
Qed.
(** Source for [shuffle_decomposition]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Theorem shuffle_decomposition : sigma = (block_perm p tail_reorder * tau)%g.
Proof.
apply/permP=> i; case: (split_ordP i) => [j ->|j ->]; rewrite permM.
- by rewrite block_perm_l prefix_equality.
- by rewrite block_perm_r tail_reorderE.
Qed.
End RemainingBlock.

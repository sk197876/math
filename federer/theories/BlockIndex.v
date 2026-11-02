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
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.2, sign in the iterated shuffle formula. Extending a
    permutation by an initial fixed block preserves its inversion index. *)
(** Source for [inversions_translate]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma inversions_translate p positions :
  inversions (map (addn p) positions) = inversions positions.
Proof.
elim: positions => [|i positions ih] //=; rewrite count_map ih.
congr (_ + _)%N; apply: eq_count => j; by rewrite /= ltn_add2l.
Qed.
(** Source for [inversions_sorted]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma inversions_sorted positions : sorted leq positions -> inversions positions = 0%N.
Proof.
elim: positions => [|i positions ih] //= => hs.
have hc := sorted_count_smaller_zero (leqnn i) hs.
rewrite /= ltnn add0n in hc; rewrite hc add0n.
apply: ih; exact: path_sorted hs.
Qed.
(** Source for [inversions_cat_ordered]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma inversions_cat_ordered left right :
  (forall i j, i \in left -> j \in right -> (i <= j)%N) ->
  inversions (left ++ right) = (inversions left + inversions right)%N.
Proof.
elim: left => [|i left ih] //= => h.
have hc : count (fun j => j < i)%N right = 0%N.
  have he : {in right, (fun j => j < i)%N =1 pred0}.
    move=> j hj; have hij := h i j (mem_head i left) hj.
    by rewrite ltnNge hij.
  by rewrite (eq_in_count he) count_pred0.
rewrite count_cat hc addn0 ih ?addnA //.
move=> j k hj hk; apply: h hk; by rewrite in_cons hj orbT.
Qed.
(** Source for [block_permutation_values]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma block_permutation_values p q (sigma : 'S_q) :
  map val (permutation_sequence (block_perm p sigma)) =
    iota 0 p ++ map (addn p) (map val (permutation_sequence sigma)).
Proof.
rewrite permutation_sequence_cat map_cat.
have hl : map (fun i : 'I_p => block_perm p sigma (lshift q i)) (enum 'I_p) =
    map (@lshift p q) (enum 'I_p).
  apply: eq_map => i; exact: block_perm_l.
have hr : map (fun i : 'I_q => block_perm p sigma (rshift p i)) (enum 'I_q) =
    map (fun i : 'I_q => rshift p (sigma i)) (enum 'I_q).
  apply: eq_map => i; exact: block_perm_r.
rewrite hl hr -(map_comp val (@lshift p q) (enum 'I_p))
  -(map_comp val (fun i : 'I_q => rshift p (sigma i)) (enum 'I_q)).
change (map val (enum 'I_p) ++ map (fun i : 'I_q => p + val (sigma i)) (enum 'I_q) =
  iota 0 p ++ map (addn p) (map val (permutation_sequence sigma))).
rewrite val_enum_ord.
change (iota 0 p ++ map (fun i : 'I_q => p + val (sigma i)) (enum 'I_q) =
  iota 0 p ++ map (addn p) (map val (map sigma (enum 'I_q)))).
by rewrite -(map_comp val sigma (enum 'I_q))
  -(map_comp (addn p) (fun i : 'I_q => val (sigma i)) (enum 'I_q)).
Qed.
(** Source for [block_permutation_inversions]: Federer (1969), 1.4.2, pp.
    18-19, block-degree notation and iterated shuffle formula. In words: For
    an ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma block_permutation_inversions p q (sigma : 'S_q) :
  inversions (map val (permutation_sequence (block_perm p sigma))) =
    inversions (map val (permutation_sequence sigma)).
Proof.
rewrite block_permutation_values inversions_cat_ordered.
- rewrite inversions_translate inversions_sorted ?add0n //.
  exact: iota_sorted.
- move=> i j; rewrite mem_iota add0n => /andP [_ hi] /mapP [k _ ->].
  exact: leq_trans (ltnW hi) (leq_addr k p).
Qed.
(** Source for [block_permutation_index]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma block_permutation_index (K : fieldType) p q (sigma : 'S_q) :
  FedererPermutation.index K (block_perm p sigma) = FedererPermutation.index K sigma.
Proof. by rewrite /FedererPermutation.index block_permutation_inversions. Qed.

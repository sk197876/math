(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import Alternating.
From Federer Require Import AlternatingShuffle PermutationBlocks ShuffleComposition MultipleShuffles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.2: the argument blocks v_(sigma[s(i-1)+1]),...,
    v_(sigma[s(i)]) in the multiple shuffle formula. *)
Section Arguments.
Variable K : fieldType.
Variable V : lmodType K.
(** Source for [permuted_values]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition permuted_values n (t : n.-tuple V) (sigma : 'S_n) :=
  map (tnth t) (permutation_sequence sigma).
(** Source for [permuted_valuesE]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma permuted_valuesE n (t : n.-tuple V) sigma :
  permuted_values t sigma = [seq nth 0 t i | i <- map val (permutation_sequence sigma)].
Proof.
rewrite /permuted_values -(map_comp (nth 0 t) val (permutation_sequence sigma)).
apply: eq_map => i; exact: tnth_nth.
Qed.
(** Source for [permuted_values_size]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma permuted_values_size n (t : n.-tuple V) sigma : size (permuted_values t sigma) = n.
Proof. by rewrite /permuted_values size_map size_tuple. Qed.
(** Source for [shuffle_left_arguments]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma shuffle_left_arguments p q (t : (p+q).-tuple V) sigma :
  val (shuffle_left_tuple t sigma) = take p (permuted_values t sigma).
Proof. by rewrite permuted_valuesE -map_take. Qed.
(** Source for [shuffle_right_arguments]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma shuffle_right_arguments p q (t : (p+q).-tuple V) sigma :
  val (shuffle_right_tuple t sigma) = drop p (permuted_values t sigma).
Proof. by rewrite permuted_valuesE -map_drop. Qed.
(** Source for [shuffle_right_tnth]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma shuffle_right_tnth p q (t : (p+q).-tuple V) sigma (i : 'I_q) :
  tnth (shuffle_right_tuple t sigma) i = tnth t (sigma (rshift p i)).
Proof.
rewrite (tnth_nth 0) shuffle_right_arguments /permuted_values -map_drop permutation_drop.
rewrite -(map_comp (tnth t) (fun j : 'I_q => sigma (rshift p j)) (enum 'I_q)).
by rewrite (nth_map i) ?size_enum_ord ?ltn_ord // nth_ord_enum.
Qed.
(** Source for [shuffle_compose_left_arguments]: Federer (1969), 1.4.2, pp.
    18-19, block-degree notation and iterated shuffle formula. In words: For
    an ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma shuffle_compose_left_arguments p q (t : (p+q).-tuple V) (tau : Sh p q) sigma :
  take p (permuted_values t (shuffle_compose tau sigma)) = val (shuffle_left_tuple t (val tau)).
Proof.
rewrite shuffle_left_arguments /permuted_values
  -(@map_take p 'I_(p+q) V (tnth t) (permutation_sequence (shuffle_compose tau sigma)))
  -(@map_take p 'I_(p+q) V (tnth t) (permutation_sequence (val tau))).
by rewrite shuffle_compose_take.
Qed.
(** Source for [shuffle_compose_right_arguments]: Federer (1969), 1.4.2, pp.
    18-19, block-degree notation and iterated shuffle formula. In words: For
    an ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma shuffle_compose_right_arguments p q (t : (p+q).-tuple V) (tau : Sh p q) sigma :
  drop p (permuted_values t (shuffle_compose tau sigma)) =
    permuted_values (shuffle_right_tuple t (val tau)) sigma.
Proof.
rewrite /permuted_values -map_drop shuffle_compose_drop
  -(map_comp (tnth t) (fun i : 'I_q => val tau (rshift p i)) (permutation_sequence sigma)).
apply: eq_map => i; symmetry; exact: shuffle_right_tnth.
Qed.
(** Source for [block_arguments]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition block_arguments degrees i n (t : n.-tuple V) sigma :=
  take (nth 0%N degrees i) (drop (s degrees i) (permuted_values t sigma)).
(** Source for [block_arguments_head]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma block_arguments_head p degrees (t : (p+sumn degrees).-tuple V) (tau : Sh p (sumn degrees)) sigma :
  block_arguments (p::degrees) 0 t (shuffle_compose tau sigma) = val (shuffle_left_tuple t (val tau)).
Proof. by rewrite /block_arguments /s /= drop0 shuffle_compose_left_arguments. Qed.
(** Source for [block_arguments_tail]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma block_arguments_tail p degrees (t : (p+sumn degrees).-tuple V) (tau : Sh p (sumn degrees)) sigma i :
  block_arguments (p::degrees) i.+1 t (shuffle_compose tau sigma) =
    block_arguments degrees i (shuffle_right_tuple t (val tau)) sigma.
Proof.
rewrite /block_arguments /s /= [(p + sumn (take i degrees))%N]addnC -drop_drop.
by rewrite shuffle_compose_right_arguments.
Qed.
(** Source for [permuted_values_identity]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma permuted_values_identity n (t : n.-tuple V) : permuted_values t 1%g = val t.
Proof.
rewrite /permuted_values /permutation_sequence /=.
have he : (fun i : 'I_n => (1%g : 'S_n) i) =1 idfun by move=> i; rewrite perm1.
by rewrite (eq_map he) map_id map_tnth_enum.
Qed.
(** Source for [block_arguments_size]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Lemma block_arguments_size degrees (i : 'I_(size degrees)) (t : (sumn degrees).-tuple V) sigma :
  size (block_arguments degrees i t sigma) == nth 0%N degrees i.
Proof.
apply/eqP; rewrite /block_arguments /s -nth_reshape.
have hs : (sumn degrees <= size (permuted_values t sigma))%N by rewrite permuted_values_size.
have h := congr1 (fun xs => nth 0%N xs i) (reshapeKl hs).
by rewrite /shape (nth_map [::]) ?size_reshape ?ltn_ord // in h.
Qed.
(** Source for [block_tuple]: Federer (1969), 1.4.2, pp. 18-19, block-degree
    notation and iterated shuffle formula. In words: For an ordered family
    of forms, sum over permutations increasing on each prescribed block,
    multiplying the block evaluations in the original order and weighting by
    permutation index. Definition or construction used to formalise this
    passage. *)
Definition block_tuple degrees (i : 'I_(size degrees)) (t : (sumn degrees).-tuple V) sigma :
  (nth 0%N degrees i).-tuple V := Tuple (block_arguments_size i t sigma).
End Arguments.

(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import Exterior.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for Federer 1.4.2: extend a permutation of the last
    block by the identity on the first block. This is the permutation
    used when the binary shuffle formula is iterated. *)
Section Blocks.
Variables p q : nat.
(** Source for [block_perm_fun]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition block_perm_fun (s : 'S_q) (i : 'I_(p+q)) : 'I_(p+q) :=
  match split i with
  | inl j => lshift q j
  | inr j => rshift p (s j)
  end.
(** Source for [block_perm_fun_l]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma block_perm_fun_l (s : 'S_q) i : block_perm_fun s (lshift q i) = lshift q i.
Proof.
change (match split (unsplit (inl i : 'I_p + 'I_q)) with
  | inl j => lshift q j | inr j => rshift p (s j) end = lshift q i).
by rewrite unsplitK.
Qed.
(** Source for [block_perm_fun_r]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma block_perm_fun_r (s : 'S_q) i : block_perm_fun s (rshift p i) = rshift p (s i).
Proof.
change (match split (unsplit (inr i : 'I_p + 'I_q)) with
  | inl j => lshift q j | inr j => rshift p (s j) end = rshift p (s i)).
by rewrite unsplitK.
Qed.
(** Source for [block_perm_funK]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma block_perm_funK (s : 'S_q) : cancel (block_perm_fun s) (block_perm_fun s^-1%g).
Proof.
move=> i; case: (split_ordP i) => [j ->|j ->].
- by rewrite !block_perm_fun_l.
- by rewrite !block_perm_fun_r permK.
Qed.
(** Source for [block_perm]: Federer (1969), 1.4.2, pp. 18-19, block-degree
    notation and iterated shuffle formula. In words: For an ordered family
    of forms, sum over permutations increasing on each prescribed block,
    multiplying the block evaluations in the original order and weighting by
    permutation index. Definition or construction used to formalise this
    passage. *)
Definition block_perm (s : 'S_q) : 'S_(p+q) := perm (can_inj (block_perm_funK s)).
(** Source for [block_perm_l]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma block_perm_l s i : block_perm s (lshift q i) = lshift q i.
Proof. by rewrite permE block_perm_fun_l. Qed.
(** Source for [block_perm_r]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma block_perm_r s i : block_perm s (rshift p i) = rshift p (s i).
Proof. by rewrite permE block_perm_fun_r. Qed.
(** Source for [block_perm_injective]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma block_perm_injective : injective block_perm.
Proof.
move=> s t h; apply/permP=> i; apply: (@rshift_inj p q).
have hi := congr1 (fun f : 'S_(p+q) => f (rshift p i)) h.
by rewrite !block_perm_r in hi.
Qed.
End Blocks.

Section OrdinalBlocks.
Variables p q : nat.
(** Source for [enum_ord_cat]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma enum_ord_cat : enum 'I_(p+q) =
  map (@lshift p q) (enum 'I_p) ++ map (@rshift p q) (enum 'I_q).
Proof.
apply: (inj_map val_inj); rewrite val_enum_ord map_cat
  -(map_comp val (@lshift p q) (enum 'I_p))
  -(map_comp val (@rshift p q) (enum 'I_q)).
change (iota 0 (p+q) = map val (enum 'I_p) ++ map (fun i : 'I_q => p+i) (enum 'I_q)).
by rewrite val_enum_ord (map_comp (addn p) val) val_enum_ord iotaD add0n -(iotaDl p 0 q) addn0.
Qed.
(** Source for [permutation_sequence_cat]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma permutation_sequence_cat (s : 'S_(p+q)) :
  val (permutation_sequence s) =
    map (fun i : 'I_p => s (lshift q i)) (enum 'I_p) ++
    map (fun i : 'I_q => s (rshift p i)) (enum 'I_q).
Proof.
change (map s (enum 'I_(p+q)) =
  map (fun i : 'I_p => s (lshift q i)) (enum 'I_p) ++
  map (fun i : 'I_q => s (rshift p i)) (enum 'I_q)).
by rewrite enum_ord_cat map_cat
  -(map_comp s (@lshift p q) (enum 'I_p))
  -(map_comp s (@rshift p q) (enum 'I_q)).
Qed.
(** Source for [permutation_take]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma permutation_take p' (s : 'S_(p+q)) : p' = p ->
  take p' (permutation_sequence s) = map (fun i : 'I_p => s (lshift q i)) (enum 'I_p).
Proof.
move=> ->; rewrite permutation_sequence_cat take_size_cat // size_map size_enum_ord.
by [].
Qed.
(** Source for [permutation_drop]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma permutation_drop (s : 'S_(p+q)) :
  drop p (permutation_sequence s) = map (fun i : 'I_q => s (rshift p i)) (enum 'I_q).
Proof. by rewrite permutation_sequence_cat drop_size_cat // size_map size_enum_ord. Qed.
End OrdinalBlocks.

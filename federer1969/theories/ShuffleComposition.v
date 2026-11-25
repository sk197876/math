(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import Exterior.
From Federer Require Import PermutationBlocks MultipleShuffles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Federer 1.4.2, shuffles of several blocks: a binary shuffle acts
    increasingly on the whole remaining block, preserving its internal
    block orders. *)
Section Composition.
Variables p q : nat.
(** Source for [shuffle_compose]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition shuffle_compose (tau : Sh p q) (sigma : 'S_q) : 'S_(p+q) :=
  (block_perm p sigma * val tau)%g.
(** Source for [shuffle_compose_take]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma shuffle_compose_take tau sigma :
  take p (permutation_sequence (shuffle_compose tau sigma)) = take p (permutation_sequence (val tau)).
Proof.
rewrite !permutation_take //; apply: eq_map => i.
by rewrite /shuffle_compose permM block_perm_l.
Qed.
(** Source for [shuffle_compose_drop]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma shuffle_compose_drop tau sigma :
  drop p (permutation_sequence (shuffle_compose tau sigma)) =
    map (fun i : 'I_q => val tau (rshift p i)) (permutation_sequence sigma).
Proof.
rewrite permutation_drop.
change (map (fun i : 'I_q => shuffle_compose tau sigma (rshift p i)) (enum 'I_q) =
  map (fun i : 'I_q => val tau (rshift p i)) (map sigma (enum 'I_q))).
rewrite -(map_comp (fun i : 'I_q => val tau (rshift p i)) sigma (enum 'I_q)).
apply: eq_map => i; by rewrite /shuffle_compose permM block_perm_r.
Qed.
(** Source for [shuffle_tail_mono]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma shuffle_tail_mono (tau : Sh p q) i j :
  (val (val tau (rshift p i)) < val (val tau (rshift p j))) = (i < j).
Proof.
pose r (i : 'I_q) := val (val tau (rshift p i)).
have hs : sorted ltn (map r (enum 'I_q)).
  have h := (andP (valP tau)).2.
  rewrite permutation_drop -(map_comp val (fun i : 'I_q => val tau (rshift p i)) (enum 'I_q)) in h.
  exact: h.
have h_nth (k : 'I_q) : nth 0 (map r (enum 'I_q)) k = r k.
  by rewrite (nth_map k) ?size_enum_ord ?ltn_ord // nth_ord_enum.
have h_lt (k l : 'I_q) : (k < l) -> (r k < r l).
  move=> hkl.
  have hk : k < size (map r (enum 'I_q)) by rewrite size_map size_enum_ord ltn_ord.
  have hl : l < size (map r (enum 'I_q)) by rewrite size_map size_enum_ord ltn_ord.
  have h := sorted_ltn_nth ltn_trans 0 hs k l hk hl hkl.
  by rewrite !h_nth in h.
change ((r i < r j) = (i < j)).
case: (ltngtP i j) => [hij|hji|he].
- exact: h_lt i j hij.
- by rewrite ltnNge (ltnW (h_lt j i hji)).
- have -> : i = j by apply: val_inj.
  exact: ltnn.
Qed.
(** Source for [shuffle_compose_blocks]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma shuffle_compose_blocks degrees tau sigma :
  multiple_shuffle_in (p :: degrees) (shuffle_compose tau sigma) = multiple_shuffle_in degrees sigma.
Proof.
rewrite /multiple_shuffle_in /= -map_take -map_drop shuffle_compose_take shuffle_compose_drop.
have hp := (andP (valP tau)).1; rewrite hp /=.
rewrite -(map_comp val (fun i : 'I_q => val tau (rshift p i)) (permutation_sequence sigma)).
apply: blocks_sorted_map_eq => i j; exact: shuffle_tail_mono.
Qed.
End Composition.

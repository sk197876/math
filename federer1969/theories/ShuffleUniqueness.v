(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import Exterior.
From Federer Require Import PermutationBlocks ShuffleComposition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Federer 1.4.2: uniqueness in the decomposition of a multiple shuffle
    into a first binary shuffle and a shuffle of the remaining blocks. *)
Section Uniqueness.
Variables p q : nat.
(** Source for [shuffle_take_injective]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma shuffle_take_injective (tau upsilon : Sh p q) :
  take p (permutation_sequence (val tau)) = take p (permutation_sequence (val upsilon)) -> tau = upsilon.
Proof.
move=> h.
have htperm : perm_eq (drop p (permutation_sequence (val tau)))
    (drop p (permutation_sequence (val upsilon))).
  apply: uniq_perm.
  - exact: drop_uniq (permutation_sequence_uniq _).
  - exact: drop_uniq (permutation_sequence_uniq _).
  - by move=> i; rewrite !permutation_drop_mem h.
have ht : drop p (permutation_sequence (val tau)) = drop p (permutation_sequence (val upsilon)).
  apply: (inj_map val_inj).
  apply: (irr_sorted_eq ltn_trans ltnn (andP (valP tau)).2 (andP (valP upsilon)).2).
  exact: (perm_mem (perm_map val htperm)).
have hs : permutation_sequence (val tau) = permutation_sequence (val upsilon).
  apply: val_inj.
  exact (eq_trans (esym (cat_take_drop p (permutation_sequence (val tau))))
    (eq_trans (congr2 cat h ht) (cat_take_drop p (permutation_sequence (val upsilon))))).
apply: val_inj; apply/permP=> i.
have he := congr1 (fun t => tnth t i) hs; by rewrite !tnth_mktuple in he.
Qed.
(** Source for [shuffle_compose_injective]: Federer (1969), 1.4.2, pp.
    18-19, block-degree notation and iterated shuffle formula. In words: For
    an ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma shuffle_compose_injective :
  injective (fun t : (Sh p q * 'S_q)%type => shuffle_compose t.1 t.2).
Proof.
move=> [tau sigma] [upsilon rho] he.
have ht : tau = upsilon.
  apply: shuffle_take_injective.
  have h := congr1 (fun r => take p (permutation_sequence r)) he.
  by rewrite !shuffle_compose_take in h.
move: he; rewrite ht => he.
have hs : sigma = rho.
  apply/permP=> i; apply: (@rshift_inj p q); apply: (perm_inj (s:=val upsilon)).
  have h := congr1 (fun r : 'S_(p+q) => r (rshift p i)) he.
  by rewrite /shuffle_compose !permM !block_perm_r in h.
by rewrite hs.
Qed.
End Uniqueness.

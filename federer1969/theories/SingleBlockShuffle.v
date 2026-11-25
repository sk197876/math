(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import Exterior.
From Federer Require Import MultipleShuffles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Federer 1.4.2: a shuffle with one block is the identity. This gives
    the induction base without assuming a unit in the coefficient algebra. *)
(** Source for [increasing_permutation_identity]: Federer (1969), 1.4.2, pp.
    18-19, block-degree notation and iterated shuffle formula. In words: For
    an ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma increasing_permutation_identity n (sigma : 'S_n) :
  sorted ltn (map val (permutation_sequence sigma)) -> sigma = 1%g.
Proof.
move=> hs.
have hval : map val (permutation_sequence sigma) = iota 0 n.
  apply: (irr_sorted_eq ltn_trans ltnn hs (iota_ltn_sorted 0 n)).
  exact: perm_mem (permutation_values_perm sigma).
have hseq : val (permutation_sequence sigma) = enum 'I_n.
  apply: (inj_map val_inj); by rewrite hval val_enum_ord.
apply/permP=> i; rewrite perm1.
have h := congr1 (fun t => nth i t i) hseq.
by rewrite (nth_mktuple sigma i i) nth_ord_enum in h.
Qed.
(** Source for [Sh_multi_single_identity]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma Sh_multi_single_identity p (sigma : Sh_multi [::p]) : val sigma = 1%g.
Proof.
apply: increasing_permutation_identity.
have h := valP sigma; rewrite /multiple_shuffle_in /= andbT in h.
have ht : take p (map val (permutation_sequence (val sigma))) = map val (permutation_sequence (val sigma)).
  apply: take_oversize; by rewrite size_map size_tuple /= addn0.
by rewrite ht in h.
Qed.
(** Source for [identity_multiple_shuffle]: Federer (1969), 1.4.2, pp.
    18-19, block-degree notation and iterated shuffle formula. In words: For
    an ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma identity_multiple_shuffle degrees : multiple_shuffle_in degrees (1%g : 'S_(sumn degrees)).
Proof.
have hs : sorted ltn (map val (permutation_sequence (1%g : 'S_(sumn degrees)))).
  change (sorted ltn (map val (map (fun i : 'I_(sumn degrees) => (1%g : 'S_(sumn degrees)) i) (enum 'I_(sumn degrees))))).
  have he : (fun i : 'I_(sumn degrees) => (1%g : 'S_(sumn degrees)) i) =1 idfun by move=> i; rewrite perm1.
  rewrite (eq_map he) map_id val_enum_ord; exact: iota_ltn_sorted.
rewrite /multiple_shuffle_in.
move: (map val (permutation_sequence (1%g : 'S_(sumn degrees)))) hs => positions hs.
elim: degrees positions hs => [|p degrees ih] positions hs //=.
apply/andP; split; [exact: take_sorted hs | apply: ih; exact: drop_sorted hs].
Qed.
(** Source for [identity_Sh]: Federer (1969), 1.4.2, pp. 18-19, block-degree
    notation and iterated shuffle formula. In words: For an ordered family
    of forms, sum over permutations increasing on each prescribed block,
    multiplying the block evaluations in the original order and weighting by
    permutation index. Definition or construction used to formalise this
    passage. *)
Definition identity_Sh degrees : Sh_multi degrees := Sub 1%g (identity_multiple_shuffle degrees).
(** Source for [Sh_multi_single_unique]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma Sh_multi_single_unique p (sigma : Sh_multi [::p]) : sigma = identity_Sh [::p].
Proof. apply: val_inj; exact: Sh_multi_single_identity. Qed.

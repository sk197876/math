(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import Exterior.
From Federer Require Import PermutationBlocks MultipleShuffles
  ShuffleDecomposition ShuffleComposition ShuffleUniqueness BlockIndex.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.2: the permutations in the iterated formula are enumerated
    exactly once by a binary shuffle followed by a shuffle of the remaining
    blocks. Both inverse equations and the multiplicative index are proved. *)
Section Bijection.
Variable p : nat.
Variable degrees : seq nat.
Local Notation q := (sumn degrees).
(** Source for [compose_multiple]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition compose_multiple (t : (Sh p q * Sh_multi degrees)%type) : Sh_multi (p :: degrees) :=
  Sub (shuffle_compose t.1 (val t.2))
    (eq_ind_r is_true (valP t.2) (shuffle_compose_blocks degrees t.1 (val t.2))).
(** Source for [compose_multipleE]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma compose_multipleE t : val (compose_multiple t) = shuffle_compose t.1 (val t.2).
Proof. by []. Qed.
(** Source for [compose_multiple_injective]: Federer (1969), 1.4.2, pp.
    18-19, block-degree notation and iterated shuffle formula. In words: For
    an ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma compose_multiple_injective : injective compose_multiple.
Proof.
move=> [tau sigma] [upsilon rho] h.
have he := congr1 val h.
have hp : (tau, val sigma) = (upsilon, val rho) :=
  @shuffle_compose_injective p q (tau, val sigma) (upsilon, val rho) he.
have ht := congr1 fst hp; have hs := congr1 snd hp.
congr (_, _); [exact: ht | exact: val_inj hs].
Qed.
(** Source for [decompose_firstP]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma decompose_firstP (sigma : Sh_multi (p :: degrees)) :
  sorted ltn (map val (take p (permutation_sequence (val sigma)))).
Proof.
have h := (andP (valP sigma)).1.
by rewrite map_take.
Qed.
(** Source for [decompose_first]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition decompose_first (sigma : Sh_multi (p :: degrees)) : Sh p q :=
  @first_shuffle p q (val sigma) (decompose_firstP sigma).
(** Source for [decompose_first_take]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma decompose_first_take sigma :
  take p (permutation_sequence (val (decompose_first sigma))) = take p (permutation_sequence (val sigma)).
Proof. exact: first_shuffle_take. Qed.
(** Source for [decompose_rest_perm]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition decompose_rest_perm (sigma : Sh_multi (p :: degrees)) : 'S_q :=
  tail_reorder (decompose_first_take sigma).
(** Source for [decompose_multiple_perm]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma decompose_multiple_perm sigma :
  val sigma = shuffle_compose (decompose_first sigma) (decompose_rest_perm sigma).
Proof. exact: shuffle_decomposition. Qed.
(** Source for [decompose_restP]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma decompose_restP sigma : multiple_shuffle_in degrees (decompose_rest_perm sigma).
Proof.
have h := valP sigma.
rewrite (decompose_multiple_perm sigma) shuffle_compose_blocks in h.
exact: h.
Qed.
(** Source for [decompose_multiple]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition decompose_multiple (sigma : Sh_multi (p :: degrees)) : (Sh p q * Sh_multi degrees)%type :=
  (decompose_first sigma, Sub (decompose_rest_perm sigma) (decompose_restP sigma)).
(** Source for [decompose_multipleK]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma decompose_multipleK : cancel decompose_multiple compose_multiple.
Proof.
move=> sigma; apply: val_inj; exact (esym (decompose_multiple_perm sigma)).
Qed.
(** Source for [compose_multipleK]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma compose_multipleK : cancel compose_multiple decompose_multiple.
Proof.
move=> t; apply: compose_multiple_injective; exact: decompose_multipleK.
Qed.
(** Source for [compose_multiple_bijective]: Federer (1969), 1.4.2, pp.
    18-19, block-degree notation and iterated shuffle formula. In words: For
    an ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma compose_multiple_bijective : bijective compose_multiple.
Proof. exists decompose_multiple; [exact: compose_multipleK | exact: decompose_multipleK]. Qed.
(** Source for [compose_multiple_index]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Lemma compose_multiple_index (K : fieldType) (h2 : (1+1 : K) != 0) t :
  FedererPermutation.index K (val (compose_multiple t)) =
    FedererPermutation.index K (val t.1) * FedererPermutation.index K (val t.2).
Proof.
rewrite compose_multipleE /shuffle_compose (index_multiplicative h2) block_permutation_index.
exact: mulrC.
Qed.
End Bijection.

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

(** Federer 1.4.2: s(i) is the sum of the first i block lengths; a
    shuffle is increasing on every consecutive block. List position i
    corresponds to Federer's i+1, so block i begins at s(i). *)
(** Source for [s]: Federer (1969), 1.4.2, pp. 18-19, block-degree notation
    and iterated shuffle formula. In words: For an ordered family of forms,
    sum over permutations increasing on each prescribed block, multiplying
    the block evaluations in the original order and weighting by permutation
    index. Definition or construction used to formalise this passage. *)
Definition s (degrees : seq nat) i := sumn (take i degrees).
(** Source for [blocks_sorted]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Fixpoint blocks_sorted (degrees : seq nat) (positions : seq nat) : bool :=
  match degrees with
  | [::] => true
  | p :: rest => sorted ltn (take p positions) && blocks_sorted rest (drop p positions)
  end.
(** Source for [blocks_sortedP]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Lemma blocks_sortedP degrees positions : reflect
  (forall i, i < size degrees ->
    sorted ltn (take (nth 0 degrees i) (drop (s degrees i) positions)))
  (blocks_sorted degrees positions).
Proof.
elim: degrees positions => [|p ds ih] positions.
- apply: ReflectT => i; by [].
- apply: (iffP andP).
  + move=> [hp ht] [|i] hi; first by rewrite /s /= drop0.
    have hr := elimT (ih (drop p positions)) ht.
    have hs := hr i hi.
    by move: hs; rewrite /s /= drop_drop addnC.
  + move=> h; split.
    * have h0 := h 0 (ltn0Sn _); by move: h0; rewrite /s /= drop0.
    * apply/(ih (drop p positions))=> i hi; have hs := h i.+1 hi.
      by move: hs; rewrite /s /= drop_drop addnC.
Qed.
(** Source for [multiple_shuffle_in]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition multiple_shuffle_in degrees n (sigma : 'S_n) :=
  blocks_sorted degrees (map val (permutation_sequence sigma)).
(** Source for [Sh_multi]: Federer (1969), 1.4.2, pp. 18-19, block-degree
    notation and iterated shuffle formula. In words: For an ordered family
    of forms, sum over permutations increasing on each prescribed block,
    multiplying the block evaluations in the original order and weighting by
    permutation index. Definition or construction used to formalise this
    passage. *)
Definition Sh_multi degrees := {sigma : 'S_(sumn degrees) | multiple_shuffle_in degrees sigma}.
HB.instance Definition _ degrees := Finite.copy (Sh_multi degrees)
  {sigma : 'S_(sumn degrees) | multiple_shuffle_in degrees sigma}.
(** Source for [Sh_multi_increasing]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Lemma Sh_multi_increasing degrees (sigma : Sh_multi degrees) i : i < size degrees ->
  sorted ltn (take (nth 0 degrees i)
    (drop (s degrees i) (map val (permutation_sequence (val sigma))))).
Proof. exact: (elimT (blocks_sortedP _ _) (valP sigma)). Qed.
(** Source for [multiple_shuffle_two]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma multiple_shuffle_two p q (sigma : 'S_(p+q)) :
  multiple_shuffle_in [::p;q] sigma = shuffle_in p sigma.
Proof.
rewrite /multiple_shuffle_in /shuffle_in /= andbT !map_take !map_drop.
have hs : size (drop p (map val (permutation_sequence sigma))) = q.
  by rewrite size_drop size_map size_tuple addKn.
have ht : take q (drop p (map val (permutation_sequence sigma))) =
    drop p (map val (permutation_sequence sigma)).
  apply: take_oversize; by rewrite hs.
by rewrite ht.
Qed.

(** Source for [blocks_sorted_map_eq]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma blocks_sorted_map_eq (I : Type) (f g : I -> nat)
    (hfg : forall i j, (f i < f j) = (g i < g j)) degrees (positions : seq I) :
  blocks_sorted degrees (map f positions) = blocks_sorted degrees (map g positions).
Proof.
elim: degrees positions => [|p ds ih] positions //=.
rewrite -!map_take -!map_drop ih !sorted_map.
congr (_ && _); apply: eq_sorted => i j; exact: hfg.
Qed.
(** Source for [blocks_sorted_map]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma blocks_sorted_map (f : nat -> nat) (hf : forall i j, (f i < f j) = (i < j)) degrees positions :
  blocks_sorted degrees (map f positions) = blocks_sorted degrees positions.
Proof.
elim: degrees positions => [|p ds ih] positions //=.
rewrite -map_take -map_drop ih sorted_map.
congr (_ && _); apply: eq_sorted => i j; exact: hf.
Qed.

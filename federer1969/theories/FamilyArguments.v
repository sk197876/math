(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import Alternating.
From Federer Require Import AlternatingFamily AlternatingShuffle MultipleShuffles
  PermutationArguments ShuffleComposition SingleBlockShuffle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.2: the ordered list of the m block evaluations in the
    iterated shuffle formula. No commutativity of the coefficients is used. *)
Section FamilyArguments.
Variable K : fieldType.
Variables V W : lmodType K.
(** Source for [family_values]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition family_values degrees (alpha : form_family V W degrees) n
    (t : n.-tuple V) (sigma : 'S_n) : seq W :=
  [seq form_words (alpha i) (block_arguments degrees i t sigma)
    | i <- enum 'I_(size degrees)].
(** Source for [family_values_size]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma family_values_size degrees (alpha : form_family V W degrees) n (t : n.-tuple V) sigma :
  size (family_values alpha t sigma) = size degrees.
Proof. by rewrite /family_values size_map size_enum_ord. Qed.
(** Source for [family_values_nonempty]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma family_values_nonempty degrees (alpha : form_family V W degrees) n (t : n.-tuple V) sigma :
  degrees != [::] -> family_values alpha t sigma != [::].
Proof. by rewrite -!size_eq0 family_values_size. Qed.
(** Source for [family_values_cons]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma family_values_cons p ds (alpha : form_family V W (p::ds))
    (t : (p+sumn ds).-tuple V) (tau : Sh p (sumn ds)) sigma :
  family_values alpha t (shuffle_compose tau sigma) =
    form_family_head alpha (shuffle_left_tuple t (val tau)) ::
    family_values (form_family_tail alpha) (shuffle_right_tuple t (val tau)) sigma.
Proof.
rewrite /family_values enum_ordSl map_cons.
congr (_ :: _).
- rewrite block_arguments_head; exact: form_wordsE.
- rewrite -(map_comp
    (fun i => form_words (alpha i) (block_arguments (p::ds) i t (shuffle_compose tau sigma)))
    (lift ord0) (enum 'I_(size ds))).
  apply: eq_map => i; change (form_words (form_family_tail alpha i)
      (block_arguments (p::ds) i.+1 t (shuffle_compose tau sigma)) =
      form_words (form_family_tail alpha i) (block_arguments ds i (shuffle_right_tuple t (val tau)) sigma)).
  by rewrite block_arguments_tail.
Qed.
(** Source for [family_values_single]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma family_values_single p (alpha : form_family V W [::p]) (t : (sumn [::p]).-tuple V) :
  family_values alpha t 1%g = [:: form_words (form_family_head alpha) t].
Proof.
rewrite /family_values enum_ordSl enum_ord0 /= /block_arguments /s /= drop0 permuted_values_identity.
congr [:: _]; congr (form_words _ _); apply: take_oversize; by rewrite size_tuple /= addn0.
Qed.
(** Source for [family_values_tuples]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma family_values_tuples degrees (alpha : form_family V W degrees)
    (t : (sumn degrees).-tuple V) sigma :
  family_values alpha t sigma = [seq alpha i (block_tuple i t sigma) | i <- enum 'I_(size degrees)].
Proof.
apply: eq_map => i; exact (@form_wordsE K V W (nth 0%N degrees i) (alpha i) (block_tuple i t sigma)).
Qed.
End FamilyArguments.

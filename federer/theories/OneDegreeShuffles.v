(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import Alternating.
From Federer Require Import MultipleShuffles PermutationArguments.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.2, p(i)=1: every permutation is a shuffle, s(i)=i,
    and every block contains precisely the single permuted argument.
    Positions use ordinals starting at zero, corresponding to i+1 in
    the book. The cast below changes only the proof of the bound. *)
(** Source for [one_degrees_sum]: Federer (1969), 1.4.2, p. 19,
    specialisation p(i)=1. In words: The alternating product of one-forms
    evaluates as the sum over all permutations of the signed ordered
    products of the one-form values. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma one_degrees_sum degrees : all (pred1 1%N) degrees -> size degrees = sumn degrees.
Proof. move/all_pred1P=> h; by rewrite {2}h sumn_nseq mul1n. Qed.
(** Source for [one_degrees_nth]: Federer (1969), 1.4.2, p. 19,
    specialisation p(i)=1. In words: The alternating product of one-forms
    evaluates as the sum over all permutations of the signed ordered
    products of the one-form values. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma one_degrees_nth degrees (h : all (pred1 1%N) degrees) (i : 'I_(size degrees)) :
  nth 0%N degrees i = 1%N.
Proof. apply/eqP; exact: (allP h _ (mem_nth 0%N (ltn_ord i))). Qed.
(** Source for [one_degrees_prefix]: Federer (1969), 1.4.2, p. 19,
    specialisation p(i)=1. In words: The alternating product of one-forms
    evaluates as the sum over all permutations of the signed ordered
    products of the one-form values. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma one_degrees_prefix degrees (h : all (pred1 1%N) degrees) i :
  (i <= size degrees)%N -> s degrees i = i.
Proof.
move=> hi; move/all_pred1P: h=> h.
by rewrite /s h take_nseq // sumn_nseq mul1n.
Qed.
(** Source for [one_degrees_blocks]: Federer (1969), 1.4.2, p. 19,
    specialisation p(i)=1. In words: The alternating product of one-forms
    evaluates as the sum over all permutations of the signed ordered
    products of the one-form values. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma one_degrees_blocks degrees : all (pred1 1%N) degrees ->
  forall positions, blocks_sorted degrees positions.
Proof.
elim: degrees => [|p ds ih] //= /andP [/eqP -> hd] positions.
rewrite (ih hd) andbT; by case: positions => [|x xs] //=; rewrite take0.
Qed.
(** Source for [one_degrees_shuffle]: Federer (1969), 1.4.2, p. 19,
    specialisation p(i)=1. In words: The alternating product of one-forms
    evaluates as the sum over all permutations of the signed ordered
    products of the one-form values. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma one_degrees_shuffle degrees (h : all (pred1 1%N) degrees) n (sigma : 'S_n) :
  multiple_shuffle_in degrees sigma.
Proof. exact (@one_degrees_blocks degrees h (map val (permutation_sequence sigma))). Qed.
(** Source for [one_degree_argument]: Federer (1969), 1.4.2, p. 19,
    specialisation p(i)=1. In words: The alternating product of one-forms
    evaluates as the sum over all permutations of the signed ordered
    products of the one-form values. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma one_degree_argument (K : fieldType) (V : lmodType K)
    degrees (h : all (pred1 1%N) degrees) (i : 'I_(size degrees))
    (t : (sumn degrees).-tuple V) sigma :
  block_arguments degrees i t sigma =
    [:: tnth t (sigma (cast_ord (one_degrees_sum h) i))].
Proof.
rewrite /block_arguments (one_degrees_nth h) (one_degrees_prefix h (ltnW (ltn_ord i))).
have hi : (i < size (permuted_values t sigma))%N.
  by rewrite permuted_values_size -(one_degrees_sum h); exact: ltn_ord.
rewrite (drop_nth 0 hi) /= take0 /permuted_values.
congr [:: _].
rewrite -(map_comp (tnth t) sigma (enum 'I_(sumn degrees))).
pose j := cast_ord (one_degrees_sum h) i.
change (nth 0 [tuple tnth t (sigma k) | k < sumn degrees] j = tnth t (sigma j)).
exact: nth_mktuple.
Qed.

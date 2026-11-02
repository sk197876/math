(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingCoordinates.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for Federer 1.4.4: fixing all but the first argument
    of an alternating form gives a linear functional. *)
Section FirstArgument.
Variable K : fieldType.
Variables V W : lmodType K.
Variable m : nat.
Variable phi : A_m V W m.
Variable t : seq V.
(** Source for [first_argument]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition first_argument v : W := form_words phi (v::t).
(** Source for [first_argument_linear]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma first_argument_linear : linear first_argument.
Proof. exact: (form_words_multilinear phi [::] t). Qed.
HB.instance Definition _ := GRing.isLinear.Build K V W *:%R first_argument first_argument_linear.
End FirstArgument.

(** The finite-dimensional obstruction in Federer 1.4.4: there cannot
    be more independent vectors than the dimension of the space. *)
(** Source for [finite_independent_dimension_bound]: Federer (1969), 1.4.4,
    p. 20, infinite-dimensional assertion immediately before the
    parenthesis. In words: In infinite dimension, for every degree m at
    least two there are m-covectors outside the image of Omega. Supporting
    lemma for this passage; not separately stated in the book. *)
Theorem finite_independent_dimension_bound (K : fieldType) (V : vectType K) n
    (e : 'I_n -> V) : finite_independent e -> (n <= dim V)%N.
Proof.
move=> he; pose t : n.-tuple V := [tuple e i | i < n].
have ht (i : 'I_n) : t`_i = e i := nth_mktuple e (0 : V) i.
have hsum (c : 'I_n -> K) : (\sum_i c i *: t`_i) = \sum_i c i *: e i.
  apply: eq_bigr => i _; by rewrite ht.
have hf : free t.
  apply/freeP=> c hc; apply: he; by rewrite -(hsum c).
have hd := dimvS (subvf (<<t>>%VS)).
move/eqP: hf => hf; by rewrite dimvf hf size_tuple in hd.
Qed.

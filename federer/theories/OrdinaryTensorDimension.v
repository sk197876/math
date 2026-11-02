(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import OrdinaryTensorObstruction IndependentDual.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5, opening assertion, with the sufficient dimension
    hypotheses made precise: each space contains two independent
    vectors. These hypotheses allow both finite and infinite dimension. *)
Section DimensionObstruction.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Variables (e : 'I_2 -> V) (d : 'I_2 -> W).
Hypotheses (he : finite_independent e) (hd : finite_independent d).
Local Notation U := (alternating_unital_algebra h2 V (scalar_algebra K)).
Local Notation E := (exterior_algebra W).
Local Notation T := (algebra_tensor U E).
Local Notation G := (tensor_grading_product (A_star_grading V K^o) (exterior_grading W)).
Local Notation a := (independent_dual he ord0).
Local Notation b0 := (independent_dual hd ord0).
Local Notation b1 := (independent_dual hd ord_max).
(** Source for [independent_w00]: Federer (1969), 1.4.5, p. 20, opening
    sentence and its parenthesised exception. In words: The ordinary tensor
    product of two exterior algebras is asserted to be neither commutative
    nor anticommutative apart from the printed exception. Supporting lemma
    for this passage; not separately stated in the book. The
    zero-dimensional examples are local counterexamples to the unrestricted
    printed exception, not examples stated in Federer. *)
Lemma independent_w00 : b0 (d ord0) = 1. Proof. by rewrite independent_dualE eqxx. Qed.
(** Source for [independent_w01]: Federer (1969), 1.4.5, p. 20, opening
    sentence and its parenthesised exception. In words: The ordinary tensor
    product of two exterior algebras is asserted to be neither commutative
    nor anticommutative apart from the printed exception. Supporting lemma
    for this passage; not separately stated in the book. The
    zero-dimensional examples are local counterexamples to the unrestricted
    printed exception, not examples stated in Federer. *)
Lemma independent_w01 : b0 (d ord_max) = 0. Proof. by rewrite independent_dualE. Qed.
(** Source for [independent_w10]: Federer (1969), 1.4.5, p. 20, opening
    sentence and its parenthesised exception. In words: The ordinary tensor
    product of two exterior algebras is asserted to be neither commutative
    nor anticommutative apart from the printed exception. Supporting lemma
    for this passage; not separately stated in the book. The
    zero-dimensional examples are local counterexamples to the unrestricted
    printed exception, not examples stated in Federer. *)
Lemma independent_w10 : b1 (d ord0) = 0. Proof. by rewrite independent_dualE. Qed.
(** Source for [independent_w11]: Federer (1969), 1.4.5, p. 20, opening
    sentence and its parenthesised exception. In words: The ordinary tensor
    product of two exterior algebras is asserted to be neither commutative
    nor anticommutative apart from the printed exception. Supporting lemma
    for this passage; not separately stated in the book. The
    zero-dimensional examples are local counterexamples to the unrestricted
    printed exception, not examples stated in Federer. *)
Lemma independent_w11 : b1 (d ord_max) = 1. Proof. by rewrite independent_dualE eqxx. Qed.
(** Source for [independent_v00]: Federer (1969), 1.4.5, p. 20, opening
    sentence and its parenthesised exception. In words: The ordinary tensor
    product of two exterior algebras is asserted to be neither commutative
    nor anticommutative apart from the printed exception. Supporting lemma
    for this passage; not separately stated in the book. The
    zero-dimensional examples are local counterexamples to the unrestricted
    printed exception, not examples stated in Federer. *)
Lemma independent_v00 : a (e ord0) = 1. Proof. by rewrite independent_dualE eqxx. Qed.
(** Source for [ordinary_tensor_neither]: Federer (1969), 1.4.5, p. 20,
    opening sentence and its parenthesised exception. In words: The ordinary
    tensor product of two exterior algebras is asserted to be neither
    commutative nor anticommutative apart from the printed exception.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. The zero-dimensional examples are local counterexamples
    to the unrestricted printed exception, not examples stated in Federer. *)
Theorem ordinary_tensor_neither :
  (~ commutative (alg_mul T)) /\ (~ graded_anticommutative G (alg_mul T)).
Proof.
split.
- exact (@ordinary_tensor_not_commutative K h2 V W b0 b1 (d ord0) (d ord_max)
    independent_w00 independent_w01 independent_w10 independent_w11).
- exact (@ordinary_tensor_not_anticommutative K h2 V W b0 (d ord0)
    independent_w00 a (e ord0) independent_v00).
Qed.
End DimensionObstruction.

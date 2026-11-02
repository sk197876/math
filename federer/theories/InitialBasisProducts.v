(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import InitialIndices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1: when lambda contains the initial k indices, its
    basis product factors into e_1 wedge ... wedge e_k and the product
    on the complementary index. There is no sign, since every initial
    index precedes every complementary index. *)
Section Product.
Variable K : fieldType.
Variable V : lmodType K.
Variables k n m : nat.
Variable hkn : (k <= n)%N.
Variable e : 'I_n -> V.
Variable lambda : Lambda n m.
Variable hsub : Lambda_set (Lambda_initial hkn) \subset Lambda_set lambda.
Local Notation nu := (InteriorComplements.nu hsub).
(** Source for [initial_basis_product]: Federer (1969), 1.6.1, p. 23, last
    paragraph, basis extension and the Grassmann-coordinate argument. In
    words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem initial_basis_product :
  component_val (e_lambda e (val lambda)) =
    wedge (component_val (e_lambda e (val (Lambda_initial hkn))))
      (component_val (e_lambda e (val nu))).
Proof.
have hs : sorted leq (map val (val lambda)).
  have := valP lambda; by rewrite ltn_sorted_uniq_leq => /andP [].
have hp := nu_permutation hsub.
have h := @exterior_index_word_order K V n e
  (val (Lambda_initial hkn) ++ val nu) (val lambda) hs hp.
rewrite (initial_concatenation_inversions hsub) expr0 scale1r in h.
rewrite !e_lambdaE exterior_word_cat -map_cat; exact: esym h.
Qed.
End Product.

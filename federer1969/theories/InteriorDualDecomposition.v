(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDuality.
From Federer Require Import LeftCovectorContraction InteriorOneDegree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.3, final display. The two terms are (v wedge xi)
    left-interior alpha and v wedge (xi left-interior alpha), with the
    degree identifications from InteriorOneDegree. No finite basis is used. *)
Section DualDecomposition.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable v : V.
Variable alpha : A_m V K^o 1.
Hypothesis hv : one_hom alpha v = 1.
(** Source for [dual_interior_decomposition]: Federer (1969), 1.5.3, p. 23,
    final displayed dual equation. In words: A multivector splits as the
    contraction of v wedge xi by alpha plus v wedged with the contraction of
    xi by alpha. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem dual_interior_decomposition n (xi : exterior_power V n.+1) :
  xi = left_alpha h2 alpha (v_wedge v xi) + v_wedge v (left_alpha h2 alpha xi).
Proof.
apply: val_inj; change
  (component_val xi = component_val (left_alpha h2 alpha (v_wedge v xi) +
    v_wedge v (left_alpha h2 alpha xi))).
rewrite (linearD (@component_val K (exterior_space V) (exterior_grading V) n.+1)).
change (component_val xi = component_val (left_alpha h2 alpha (v_wedge v xi)) +
  component_val (v_wedge v (left_alpha h2 alpha xi))).
rewrite !left_alphaE !v_wedgeE ?left_alphaE.
have h := @left_covector_product K h2 V alpha v (component_val xi).
rewrite hv scale1r in h.
by rewrite h subrK.
Qed.
End DualDecomposition.

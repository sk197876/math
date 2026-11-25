(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear GradedAlgebra GradedSums GradedTensor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** A two-sided unit in a nonnegatively graded algebra has degree zero.
    Neither associativity nor a characteristic assumption is needed. *)
Section UnitDegree.
Variable K : fieldType.
Variable V : lmodType K.
Variable G : grading V.
Variable mu : V -> V -> V.
Hypotheses (hb : bilinear mu) (hm : graded_product G mu).
Variable u : V.
Hypotheses (hul : left_id u mu) (hur : right_id u mu).
(** Source for [unit_mul_right]: Federer (1969), 1.2.1, p. 11, unit
    discussion after the definition of a graded algebra. In words: The book
    discusses a unit in degree zero; the more general fact that every unit
    of a nonnegatively graded algebra has degree zero is made explicit.
    Definition or construction used to formalise this passage. *)
Definition unit_mul_right x y := mu y x.
HB.instance Definition _ x := GRing.isLinear.Build K V V *:%R
  (unit_mul_right x) (proj1 hb x).
(** Source for [unit_zero_part]: Federer (1969), 1.2.1, p. 11, unit
    discussion after the definition of a graded algebra. In words: The book
    discusses a unit in degree zero; the more general fact that every unit
    of a nonnegatively graded algebra has degree zero is made explicit.
    Consequence of the definition, made explicit in the cited. *)
Lemma unit_zero_part n x : homogeneous G n x -> mu (grade G 0 u) x = x.
Proof.
move=> hx; have [N hN] := grade_finite G u.
have he := projection_reconstruct_widen (@grade_orthogonal K V G) hN (leqnSn N).
have e := congr1 (grade G n) (hul x).
change (grade G n (unit_mul_right x u) = grade G n x) in e.
rewrite he linear_sum linear_sum /= hx in e.
have hi i : grade G n (mu (grade G i u) x) =
  if i == 0%N then mu (grade G i u) x else 0.
  rewrite (grade_homogeneous _ (hm (homogeneous_grade G i u) hx)).
  by rewrite -{1}[n]add0n eqn_add2r eq_sym.
move: e; under eq_bigr do rewrite hi.
rewrite -big_mkcond (big_pred1 (Ordinal (ltn0Sn N))); last by [].
by [].
Qed.
(** Source for [graded_unit_degree_zero]: Federer (1969), 1.2.1, p. 11, unit
    discussion after the definition of a graded algebra. In words: The book
    discusses a unit in degree zero; the more general fact that every unit
    of a nonnegatively graded algebra has degree zero is made explicit.
    Consequence of the definition, made explicit in the cited. *)
Theorem graded_unit_degree_zero : homogeneous G 0 u.
Proof.
have he x : mu (grade G 0 u) x = x.
  elim/(graded_induction (G:=G)): x => [|x y hx hy|n x hx].
  - exact: bil0r hb _.
  - by rewrite (bilDr hb) hx hy.
  exact: unit_zero_part hx.
by rewrite /homogeneous -(hur (grade G 0 u)) he.
Qed.
End UnitDegree.

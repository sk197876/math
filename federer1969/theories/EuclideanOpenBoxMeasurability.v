(** Federer (1969), 3.2.41, printed p. 277: the actual open
    coordinate boxes are Lebesgue measurable, before finite additivity
    is applied to their disjoint unions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  MeasureUP EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanOpenCoordinateBoxUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_coordinate_box_measurable]: supporting actual
    measurable boxes in the first two proof paragraphs of Federer
    3.2.41, p. 277, using the established coordinate product law
    of 2.7.16, pp. 134--136. *)
Lemma open_coordinate_box_measurable (R:realType) n (a b:R_n R n)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_euclidean_open_coordinate_box a b A ->
  measure_measurable (@euclidean_lebesgue_measure R n) A.
Proof.
move=> hA.
have hEq:A=euclidean_coordinate_box (fun i=>`]a i,b i[).
  apply/seteqP; split=> x hx.
  - move=> i; have hi:=(hA.2 x).1 hx i.
    by rewrite /euclidean_coordinate_box /= in_itv.
  - apply:(hA.2 x).2=> i; have hi:=hx i.
    by move:hi; rewrite /= in_itv.
rewrite hEq.
exact:(@euclidean_coordinate_box_measure R n (fun i=>`]a i,b i[)
  (fun i=>lebesgue_scalar_open_interval_measurable (a i) (b i))).1.
Qed.

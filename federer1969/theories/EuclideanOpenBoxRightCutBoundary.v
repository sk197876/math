(** Federer (1969), 3.2.41, printed p. 277: actual right
    cuts outside an original proper box either preserve or
    delete that member. No chosen endpoint is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanOpenCoordinateBoxUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_box_right_cut_whole]: supporting unchanged
    members of G_2,H_2 in Federer 3.2.41, p. 277. *)
Lemma open_box_right_cut_whole (R:realType) n (a b:R_n R n)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (k:'I_n) (t:R):
  is_euclidean_open_coordinate_box a b A ->t<=a k ->
  A `&` [set x|t<x k]=A.
Proof.
move=> hA hta; apply/seteqP; split=> x hx; first exact hx.1.
split=>//; have /andP[hLow _]:=(hA.2 x).1 hx k.
exact:le_lt_trans hta hLow.
Qed.

(** Source for [open_box_right_cut_empty]: supporting deletion of
    empty members of G_2,H_2 in Federer 3.2.41, p. 277. *)
Lemma open_box_right_cut_empty (R:realType) n (a b:R_n R n)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (k:'I_n) (t:R):
  is_euclidean_open_coordinate_box a b A ->b k<=t ->
  A `&` [set x|t<x k]=set0.
Proof.
move=> hA hbt; apply/seteqP; split; last by move=> x [].
move=> x [hx hCut]; have /andP[_ hHigh]:=(hA.2 x).1 hx k.
exfalso; have hBad:=lt_le_trans (lt_trans hCut hHigh) hbt; by rewrite ltxx in hBad.
Qed.

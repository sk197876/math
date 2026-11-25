(** Federer (1969), 3.2.41, printed p. 277, first proof paragraph
    and display: box volumes are the products of their interval
    lengths. These consequences use the existing actual Euclidean
    Lebesgue measure and box formula of 2.7.16, pp. 134--136. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanOpenCoordinateBoxUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_coordinate_box_nonempty]: supporting actual
    nonemptiness of each box in Federer 3.2.41, p. 277. The
    midpoint lies in every proper interval; dimension zero retains
    its positive empty-product atom. *)
Lemma open_coordinate_box_nonempty (R : realType) n (a b : R_n R n)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_euclidean_open_coordinate_box a b A -> A !=set0.
Proof.
move=> hA; exists ([ffun i => (a i+b i)/2] : R_n R n).
apply: (hA.2 _).2=> i; rewrite ffunE.
have hi := hA.1 i.
have he : (a i+b i)/2+(a i+b i)/2=a i+b i by field.
apply/andP; split; lra.
Qed.

(** Source for [open_coordinate_box_volume]: supporting exact
    actual box volume in Federer 3.2.41, p. 277, using the
    proved 2.7.16 rectangular-product normalization. No measure
    or measurability premise on the original box is added. *)
Lemma open_coordinate_box_volume (R : realType) n (a b : R_n R n)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_euclidean_open_coordinate_box a b A ->
  @euclidean_lebesgue_measure R n A=(\prod_i (b i-a i))%:E.
Proof.
move=> hA.
have he : A=[set x : inner_metric_space (@euclidean_inner_productP R n) |
    forall i, a i<x i<b i].
  apply/seteqP; split=> x; [exact: (hA.2 x).1 | exact: (hA.2 x).2].
rewrite he.
exact: (@euclidean_open_box R n a b (fun i => ltW (hA.1 i))).
Qed.

(** Source for [open_coordinate_box_positive_finite_volume]: supporting
    legal normalization by the box volumes in Federer 3.2.41,
    p. 277. Positivity and finiteness are derived, including the
    positive zero-dimensional atom of the supporting box laws. *)
Lemma open_coordinate_box_positive_finite_volume (R : realType) n (a b : R_n R n)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_euclidean_open_coordinate_box a b A ->
  (0<@euclidean_lebesgue_measure R n A < +oo)%E.
Proof.
move=> hA; rewrite (open_coordinate_box_volume hA) lte_fin ltry andbT.
apply: prodr_gt0=> i _; by rewrite subr_gt0; exact: hA.1.
Qed.

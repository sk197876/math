(** Federer (1969), 2.7.16, printed p. 136, and 2.10.38, pp. 198–199: derive
    elementary rectangular-box properties from the public specification. In
    particular its actual Lebesgue volume is the product of the specified
    widths. Zero widths and ambient dimension zero are retained. Source
    context: EuclideanBoxUP.v and EuclideanRectangularBox.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerMetric EuclideanBoxUP EuclideanRectangularBox EuclideanLebesgue
  EuclideanLebesgueDimensions Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_box_contains_origin]: supporting
    nonempty rectangular boxes for 2.10.38, p. 198,
    derived from the defining inequalities in 2.7.16,
    p. 136. Degenerate boxes still contain their origin. *)
Lemma euclidean_box_contains_origin (R : realType) n origin e c Q :
  @is_euclidean_rectangular_box R n origin e c Q -> Q origin.
Proof.
move=> hQ; apply: (proj2 (euclidean_box_carrier_law hQ origin))=> i.
rewrite subrr (bil0l (@euclidean_inner_bilinear R n)) lexx /=.
exact (@euclidean_box_width_nonnegative_law R n origin e c Q hQ i).
Qed.

(** Source for [euclidean_box_volume]: direct box-volume
    statement of 2.7.16, p. 136, through the
    abstract box specification used in 2.10.38,
    pp. 198–199. The measure is the actual
    sealed Euclidean Lebesgue measure, including dimension zero. *)
Theorem euclidean_box_volume (R : realType) n origin e c Q :
  @is_euclidean_rectangular_box R n origin e c Q ->
  @euclidean_lebesgue_measure R n Q=(\prod_(i<n) c i)%:E.
Proof.
move=> hQ.
have he : Q=[set x : inner_metric_space (@euclidean_inner_productP R n) |
    forall i, 0<=euclidean_inner_product (x-origin) (e i)<=c i].
  apply/seteqP; split=> x hx.
  - exact: (proj1 (euclidean_box_carrier_law hQ x)) hx.
  - exact: (proj2 (euclidean_box_carrier_law hQ x)) hx.
rewrite he; exact: euclidean_rectangular_box
  (euclidean_box_width_nonnegative_law hQ) (euclidean_box_orthonormal_law hQ).
Qed.

(** Source for [euclidean_box_dimension_zero]: supporting
    empty-coordinate convention for 2.10.38, pp. 198–199.
    A zero-dimensional rectangular box contains the entire
    zero-dimensional space; no positive side is introduced. *)
Lemma euclidean_box_dimension_zero (R : realType) origin e c Q :
  @is_euclidean_rectangular_box R 0 origin e c Q -> Q=setT.
Proof.
move=> hQ; apply/seteqP; split=> x // _.
apply: (proj2 (euclidean_box_carrier_law hQ x))=> i.
by have := ltn_ord i; rewrite ltn0.
Qed.

(** Federer (1969), 2.7.16, printed p. 136, specifies a rectangular box by
    inequalities along an orthonormal basis; 2.10.38, pp. 198–199, uses such
    a box to enclose a compact set. Specify the carrier by these laws before
    choosing its origin or constructing a witness. Zero widths and the
    zero-dimensional box are allowed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerMetric OrthonormalFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_euclidean_rectangular_box]: direct abstract
    specification of the rectangular box described in
    2.7.16, p. 136, used by 2.10.38,
    pp. 198–199. This predicate expresses proved laws;
    it introduces no unproved object or global axiom. *)
Record is_euclidean_rectangular_box (R : realType) n (origin : R_n R n)
    (axis : 'I_n -> R_n R n) (width : 'I_n -> R)
    (Q : set (inner_metric_space (@euclidean_inner_productP R n))) : Prop := {
  (** Source for [euclidean_box_orthonormal_law]: direct
      orthonormal axes of the box in 2.7.16,
      p. 136, used in 2.10.38, p. 198. *)
  euclidean_box_orthonormal_law : orthonormal_family (@euclidean_inner_product R n) axis;
  (** Source for [euclidean_box_width_nonnegative_law]: direct
      nonnegative side lengths of the rectangular box
      in 2.7.16, p. 136, including degenerate
      boxes needed for 2.10.38, pp. 198–199. *)
  euclidean_box_width_nonnegative_law : forall i, 0<=width i;
  (** Source for [euclidean_box_carrier_law]: direct
      coordinate inequalities defining the rectangular box
      in 2.7.16, p. 136, used by the
      construction in 2.10.38, p. 199. *)
  euclidean_box_carrier_law : forall x, Q x <-> forall i,
    0<=euclidean_inner_product (x-origin) (axis i)<=width i
}.

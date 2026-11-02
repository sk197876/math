(** Federer (1969), 2.10.46, p. 203: use Fubini along the fibres of an
    orthogonal projection p onto R^k. Specify orthogonal coordinates
    identifying p with the last coordinate block before constructing such
    coordinates. Only inverse, orthogonality and projection equations are
    required; volume estimates and Fubini conclusions are derived
    separately. This supports the displayed projection-volume bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct OrthogonalMaps EuclideanRightBlockProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_orthogonal_projection_chart]: supporting
    orthogonal-coordinate specification for the Fubini step
    in 2.10.46, p. 203, using 1.7.4,
    pp. 30–31. The maps act on R^(m+k),
    and the last k coordinates are the supplied projection. *)
Record is_orthogonal_projection_chart (R : realType) m k
    (p : {linear R_n R (m+k) -> R_n R k})
    (f g : {linear R_n R (m+k) -> R_n R (m+k)}) : Prop := {
  (** Source for [projection_chart_forward_inverse_law]: supporting
      inverse-coordinate identity for 2.10.46, p. 203. *)
  projection_chart_forward_inverse_law : cancel f g;
  (** Source for [projection_chart_backward_inverse_law]: supporting
      inverse-coordinate identity for 2.10.46, p. 203. *)
  projection_chart_backward_inverse_law : cancel g f;
  (** Source for [projection_chart_orthogonal_law]: supporting
      preservation of Euclidean inner products in the
      coordinate change for 2.10.46, p. 203. *)
  projection_chart_orthogonal_law : is_orthogonal_map
    (@euclidean_inner_product R (m+k)) (@euclidean_inner_product R (m+k)) f;
  (** Source for [projection_chart_coordinate_law]: supporting
      identification of projection fibres with coordinate
      slices in the Fubini step of 2.10.46, p. 203. *)
  projection_chart_coordinate_law : forall x, @euclidean_right_block R m k (f x)=p x
}.

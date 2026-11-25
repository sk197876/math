(** Orthogonal normal charts supporting the volume assertion of Federer
    (1969), 2.10.30, p. 195. Specify inverse linear maps preserving the
    inner product and sending the specified coordinate vector to the given
    unit normal. Existence is proved separately from the project's
    orthogonal-frame and transitivity theorems. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct OrthogonalMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_normal_chart_data]: supporting
    pair of linear coordinate maps for the arbitrary
    direction in 2.10.30, p. 195. Their
    properties are specified separately. *)
Record euclidean_normal_chart_data (R : realType) (n : nat) := {
  (** Source for [normal_chart_forward_map]: supporting
      orthogonal map taking the specified axis to the
      normal in 2.10.30, p. 195. *)
  normal_chart_forward_map : {linear R_n R n -> R_n R n};
  (** Source for [normal_chart_backward_map]: supporting
      inverse normal-coordinate map for 2.10.30,
      p. 195. *)
  normal_chart_backward_map : {linear R_n R n -> R_n R n}
}.

(** Source for [is_euclidean_normal_chart]: supporting
    abstract orthogonal-chart laws for 2.10.30,
    p. 195. Whole-space measure preservation is
    derived later from the proved orthogonality laws. *)
Record is_euclidean_normal_chart (R : realType) (n : nat) (j : 'I_n) (u : R_n R n)
    (D : euclidean_normal_chart_data R n) : Prop := {
  (** Source for [normal_chart_orthogonal_law]: supporting
      orthogonal normal chart for the general-direction
      operation of 2.10.30, p. 195. *)
  normal_chart_orthogonal_law : is_orthogonal_map (@euclidean_inner_product R n)
    (@euclidean_inner_product R n) (normal_chart_forward_map D);
  (** Source for [normal_chart_forward_inverse_law]: supporting
      inverse coordinate identity for 2.10.30, p. 195. *)
  normal_chart_forward_inverse_law : cancel (normal_chart_forward_map D) (normal_chart_backward_map D);
  (** Source for [normal_chart_backward_inverse_law]: supporting
      reverse coordinate identity for 2.10.30, p. 195. *)
  normal_chart_backward_inverse_law : cancel (normal_chart_backward_map D) (normal_chart_forward_map D);
  (** Source for [normal_chart_axis_law]: supporting choice of the normal
    direction in 2.10.30, p. 195 *)
  normal_chart_axis_law : normal_chart_forward_map D (@coordinate_basis R n j)=u
}.

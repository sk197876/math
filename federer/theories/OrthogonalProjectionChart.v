(** Public adapted orthogonal coordinates for the Fubini argument of Federer
    (1969), 2.10.46, p. 203. Downstream arguments use only the proved
    abstract chart laws. Source context: EuclideanRightBlockProjection.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations CoordinateProjection
  OrthogonalProjectionChartUP OrthogonalProjectionChartSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [orthogonal_projection_chart]: abstract coordinates
    adapted to p in the Fubini step of 2.10.46, p. 203. *)
Definition orthogonal_projection_chart (R : realType) m k
  (p : {linear R_n R (m+k) -> R_n R k}) (hp : O_star p) :=
  @OrthogonalProjectionChart.value R m k p hp.

(** Source for [orthogonal_projection_chart_specification]: proved
    specification of the coordinate change supporting 2.10.46, p. 203. *)
Theorem orthogonal_projection_chart_specification (R : realType) m k
  (p : {linear R_n R (m+k) -> R_n R k}) (hp : O_star p) :
  is_orthogonal_projection_chart p
    (@orthogonal_projection_chart R m k p hp).1
    (@orthogonal_projection_chart R m k p hp).2.
Proof. exact: OrthogonalProjectionChart.laws. Qed.

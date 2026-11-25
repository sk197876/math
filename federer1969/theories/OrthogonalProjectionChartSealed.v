(** Opaque coordinates adapted to an orthogonal projection, supporting
    Federer (1969), 2.10.46, p. 203. The implementation proves the abstract
    inverse, orthogonality and projection laws. Source context:
    EuclideanRightBlockProjection.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations CoordinateProjection
  OrthogonalProjectionChartUP OrthogonalProjectionChartConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type ORTHOGONAL_PROJECTION_CHART.
(** Source for [value]: abstract adapted coordinate maps for the
    Fubini estimate in 2.10.46, p. 203. *)
Parameter value : forall (R : realType) m k
  (p : {linear R_n R (m+k) -> R_n R k}), O_star p ->
  ({linear R_n R (m+k) -> R_n R (m+k)} *
   {linear R_n R (m+k) -> R_n R (m+k)})%type.
(** Source for [laws]: abstract coordinate laws supporting
    2.10.46, p. 203; no volume conclusion is postulated. *)
Parameter laws : forall (R : realType) m k
  (p : {linear R_n R (m+k) -> R_n R k}) (hp : O_star p),
  is_orthogonal_projection_chart p (@value R m k p hp).1 (@value R m k p hp).2.
End ORTHOGONAL_PROJECTION_CHART.
Module OrthogonalProjectionChart : ORTHOGONAL_PROJECTION_CHART.
(** Source for [value]: privately proved orthogonal coordinate
    witness for 2.10.46, p. 203, hidden by opaque ascription. *)
Definition value (R : realType) m k
  (p : {linear R_n R (m+k) -> R_n R k}) (hp : O_star p) :=
  projT1 (cid (@orthogonal_projection_chart_exists R m k p hp)).
(** Source for [laws]: proved inverse, orthogonality and projection
    laws for the coordinates used in 2.10.46, p. 203. *)
Lemma laws (R : realType) m k
  (p : {linear R_n R (m+k) -> R_n R k}) (hp : O_star p) :
  is_orthogonal_projection_chart p (@value R m k p hp).1 (@value R m k p hp).2.
Proof. exact: (projT2 (cid (@orthogonal_projection_chart_exists R m k p hp))). Qed.
End OrthogonalProjectionChart.

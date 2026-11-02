(** Public cube families supporting Federer (1969), 2.10.47, p. 204. No
    private implementation is imported; geometry uses only the opaque
    coordinate law. Source context: DyadicCubeGridUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  DyadicCubeGridUP DyadicCubeGridSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [dyadic_cube_grid]: abstract level-j cube
    carriers for 2.10.47, p. 204. *)
Definition dyadic_cube_grid (R : realType) n (a : R_n R n) := @DyadicCubeGrid.value R n a.

(** Source for [dyadic_cube_grid_specification]: public
    coordinate law for the cubes of 2.10.47, p. 204. *)
Lemma dyadic_cube_grid_specification (R : realType) n (a : R_n R n) :
  is_dyadic_cube_grid a (@dyadic_cube_grid R n a).
Proof. exact: DyadicCubeGrid.laws. Qed.

(** Source for [dyadic_cube_level]: H_j as the finite
    family of level-j cubes in 2.10.47, p. 204. *)
Definition dyadic_cube_level (R : realType) n
    (Q : forall j, dyadic_cube_indices n j -> set (inner_metric_space (@euclidean_inner_productP R n))) j :=
  Q j @` setT.

(** Source for [dyadic_cube_level_finite]: finiteness of
    each H_j in 2.10.47, p. 204, used for
    the finite union of the chosen compact D_S on p. 205. *)
Lemma dyadic_cube_level_finite (R : realType) n
    (Q : forall j, dyadic_cube_indices n j -> set (inner_metric_space (@euclidean_inner_productP R n))) j :
  finite_set (dyadic_cube_level Q j).
Proof. exact: finite_image _ finite_finset. Qed.

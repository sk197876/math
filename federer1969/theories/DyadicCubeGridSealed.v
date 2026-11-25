(** Opaque grid selection supporting Federer (1969), 2.10.47, p. 204. Only
    the carriers and their abstract coordinate law are exposed. Source
    context: DyadicCubeGridUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  DyadicCubeGridUP DyadicCubeGridConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type DYADIC_CUBE_GRID.
  (** Source for [value]: abstract cube family of
      2.10.47, p. 204. *)
  Parameter value : forall (R : realType) n, R_n R n -> forall j,
    dyadic_cube_indices n j -> set (inner_metric_space (@euclidean_inner_productP R n)).
  (** Source for [laws]: defining cube-coordinate law
      from 2.10.47, p. 204. *)
  Parameter laws : forall (R : realType) n (a : R_n R n),
    is_dyadic_cube_grid a (@value R n a).
End DYADIC_CUBE_GRID.
Module DyadicCubeGrid : DYADIC_CUBE_GRID.
(** Source for [value]: proved grid witness hidden for
    the construction of 2.10.47, p. 204. *)
Definition value (R : realType) n (a : R_n R n) :=
  projT1 (cid (@dyadic_cube_grid_exists R n a)).
(** Source for [laws]: witness satisfies the abstract
    law for 2.10.47, p. 204. *)
Lemma laws (R : realType) n (a : R_n R n) :
  is_dyadic_cube_grid a (@value R n a).
Proof. exact: projT2 (cid (@dyadic_cube_grid_exists R n a)). Qed.
End DyadicCubeGrid.

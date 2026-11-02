(** Opaque grid centres supporting Federer (1969), 2.10.39, printed p. 199.
    Expose only the coordinate laws and the finite index domain. Source
    context: RectangularGridUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  OrthonormalFamilies RectangularGridUP RectangularGridConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type RECTANGULAR_GRID.
(** Source for [value]: abstract centres of the
    subdivided boxes in 2.10.39, p. 199. *)
Parameter value : forall (R : realType) n (origin : R_n R n)
  (axis : 'I_n -> R_n R n) (count : 'I_n -> nat) (node : 'I_n -> nat -> R),
  orthonormal_family (@euclidean_inner_product R n) axis ->
  rectangular_grid_indices count -> R_n R n.
(** Source for [laws]: abstract midpoint-coordinate laws
    for the subdivision in 2.10.39, p. 199. *)
Parameter laws : forall (R : realType) n origin axis count node
  (he : orthonormal_family (@euclidean_inner_product R n) axis),
  @is_rectangular_grid_centres R n origin axis count node (@value R n origin axis count node he).
End RECTANGULAR_GRID.
Module RectangularGrid : RECTANGULAR_GRID.
(** Source for [value]: privately proved grid-centre
    witness supporting 2.10.39, p. 199,
    hidden by opaque module ascription. *)
Definition value (R : realType) n origin axis count node
  (he : orthonormal_family (@euclidean_inner_product R n) axis) :=
  projT1 (cid (@rectangular_grid_centres_exists R n origin axis count node he)).
(** Source for [laws]: proved midpoint-coordinate laws
    supporting the box subdivision in 2.10.39, p. 199. *)
Lemma laws (R : realType) n origin axis count node
  (he : orthonormal_family (@euclidean_inner_product R n) axis) :
  @is_rectangular_grid_centres R n origin axis count node (@value R n origin axis count node he).
Proof. exact: (projT2 (cid (@rectangular_grid_centres_exists R n origin axis count node he))). Qed.
End RectangularGrid.

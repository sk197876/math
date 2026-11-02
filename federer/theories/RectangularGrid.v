(** Public abstract grid centres supporting Federer (1969), 2.10.39, printed
    p. 199. Later covering proofs use only the midpoint-coordinate laws.
    Source context: RectangularGridUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  OrthonormalFamilies RectangularGridUP RectangularGridSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [rectangular_grid_centres]: abstract chosen
    small-box centres in 2.10.39, p. 199. *)
Definition rectangular_grid_centres (R : realType) n origin axis count node
    (he : orthonormal_family (@euclidean_inner_product R n) axis) :=
  @RectangularGrid.value R n origin axis count node he.

(** Source for [rectangular_grid_centres_specification]: proved
    midpoint-coordinate laws for the small-box centres
    used in 2.10.39, p. 199. *)
Theorem rectangular_grid_centres_specification (R : realType) n origin axis count node
    (he : orthonormal_family (@euclidean_inner_product R n) axis) :
  @is_rectangular_grid_centres R n origin axis count node
    (@rectangular_grid_centres R n origin axis count node he).
Proof. exact: RectangularGrid.laws. Qed.

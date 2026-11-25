(** Private orthonormal-coordinate witness for the grid centres used in
    Federer (1969), 2.10.39, printed p. 199. The proved coordinate
    specification is exposed only through an opaque sealed interface. Source
    context: RectangularGridUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps OrthonormalFamilies RectangularGridUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [rectangular_grid_centres_exists]: private
    existence proof of the small-box centres in
    2.10.39, p. 199. Synthesis in the specified
    orthonormal frame proves their required coordinates. *)
Theorem rectangular_grid_centres_exists (R : realType) n origin axis count node :
  orthonormal_family (@euclidean_inner_product R n) axis ->
  exists centre, @is_rectangular_grid_centres R n origin axis count node centre.
Proof.
move=> he.
exists (fun s : rectangular_grid_indices count=>origin+
  euclidean_frame_map axis ([ffun i=>(node i (s i)+node i (s i).+1)/2] : R_n R n)).
move=> s i; rewrite addrC addKr /euclidean_frame_map /= (euclidean_frame_inner he).
exact: ffunE.
Qed.

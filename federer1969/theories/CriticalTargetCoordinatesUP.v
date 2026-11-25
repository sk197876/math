(** Federer (1969), 3.4.3, p. 317: continuous linear
    coordinates which identify the actual differential range
    with R^nu. State their laws before proving existence. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_critical_target_coordinates]: the map L
    selected by Hahn–Banach in the first paragraph of the proof
    of 3.4.3, p. 317. Its restriction to the actual range of D
    is an isomorphism onto R^nu. J specifies its inverse there;
    neither map is supplied as an existence hypothesis. *)
Record is_critical_target_coordinates (R:realType) (X Y:lmodType R)
    (NY:Y->R) (D:Hom X Y) nu
    (L:Hom Y (R_n R nu)) (J:Hom (R_n R nu) Y):Prop:={
  (** Source for [critical_target_coordinates_bounded]: continuity
      of the selected L, 3.4.3, p. 317. *)
  critical_target_coordinates_bounded:norm_bounded_linear NY
    (inner_norm (@euclidean_inner_productP R nu)) L;
  (** Source for [critical_target_coordinates_inverse]: L J is
      the identity on R^nu, 3.4.3, p. 317. *)
  critical_target_coordinates_inverse:cancel J L;
  (** Source for [critical_target_coordinates_range]: J has exactly
      the original differential range, 3.4.3, p. 317. *)
  critical_target_coordinates_range:forall y,
    (exists x,D x=y) <->exists u,J u=y
}.

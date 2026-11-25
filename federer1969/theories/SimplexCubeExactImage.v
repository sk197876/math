(** Federer (1969), 4.1.27, p. 384:
    the image of the original open cube
    is exactly the set of strictly positive
    barycentric combinations of all original vertices.
    The inverse ratios do not require affine
    independence, so degenerate families are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOpenUnitCube SimplexCubeParametrisationUP
  SimplexCubeParametrisationSealed SimplexCubeBarycentricCoefficients
  SimplexCubeBarycentricExpansion PositiveBarycentricCubeInverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [simplex_cube_positive_barycentric_preimage]: the
    converse of the displayed image assertion
    in 4.1.27, p. 384. Every strictly
    positive barycentric family yields an actual
    point of the original cube, even
    for repeated vertices or m=0. *)
Theorem simplex_cube_positive_barycentric_preimage (R:realType) n m
    (v:'I_(m.+1)->R_n R n):
  simplex_positive_barycentric_image v `<=`
    (@SimplexCubeParametrisation.value R n m v) @` (@euclidean_open_unit_cube R m).
Proof.
move=>y [t [hPositive [hSum hY]]].
exists (positive_barycentric_cube_inverse t).
- exact:(@positive_barycentric_cube_inverse_in_cube R m t hPositive).
- rewrite simplex_cube_barycentric_expansion hY.
  apply:eq_bigr=>i _.
  by rewrite (@positive_barycentric_cube_inverse_coefficients R m t hPositive hSum i).
Qed.

(** Source for [simplex_cube_image]: the full literal
    image equality displayed in 4.1.27,
    p. 384, with every coefficient strictly
    positive and the sum exactly one. *)
Theorem simplex_cube_image (R:realType) n m
    (v:'I_(m.+1)->R_n R n):
  (@SimplexCubeParametrisation.value R n m v) @` (@euclidean_open_unit_cube R m)=
    simplex_positive_barycentric_image v.
Proof.
apply/seteqP;split.
- exact:simplex_cube_image_positive_barycentric.
- exact:simplex_cube_positive_barycentric_preimage.
Qed.

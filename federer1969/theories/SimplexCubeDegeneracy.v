(** Federer (1969), 4.1.27, p. 384:
    dependent vertices give the zero actual
    simplex current. Keep this case separate
    from the nondegenerate unit orientation in
    the normalized Hausdorff-density display. The
    earlier lower-dimensional support theorem supplies
    the zero-current conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading ExteriorNorm EuclideanLinearMaps CurrentSpaces CurrentSimplexFrame
  OrientedSimplexCurrentSealed OrientedSimplexDependentZero
  SimplexCubeParametrisationUP SimplexCubeCurrentImage SimplexConsecutiveOrientation
  SimplexHausdorffDensityUP SimplexHausdorffDensitySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [simplex_cube_degenerate_current_image]: the actual
    current-image identity of 4.1.27,
    p. 384, retains dependent vertex
    families as the zero current. No
    positive-degree assumption is added; the earlier
    independence predicate excludes a degenerate empty family. *)
Theorem simplex_cube_degenerate_current_image (R:realType) (h2:(1+1:R)!=0) n m
    (v:'I_(m.+1)->R_n R n):
  ~is_nondegenerate_current_simplex v->@simplex_cube_current_image R h2 n m v=0.
Proof.
move=>hDependent;rewrite simplex_cube_current_parametrisation.
exact:oriented_simplex_current_dependent_zero hDependent.
Qed.

(** Source for [simplex_hausdorff_density_degenerate_zero]: when zeta
    is zero the original algebraic density
    formula has value zero throughout, supporting
    the degenerate case of 4.1.27,
    p. 384. It is not asserted
    to be a unit orientation there. *)
Theorem simplex_hausdorff_density_degenerate_zero (R:realType) n m
    (v:'I_(m.+1)->R_n R n):
  ~is_nondegenerate_current_simplex v->
  @SimplexHausdorffDensity.value R n m v=(fun _=>0).
Proof.
move=>hDependent;apply:funext=>y.
pose hW:=@SimplexHausdorffDensity.laws R n m v.
case:(pselect (simplex_positive_barycentric_image v y))=>hY.
- rewrite (simplex_hausdorff_density_inside hW hY) /simplex_normalised_orientation
    (@simplex_consecutive_orientation_degenerate_zero R n m v hDependent).
  exact:scaler0.
- exact:(simplex_hausdorff_density_outside hW hY).
Qed.

(** Source for [simplex_normalised_orientation_unit]: the original
    normalized orientation in 4.1.27,
    p. 384, has norm one
    under nondegeneracy. The degree-zero empty product
    is retained by the already proved
    nonzero-product and norm laws. *)
Theorem simplex_normalised_orientation_unit (R:realType) (h2:(1+1:R)!=0) n m
    (v:'I_(m.+1)->R_n R n):
  is_nondegenerate_current_simplex v->
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (simplex_normalised_orientation v)= 1.
Proof.
move=>hIndependent.
pose z:=simplex_consecutive_orientation v.
pose N:=exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n).
have hZ:z!=0:=@simplex_consecutive_orientation_nonzero R h2 n m v hIndependent.
have hN:N m z!=0 by rewrite /N exterior_norm_eq0.
have hPositive:0<N m z.
  rewrite lt_neqAle eq_sym hN /=;exact:exterior_norm_nonnegative.
have hInverse:0<=(N m z)^-1 by rewrite invr_ge0;exact:ltW hPositive.
rewrite /simplex_normalised_orientation exterior_norm_scale.
rewrite (ger0_norm hInverse) mulVf //.
Qed.

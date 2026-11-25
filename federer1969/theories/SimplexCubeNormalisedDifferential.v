(** Federer (1969), 4.1.27, p. 384:
    on the original open cube the
    diagonal weight is positive, so the
    normalized exterior differential is zeta/|zeta|.
    The Jacobian identity itself keeps all
    vertices and all source points; the
    nondegenerate interpretation is stated separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  ExteriorGrading FiniteExteriorPowers ExteriorMaps ExteriorNorm
  ExteriorOperatorEstimate EuclideanLinearMaps EuclideanLinearJacobian
  EuclideanOrthonormalJacobian EuclideanStiefelInnerSplitting
  CurrentMapDifferential CurrentSimplexFrame EuclideanOpenUnitCube
  SimplexCubeParametrisationUP SimplexCubeParametrisationSealed
  SimplexCubeJacobian SimplexConsecutiveOrientation CurrentAreaNormalisedImageUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [simplex_cube_jacobian_weight_positive]: every diagonal
    factor of the original differential is
    positive on C, in 4.1.27,
    p. 384. The empty product at
    m=0 and the zero exponent at
    the final coordinate both contribute one. *)
Lemma simplex_cube_jacobian_weight_positive (R:realType) m (x:R_n R m):
  euclidean_open_unit_cube x->0<simplex_cube_jacobian_weight x.
Proof.
move=>hX;rewrite /simplex_cube_jacobian_weight.
apply:prodr_gt0=>i _;exact:exprn_gt0 _ (andP (hX i)).1.
Qed.

(** Source for [simplex_cube_jacobian]: the norm version
    of the displayed wedge formula in
    4.1.27, p. 384, by the
    actual top-source Jacobian of 3.2.1,
    p. 241. The absolute value retains
    every point outside the positive cube. *)
Theorem simplex_cube_jacobian (R:realType) n m
    (v:'I_(m.+1)->R_n R n) (x:R_n R m):
  @euclidean_linear_jacobian R m n m
    (@current_map_differential R m n (fun _=>True)
      (@SimplexCubeParametrisation.value R n m v) x)=
    `|simplex_cube_jacobian_weight x|*
      exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
        (simplex_consecutive_orientation v).
Proof.
rewrite (@euclidean_jacobian_orthonormal_frame R m n
  (@current_map_differential R m n (fun _=>True)
    (@SimplexCubeParametrisation.value R n m v) x)
  (@coordinate_basis R m) (@euclidean_coordinate_orthonormal_family R m))
  simplex_cube_wedge_differential exterior_norm_scale.
by [].
Qed.

(** Source for [simplex_cube_jacobian_positive]: affine independence
    makes the original differential univalent on
    C, as used in 4.1.27,
    p. 384. Both the positive polynomial
    weight and the nonzero original orientation
    are derived from earlier laws. *)
Theorem simplex_cube_jacobian_positive (R:realType) (h2:(1+1:R)!=0) n m
    (v:'I_(m.+1)->R_n R n) (x:R_n R m):
  is_nondegenerate_current_simplex v->euclidean_open_unit_cube x->
  0<@euclidean_linear_jacobian R m n m
    (@current_map_differential R m n (fun _=>True)
      (@SimplexCubeParametrisation.value R n m v) x).
Proof.
move=>hIndependent hX.
have hVector:simplex_consecutive_orientation v!=0:=
  @simplex_consecutive_orientation_nonzero R h2 n m v hIndependent.
have hNorm:0<exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (simplex_consecutive_orientation v).
  rewrite lt_neqAle eq_sym exterior_norm_eq0 hVector /=.
  exact:exterior_norm_nonnegative.
have hWeight:=@simplex_cube_jacobian_weight_positive R m x hX.
rewrite simplex_cube_jacobian (ger0_norm (ltW hWeight)).
exact:mulr_gt0 hWeight hNorm.
Qed.

(** Source for [simplex_cube_normalised_top_differential]: the normalized
    original top-vector image equals zeta/|zeta|
    on C, the final density calculation
    in 4.1.27, p. 384. The
    algebraic equality does not divide out
    the orientation; its degenerate zero interpretation
    is not asserted to be a unit orientation. *)
Theorem simplex_cube_normalised_top_differential (R:realType) n m
    (v:'I_(m.+1)->R_n R n) (x:R_n R m):
  euclidean_open_unit_cube x->
  @current_area_normalised_image_coefficient R m n
    (fun _=>e_lambda (@coordinate_basis R m) (ord_tuple m)) x
    (@current_map_differential R m n (fun _=>True)
      (@SimplexCubeParametrisation.value R n m v) x)=
      (exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
        (simplex_consecutive_orientation v))^-1*:simplex_consecutive_orientation v.
Proof.
move=>hX.
have hWeight:=@simplex_cube_jacobian_weight_positive R m x hX.
have hNonzero:=lt0r_neq0 hWeight.
by rewrite /current_area_normalised_image_coefficient exterior_map_indexed_product
  simplex_cube_wedge_differential simplex_cube_jacobian (ger0_norm (ltW hWeight))
  scalerA invfM mulrAC mulVf // mul1r.
Qed.

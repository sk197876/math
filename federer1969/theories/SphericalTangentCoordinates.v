(** Federer (1969), 3.2.48, pp. 285–286: actual
    orthonormal coordinates on the tangent hyperplane at c.
    A local orthogonal change sends the coordinate pole to
    c; its transverse block and inverse are used only
    through proved linear, isometry and inverse laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates CoordinateProjection
  EuclideanInnerProduct InnerProductUP InnerNormalization InnerNorm InnerProductLaws Bilinear OrthogonalMaps
  EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse EuclideanBlockCoordinates
  EuclideanBlockLinear EuclideanBlockLinearMaps SphericalCoordinateIsotropy
  EuclideanStiefelInnerSplitting OrthonormalFamilies UnitVectorOrthogonalMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [spherical_transverse_embedding]: supporting actual
    tangent coordinates in 3.2.48, p. 285. Apply
    Q to the existing transverse coordinate inclusion. *)
Definition spherical_transverse_embedding (R:realType) d
    (Q:Hom (R_n R (1+d)) (R_n R (1+d))):=
  hom_comp Q (@euclidean_last_injection_map R 1 d).

(** Source for [spherical_transverse_coordinates]: the actual inverse
    transverse coordinates supporting 3.2.48, p. 285.
    The original inverse orthogonal map is its actual adjoint. *)
Definition spherical_transverse_coordinates (R:realType) d
    (Q:Hom (R_n R (1+d)) (R_n R (1+d))):=
  hom_comp (@euclidean_last_block_map R 1 d) (euclidean_rectangular_adjoint Q).

(** Source for [spherical_transverse_embedding_orthogonal]: actual
    tangent-coordinate isometry supporting the vertical maps
    in 3.2.48, pp. 285–286. Zero transverse
    dimension retains its literal empty-coordinate space. *)
Lemma spherical_transverse_embedding_orthogonal (R:realType) d
    (Q:Hom (R_n R (1+d)) (R_n R (1+d))):
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->
  is_orthogonal_map (@euclidean_inner_product R d)
    (@euclidean_inner_product R (1+d)) (hom_as_linear (spherical_transverse_embedding Q)).
Proof.
move=>hQ x y; change (euclidean_inner_product (Q (@euclidean_last_injection R 1 d x))
  (Q (@euclidean_last_injection R 1 d y))=euclidean_inner_product x y).
rewrite hQ /euclidean_last_injection euclidean_block_join_inner /=.
by rewrite (bil0l (inner_bilinear (@euclidean_inner_productP R 1))) add0r.
Qed.

(** Source for [spherical_transverse_coordinatesK]: supporting exact
    inverse on tangent coordinates in 3.2.48, p. 285,
    derived from Q inverse Q and the actual block laws. *)
Lemma spherical_transverse_coordinatesK (R:realType) d
    (Q:Hom (R_n R (1+d)) (R_n R (1+d))):
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->
  cancel (spherical_transverse_embedding Q) (spherical_transverse_coordinates Q).
Proof.
move=>hQ x; change (@euclidean_last_block R 1 d
  (euclidean_rectangular_adjoint Q (Q (@euclidean_last_injection R 1 d x)))=x).
by rewrite (euclidean_orthogonal_adjoint_cancel hQ) euclidean_last_block_injectionK.
Qed.

(** Source for [spherical_transverse_embedding_perpendicular]: the
    transverse range lies in Tan(Sphere,Q(c_0)), supporting
    3.2.48, p. 285. This is an actual inner-product
    equation, rather than an assumed tangent identification. *)
Lemma spherical_transverse_embedding_perpendicular (R:realType) d
    (Q:Hom (R_n R (1+d)) (R_n R (1+d))):
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->forall x,
  euclidean_inner_product (Q (spherical_coordinate_pole R d)) (spherical_transverse_embedding Q x)=0.
Proof.
move=>hQ x; change (euclidean_inner_product (Q (spherical_coordinate_pole R d))
  (Q (@euclidean_last_injection R 1 d x))=0).
rewrite hQ (inner_symmetric (@euclidean_inner_productP R (1+d)))
  /spherical_coordinate_pole euclidean_inner_basis
  /euclidean_last_injection euclidean_block_join_left ffunE.
reflexivity.
Qed.

(** Source for [spherical_transverse_coordinates_inverse]: every
    actual tangent vector is restored by its transverse
    coordinates, supporting 3.2.48, p. 285. The
    perpendicularity premise is proved from the original
    sphere tangents in the kinematic application. *)
Lemma spherical_transverse_coordinates_inverse (R:realType) d
    (Q:Hom (R_n R (1+d)) (R_n R (1+d))):
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->forall v,
  euclidean_inner_product (Q (spherical_coordinate_pole R d)) v=0 ->
  spherical_transverse_embedding Q (spherical_transverse_coordinates Q v)=v.
Proof.
move=>hQ v hv.
pose w:=euclidean_rectangular_adjoint Q v.
have hPole:euclidean_inner_product (spherical_coordinate_pole R d) w=0.
  by rewrite /w euclidean_rectangular_adjoint_pairing.
have hFirst:@euclidean_first_block R 1 d w=0.
  apply/ffunP=>i; rewrite /euclidean_first_block !ffunE (ord1 i).
  by rewrite (inner_symmetric (@euclidean_inner_productP R (1+d)))
    /spherical_coordinate_pole euclidean_inner_basis in hPole.
have hDecompose:=@euclidean_block_linear_decomposition R 1 d w.
rewrite hFirst in hDecompose.
have hZero:@euclidean_first_injection R 1 d 0=0.
  exact (lin0 (@euclidean_first_injection_linear R 1 d)).
rewrite hZero add0r in hDecompose.
change (Q (@euclidean_last_injection R 1 d (@euclidean_last_block R 1 d w))=v).
rewrite -hDecompose /w; exact (euclidean_orthogonal_adjoint_cancel_reverse hQ v).
Qed.

(** Source for [spherical_transverse_frame_exists]: supporting the
    local orthonormal tangent coordinates in 3.2.48,
    pp. 285–286. An actual orthogonal Q sends
    the coordinate pole to the original unit c;
    no global choice of Q is made. *)
Theorem spherical_transverse_frame_exists (R:realType) d (c:R_n R (1+d)):
  inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  exists Q:Hom (R_n R (1+d)) (R_n R (1+d)),
    is_orthogonal_map (@euclidean_inner_product R (1+d))
      (@euclidean_inner_product R (1+d)) (hom_as_linear Q) /\
    Q (spherical_coordinate_pole R d)=c.
Proof.
move=>hc.
have hPole:inner_norm (@euclidean_inner_productP R (1+d)) (spherical_coordinate_pole R d)= 1.
  exact (@orthonormal_norm1 R (R_n R (1+d)) (@euclidean_inner_product R (1+d))
    (@euclidean_inner_productP R (1+d)) (Finite.clone 'I_(1+d) _)
    (@coordinate_basis R (1+d)) (@euclidean_coordinate_orthonormal_family R (1+d))
    (lshift d (ord0:'I_1))).
have hPositive:(0<1+d)%N by rewrite add1n ltn0Sn.
have [Q [hQ hQc]]:=@unit_vector_orthogonal_map_exists R (1+d)
  (spherical_coordinate_pole R d) c hPositive hPole hc.
exists (hom_of_linear Q); by split.
Qed.

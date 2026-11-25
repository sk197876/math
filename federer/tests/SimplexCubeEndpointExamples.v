(** Actual-space endpoint regressions for Federer (1969),
    4.1.27, p. 384: the nonzero R^0
    cube image, the original unit interval,
    a collapsed positive-degree simplex, a
    zero-coordinate Jacobian, the open-image boundary
    density and the unit zero-degree orientation.
    All use the final public operations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm InnerMetric HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanOneCoordinate EuclideanLinearMaps Biorthogonal
  ExteriorGrading FiniteExteriorPowers ExteriorNorm
  CurrentSpaces CurrentDirac CurrentMapDifferential CurrentSimplexFrame CurrentDensityAction
  CurrentSegmentMapUP OrientedSegmentCurrentSealed OrientedSimplexCurrentSealed
  OrientedSimplexCurrentLaws OrientedSimplexCurrentLowDegrees OrientedSimplexPermutation
  EuclideanFundamentalCurrent EuclideanFundamentalCurrentPoint EuclideanFundamentalCurrentNonzero
  SimplexCubeParametrisationUP SimplexCubeParametrisationSealed SimplexCubeJacobian
  SimplexCubeCurrentImage SimplexCubeDegeneracy
  HausdorffMeasure SimplexHausdorffDensityUP SimplexHausdorffDensitySealed
  SimplexHausdorffCurrent SimplexHausdorffCurrentAllVertices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [simplex_cube_point_image_nonzero]: the original
    zero-dimensional cube in 4.1.27,
    p. 384, has the actual nonzero
    point image, retaining the empty-product
    convention already used in 4.1.8. *)
Example simplex_cube_point_image_nonzero (R:realType) (h2:(1+1:R)!=0):
  @simplex_cube_current_image R h2 0%N 0%N (fun _=>0)=
      @euclidean_fundamental_current R h2 0%N /\
    @simplex_cube_current_image R h2 0%N 0%N (fun _=>0)<>0.
Proof.
have hImage:@simplex_cube_current_image R h2 0%N 0%N (fun _=>0)=
    @euclidean_fundamental_current R h2 0%N.
  by rewrite simplex_cube_current_parametrisation oriented_simplex_current_point
    -euclidean_fundamental_current_point.
split;first exact:hImage.
rewrite hImage;exact:euclidean_fundamental_current_nonzero.
Qed.

(** Source for [simplex_cube_unit_interval_image]: the final
    actual cube-image theorem of 4.1.27,
    p. 384, recovers the original
    ordered segment [0,1] from 4.1.8,
    p. 362, on its actual one-dimensional source. *)
Example simplex_cube_unit_interval_image (R:realType) (h2:(1+1:R)!=0):
  let v:'I_2->R_n R 1%N:=ordinal_cons (@euclidean_one_embed R 0)
    (fun _:'I_1=>@euclidean_one_embed R 1) in
  @simplex_cube_current_image R h2 1%N 1%N v=
    @OrientedSegmentCurrent.value R h2 1%N (fun _=>True)
      (fun x (_:True)=>norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R 1%N)) x)
      (v ord0) (v (lift ord0 ord0)) (fun _ _=>Logic.I).
Proof.
move=>v;rewrite simplex_cube_current_parametrisation.
exact:oriented_simplex_current_segment.
Qed.

(** Source for [simplex_cube_collapsed_interval_image]: repeated endpoints
    give the zero actual cube image,
    retaining the degenerate case in the
    current identity of 4.1.27, p. 384. *)
Example simplex_cube_collapsed_interval_image (R:realType) (h2:(1+1:R)!=0):
  @simplex_cube_current_image R h2 1%N 1%N (fun _=>0)=0.
Proof.
rewrite simplex_cube_current_parametrisation.
apply:(@oriented_simplex_current_repeated_vertices R h2 1%N 1%N (fun _=>0)
  ord0 (lift ord0 ord0));last by [].
by rewrite -val_eqE /=.
Qed.

(** Source for [simplex_cube_zero_coordinate_wedge]: the displayed
    wedge formula of 4.1.27, p. 384,
    holds on the cube boundary as
    well: its positive-degree diagonal weight vanishes
    at the actual origin in R^2. *)
Example simplex_cube_zero_coordinate_wedge (R:realType):
  e_lambda (fun j=>@current_map_differential R 2%N 2%N (fun _=>True)
    (@SimplexCubeParametrisation.value R 2%N 2%N
      (@current_standard_simplex_vertices R 2%N)) 0 (@coordinate_basis R 2%N j))
    (ord_tuple 2%N)=0.
Proof.
rewrite simplex_cube_wedge_differential /simplex_cube_jacobian_weight big_ord_recl /= big_ord1.
by rewrite !ffunE expr1 mul0r scale0r.
Qed.

(** Source for [simplex_cube_interval_endpoint_density]: the original
    density is zero at the boundary
    point 0, outside the displayed positive
    barycentric image in 4.1.27, p. 384.
    The current still retains its full
    compact support in the closed interval. *)
Example simplex_cube_interval_endpoint_density (R:realType):
  let v:'I_2->R_n R 1%N:=ordinal_cons (@euclidean_one_embed R 0)
    (fun _:'I_1=>@euclidean_one_embed R 1) in
  @SimplexHausdorffDensity.value R 1%N 1%N v (@euclidean_one_embed R 0)=0.
Proof.
move=>v;apply:(simplex_hausdorff_density_outside
  (@SimplexHausdorffDensity.laws R 1%N 1%N v)).
move=>[t [hPositive [_ hImage]]].
have hCoordinate:=congr1 (fun z:R_n R 1%N=>z ord0) hImage.
rewrite big_ord_recl big_ord1 /v ordinal_cons0 ordinal_consS
  /euclidean_one_embed !ffunE in hCoordinate.
change (0=t ord0*0+t (lift ord0 ord0)*1) in hCoordinate.
rewrite mulr0 mulr1 add0r in hCoordinate.
have hStrict:=hPositive (lift ord0 ord0).
by rewrite -hCoordinate ltxx in hStrict.
Qed.

(** Source for [simplex_cube_point_density_unit]: the literal
    empty wedge has unit density at
    the actual R^0 point in 4.1.27,
    p. 384. This guards against
    replacing the nonzero empty product by
    a positive-degree zero-current convention. *)
Example simplex_cube_point_density_unit (R:realType) (h2:(1+1:R)!=0):
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R 0%N)
    (@SimplexHausdorffDensity.value R 0%N 0%N (fun _=>0) 0)= 1.
Proof.
pose v:=fun _:'I_1=>(0:R_n R 0%N).
have hIndependent:is_nondegenerate_current_simplex v.
  move=>c hC i;by have:=ltn_ord i;rewrite ltn0.
have hImage:simplex_positive_barycentric_image v 0.
  exists (fun _=>1);split;first by move=>i;exact:ltr01.
  split;first by rewrite big_ord1.
  by rewrite big_ord1 scale1r.
rewrite (simplex_hausdorff_density_inside (@SimplexHausdorffDensity.laws R 0%N 0%N v) hImage).
exact:(@simplex_normalised_orientation_unit R h2 0%N 0%N v hIndependent).
Qed.

(** Source for [simplex_cube_collapsed_hausdorff_action]: the final
    all-vertices theorem gives the literal
    Hausdorff action of the actual zero
    current for a collapsed interval, checking
    the degenerate interpretation of 4.1.27,
    p. 384, without an added independence premise. *)
Example simplex_cube_collapsed_hausdorff_action (R:realType) (h2:(1+1:R)!=0):
  @is_current_density_action R h2 1%N 1%N
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1%N)) 1%N)
    (@SimplexHausdorffDensity.value R 1%N 1%N (fun _=>0))
    (0:@current_space R h2 1%N (fun _=>True)
      (fun x (_:True)=>norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R 1%N)) x) 1%N).
Proof.
have h:=@simplex_hausdorff_current_full_action R h2 1%N 1%N (fun _=>0).
have hZero:@OrientedSimplexCurrent.value R h2 1%N 1%N (fun _=>0)=0.
  apply:(@oriented_simplex_current_repeated_vertices R h2 1%N 1%N (fun _=>0)
    ord0 (lift ord0 ord0));last by [].
  by rewrite -val_eqE /=.
by rewrite hZero in h.
Qed.

(** Source for [simplex_cube_point_hausdorff_action]: the final
    actual density theorem in 4.1.27,
    p. 384, retains the nonzero
    Euclidean current on R^0 and its
    counting-measure density. No positive-degree
    normalization is used in this case. *)
Example simplex_cube_point_hausdorff_action (R:realType) (h2:(1+1:R)!=0):
  @is_current_density_action R h2 0%N 0%N
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 0%N)) 0%N)
    (@SimplexHausdorffDensity.value R 0%N 0%N (fun _=>0))
    (@euclidean_fundamental_current R h2 0%N).
Proof.
have h:=@simplex_hausdorff_current_full_action R h2 0%N 0%N (fun _=>0).
by rewrite oriented_simplex_current_point -euclidean_fundamental_current_point in h.
Qed.

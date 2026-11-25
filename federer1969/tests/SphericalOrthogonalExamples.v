(** Federer (1969), 3.2.47, pp. 282–283: concrete
    positive-atom and horizontal-scale regressions. The actual
    one-dimensional sphere has two points, the stabilizer has
    one, and the planar horizontal lift has squared length two. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology lra.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerProductLaws InnerNorm InnerMetric
  CoordinateProjection EuclideanOneCoordinate EuclideanOneNormDifferential EuclideanLinearMaps
  EuclideanHomInnerCharts OrthogonalMaps UnitSphereSpace HausdorffMeasure
  HausdorffCountingMeasure CountingMeasure CountingInjectionBound
  HausdorffUnitSphereMass EuclideanBallVolume EuclideanUnitSphereRectifiable
  RectifiableSetUP RectifiableElementary MeasureUP MeasureBasic MeasureAlmostUP
  RealPower SphericalOrthogonalProductAlgebra SphericalProductPreimageImage
  SphericalIsotropyMeasure SphericalOrthogonalFibreIsometry StiefelGammaVolumeScalar SphericalFiniteBaseMass
  SphericalPullbackZeroDegree SphericalOrthogonalPullback SphericalOrthogonalMass
  SphericalOrthogonalTangentTranslation SphericalPreimageHorizontalDimension
  SphericalHorizontalLift SphericalHorizontalSpace SphericalPreimageJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_line_pole_unit]: the actual positive
    unit pole in the ambient-dimension-one regression for
    3.2.47, p. 283, by the coordinate norm of 1.7.1. *)
Lemma spherical_line_pole_unit (R:realType):
  inner_norm (@euclidean_inner_productP R 1) (euclidean_one_embed (1:R))= 1.
Proof. by rewrite euclidean_one_norm_coordinate /euclidean_one_embed ffunE normr1. Qed.

(** Source for [spherical_two_atom_preimage_example]: the original
    converse and mass formula 3.2.47(3), p. 283,
    applied to the whole actual two-point sphere. The preimage
    has H^0 mass two and I has H^0 mass one; neither
    a sphere point nor the positive isotropy atom is lost. *)
Example spherical_two_atom_preimage_example (R:realType):
  let c:=euclidean_one_embed (1:R) in
  let E:=@euclidean_unit_sphere_set R 1 in
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R 1)) 0) 0 E /\
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R 1 1)) 0
    (spherical_orthogonal_isotropy c)= 1%E /\
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R 1 1)) 0
    (spherical_orthogonal_preimage c E)= 2%E.
Proof.
move=>c E.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose H:=inner_metric_space (@euclidean_hom_inner_productP R 1 1).
have hc:=spherical_line_pole_unit R.
have hE:@is_m_rectifiable R X 0 E:=@euclidean_unit_sphere_rectifiable R 1.
have hES:E `<=` @euclidean_unit_sphere_set R 1 by move=>x hx.
have hI:@hausdorff_measure R H 0 (spherical_orthogonal_isotropy c)= 1%E.
  have hh:=@spherical_isotropy_gamma_mass R 0 c hc.
  by rewrite stiefel_gamma_volume_scalar_zero in hh.
have hEMass:@hausdorff_measure R X 0 E= 2%E.
  have hh:=@hausdorff_unit_sphere_mass R 1 (ltnSn 0).
  by rewrite euclidean_unit_ball_volume1 mul1r in hh.
have hP:@is_m_rectifiable R H 0 (spherical_orthogonal_preimage c E).
  exact (@federer_3_2_47_1 R 0 c E 0 hc hES hE).
have hMass:@hausdorff_measure R H 0 (spherical_orthogonal_preimage c E)= 2%E.
  have hh:=@spherical_finite_base_mass R 0 c E hc hES hE.
  by rewrite hI hEMass mul1e in hh.
have hRect:is_measure_m_rectifiable (@hausdorff_measure R H 0) 0
    (spherical_orthogonal_preimage c E).
  split.
  - split; first exact (@hausdorff_measure_is_measure R H 0).
    exists (spherical_orthogonal_preimage c E); split.
    + exact (@rectifiable_countably_rectifiable R H 0 _ hP).
    + rewrite /measure_almost_included setDv; exact:measure_empty (@hausdorff_measure_is_measure R H 0).
  - by rewrite hMass ltry.
have hFull:=@federer_3_2_47_3 R 0 c E 0 hc hES hRect.
split; first exact hFull.1.
split; first exact hI.
have hh:=hFull.2.
by rewrite mul0r real_power_zero_exponent hI hEMass !mul1e in hh.
Qed.

(** Source for [spherical_negative_pole_fibre_example]: a point
    in the other sphere hemisphere still has its whole fibre,
    as required by the exact U and fibre-isometry assertion
    of 3.2.47, pp. 282–283. In dimension one its
    actual H^0 mass is the positive unit atom. *)
Example spherical_negative_pole_fibre_example (R:realType):
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R 1 1)) 0
    (spherical_orthogonal_preimage (euclidean_one_embed (1:R))
      [set euclidean_one_embed (-1:R)])= 1%E.
Proof.
have hc:=spherical_line_pole_unit R.
have hz:inner_norm (@euclidean_inner_productP R 1) (euclidean_one_embed (-1:R))= 1.
  by rewrite euclidean_one_norm_coordinate /euclidean_one_embed ffunE normrN normr1.
rewrite (@spherical_orthogonal_fibre_measure R 0 _ _ hc hz 0).
have hh:=@spherical_isotropy_gamma_mass R 0 (euclidean_one_embed (1:R)) hc.
by rewrite stiefel_gamma_volume_scalar_zero in hh.
Qed.

(** Source for [spherical_planar_horizontal_example]: a nonzero
    horizontal tangent in the actual Hilbert Hom metric tests
    the factor 2^(-1/2) in 3.2.47, p. 283.
    Its evaluation is a unit vector and its squared norm
    is two, excluding a vacuous zero-vector scale test. *)
Example spherical_planar_horizontal_example (R:realType):
  exists (c v:R_n R 2) (w:Hom (R_n R 2) (R_n R 2)),
    inner_norm (@euclidean_inner_productP R 2) c= 1 /\
    inner_norm (@euclidean_inner_productP R 2) v= 1 /\
    spherical_horizontal_space (hom_of_linear (linear_id (R_n R 2))) c w /\
    w c=v /\euclidean_hom_inner_product w w= 2.
Proof.
pose c:=@coordinate_basis R 2 ord0.
pose v:=@coordinate_basis R 2 ord_max.
pose idV:Hom (R_n R 2) (R_n R 2):=hom_of_linear (linear_id (R_n R 2)).
pose w:=spherical_horizontal_lift idV c v.
have hId:is_orthogonal_map (@euclidean_inner_product R 2)
    (@euclidean_inner_product R 2) (hom_as_linear idV) by move=>x y.
have hC:euclidean_inner_product c c= 1.
  by rewrite /c euclidean_inner_basis /coordinate_basis ffunE eqxx.
have hV:euclidean_inner_product v v= 1.
  by rewrite /v euclidean_inner_basis /coordinate_basis ffunE eqxx.
have hPerp:euclidean_inner_product (idV c) v=0.
  change (euclidean_inner_product c v=0).
  by rewrite /c /v euclidean_inner_basis /coordinate_basis ffunE.
have hCN:inner_norm (@euclidean_inner_productP R 2) c= 1.
  apply:inner_norm_value; first exact:ler01.
  by rewrite expr1n hC.
have hVN:inner_norm (@euclidean_inner_productP R 2) v= 1.
  apply:inner_norm_value; first exact:ler01.
  by rewrite expr1n hV.
exists c,v,w; split; first exact hCN.
split; first exact hVN.
split; first exact (@spherical_horizontal_lift_member R 2 idV c v hId).
split; first exact (@spherical_horizontal_lift_evaluation R 2 idV c v hC hPerp).
by rewrite (@spherical_horizontal_lift_square R 2 idV c v hId hC hPerp) hV mulr1.
Qed.

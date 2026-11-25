(** Federer (1969), 3.2.33, p. 270: the source
    cylinder X has exactly the scalar length of T minus V. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates EuclideanOneNormDifferential NormMetricScaleContinuity
  EuclideanBlockLinearMaps EuclideanOneCoordinate EuclideanLebesgue EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes HausdorffMeasure EuclideanHausdorffLebesgue LebesgueScalarMeasure RealMetricBackground RealOpenIntervals
  EuclideanOpenUnitCube EuclideanUnitCubeBorel EuclideanBlockRectangleMass
  MeasureUP MeasurePushforward BorelRegularMeasureUP TopologicalBorel ContinuousBorelPreimages ProductBorelRectangles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_coordinate_slab_mass]: the equality
    H^m(X)=L^1(T minus V) in Federer 3.2.33,
    p. 270, for any Borel scalar subset K of T.
    Two actual block rectangles and the scalar-line identification
    prove the equality, including zero-dimensional outer blocks.
    No product-measure formula or source mass is assumed. *)
Theorem euclidean_coordinate_slab_mass (R:realType) mu k (K:set (real_line_metric R)):
  borel_set K ->K `<=` real_open_interval 0 1 ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))) ((mu+1)+k)
    [set x|euclidean_open_unit_cube x /\K (x (lshift k (rshift mu ord0)))]=lebesgue_scalar_measure K.
Proof.
move=>hK hKT.
pose B:set (inner_metric_space (@euclidean_inner_productP R 1)):=(@euclidean_one_project R) @^-1` K.
pose S:set (inner_metric_space (@euclidean_inner_productP R (mu+1))):=(@euclidean_block_split R mu 1) @^-1`
  ((@euclidean_open_unit_cube R mu) `*` B).
pose C:set (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))):=
  [set x|euclidean_open_unit_cube x /\K (x (lshift k (rshift mu ord0)))].
have hOneContinuous:continuous (fun u:inner_metric_space (@euclidean_inner_productP R 1)=>
    (euclidean_one_project u:real_line_metric R)).
  apply:(@metric_fixed_lipschitz_continuous R (inner_metric_space (@euclidean_inner_productP R 1))
    (real_line_metric R) (@euclidean_one_project R) 1 (@ler01 R))=>u v.
  by rewrite real_line_metric_distanceE inner_metric_distanceE euclidean_one_norm_coordinate
    /euclidean_one_project !ffunE mul1r.
have hB:borel_set B:=continuous_borel_preimage hOneContinuous hK.
have hS:borel_set S:=continuous_borel_preimage (@euclidean_block_split_continuous R mu 1)
  (borel_product_rectangle (@euclidean_open_unit_cube_borel R mu) hB).
have hCubeMeas d:measure_measurable (@euclidean_lebesgue_measure R d) (@euclidean_open_unit_cube R d).
  exact:(borel_regular_borel_measurable (euclidean_lebesgue_is_measure R d)
    (euclidean_lebesgue_borel_regular R d) (@euclidean_open_unit_cube_borel R d)).
have hBMeas:measure_measurable (@euclidean_lebesgue_measure R 1) B.
  exact:(borel_regular_borel_measurable (euclidean_lebesgue_is_measure R 1)
    (euclidean_lebesgue_borel_regular R 1) hB).
have hSMeas:measure_measurable (@euclidean_lebesgue_measure R (mu+1)) S.
  exact:(borel_regular_borel_measurable (euclidean_lebesgue_is_measure R (mu+1))
    (euclidean_lebesgue_borel_regular R (mu+1)) hS).
have hBMass:euclidean_lebesgue_measure 1 B=lebesgue_scalar_measure K.
  rewrite /euclidean_lebesgue_measure positive_euclidean_lebesgue_first /measure_pushforward.
  congr (lebesgue_scalar_measure _); apply/seteqP; split=>t ht.
  - change (K (euclidean_one_project (euclidean_one_embed t))) in ht.
    by rewrite euclidean_one_embedK in ht.
  - change (K (euclidean_one_project (euclidean_one_embed t))).
    by rewrite euclidean_one_embedK.
have hSMass:euclidean_lebesgue_measure (mu+1) S=lebesgue_scalar_measure K.
  rewrite /S (euclidean_block_rectangle_mass (hCubeMeas mu) hBMeas).
  by rewrite /euclidean_open_unit_cube euclidean_unit_cube hBMass mul1e.
have hSet:C=(@euclidean_block_split R (mu+1) k) @^-1`
    (S `*` (@euclidean_open_unit_cube R k)).
  apply/seteqP; split=>x.
  - move=>[hx hKx].
    have [hPrefix hTail]:=(euclidean_open_unit_cube_split x).1 hx.
    have [hU hT]:=(euclidean_open_unit_cube_split (@euclidean_first_block R (mu+1) k x)).1 hPrefix.
    split; last exact hTail.
    split; first exact hU.
    rewrite /B /euclidean_one_project /euclidean_block_split /= !ffunE; exact hKx.
  - move=>[[hU hBPoint] hTail].
    rewrite /B /euclidean_one_project /euclidean_block_split /= !ffunE in hBPoint.
    have hKx:K (x (lshift k (rshift mu ord0))):=hBPoint.
    have hT:euclidean_open_unit_cube
        (@euclidean_last_block R mu 1 (@euclidean_first_block R (mu+1) k x)).
      apply:(euclidean_open_unit_cube_one _).2.
      rewrite /euclidean_one_project /euclidean_last_block /euclidean_first_block !ffunE.
      have [h0 h1]:=hKT _ hKx; by apply/andP; split.
    split; last exact hKx.
    apply:(euclidean_open_unit_cube_split x).2; split; last exact hTail.
    exact:(euclidean_open_unit_cube_split (@euclidean_first_block R (mu+1) k x)).2 (conj hU hT).
rewrite (euclidean_hausdorff_spherical_lebesgue C).1 hSet
  (euclidean_block_rectangle_mass hSMeas (hCubeMeas k)) hSMass.
by rewrite /euclidean_open_unit_cube euclidean_unit_cube mule1.
Qed.

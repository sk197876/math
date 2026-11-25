(** Federer (1969), 4.1.27, p. 384:
    the original cube current is the
    ordered product of its coordinate cube
    currents, by 4.1.8, p. 362.
    This exact source identity supplies the
    recursive simplex image, with all empty
    and one-coordinate factors retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanCartesianMap EuclideanOpenUnitCube EuclideanUnitCubeBorel
  CurrentSpaces CurrentDirac CurrentCartesianDomain CurrentCartesianProductSealed CurrentDomainTransport
  CurrentAmbientCartesianProduct CurrentCartesianEuclideanCharacteristic
  OpenEuclideanCharacteristicCurrent OpenEuclideanCharacteristicFull
  EuclideanCharacteristicDomainTransport EuclideanCharacteristicCurrent
  EuclideanFundamentalCurrent EuclideanFundamentalCurrentPoint EuclideanLebesgueDimensions
  MeasureUP CurrentJoinDomain ScalarOrientedSegmentInterval RealMetricBackground
  SimplexCubeSourceCurrent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [simplex_cube_current_product]: the original
    Euclidean current on the open unit
    cube factors in its original coordinate
    order, supporting 4.1.27, p. 384,
    by the characteristic-current product in 4.1.8,
    p. 362. Both zero dimensions are retained. *)
Theorem simplex_cube_current_product (R:realType) (h2:(1+1:R)!=0) a b:
  @current_ambient_cartesian_product R h2 a b a b
    (@simplex_cube_source_current R h2 a) (@simplex_cube_source_current R h2 b)=
      @simplex_cube_source_current R h2 (a+b)%N.
Proof.
pose Full:=fun d:nat=>fun _:R_n R d=>True.
pose hFull:=fun (d:nat) (x:R_n R d) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R d)) x.
pose A:=@euclidean_open_unit_cube R a.
pose B:=@euclidean_open_unit_cube R b.
pose EF:=@euclidean_cartesian_set R a b A B.
have hCubes:EF=@euclidean_open_unit_cube R (a+b)%N.
  apply:funext=>x;apply:propext;exact:iff_sym (@euclidean_open_unit_cube_split R a b x).
have hEF:measure_measurable (@euclidean_lebesgue_measure R (a+b)%N) EF.
  by rewrite hCubes;exact:simplex_cube_source_measurable.
pose Domain:=@euclidean_cartesian_set R a b (Full a) (Full b).
pose hDomain:=@current_cartesian_domain_open R a b (Full a) (Full b) (hFull a) (hFull b).
rewrite /current_ambient_cartesian_product /simplex_cube_source_current
  -(@open_euclidean_characteristic_current_full R h2 a A (@simplex_cube_source_measurable R a))
  -(@open_euclidean_characteristic_current_full R h2 b B (@simplex_cube_source_measurable R b)).
rewrite (@current_cartesian_euclidean_characteristic R h2 a b
  (Full a) (Full b) (hFull a) (hFull b) A B
  (@simplex_cube_source_measurable R a) (@simplex_cube_source_measurable R b) hEF).
rewrite (@euclidean_characteristic_domain_transport R h2 (a+b)%N Domain
  (Full (a+b)%N) hDomain (hFull (a+b)%N) (@current_cartesian_full_domain R a b) EF hEF)
  open_euclidean_characteristic_current_full.
have hSets:=@open_euclidean_characteristic_set_equal R h2 (a+b)%N
  (Full (a+b)%N) (hFull (a+b)%N) EF (@euclidean_open_unit_cube R (a+b)%N)
  hEF (@simplex_cube_source_measurable R (a+b)%N) hCubes.
by rewrite !open_euclidean_characteristic_current_full in hSets.
Qed.

(** Source for [simplex_cube_current_zero]: the original
    empty cube carries the actual nonzero
    Euclidean zero-current, supporting the base case
    in 4.1.27, p. 384. Its current
    is the original point current at the
    sole zero-dimensional vector. *)
Theorem simplex_cube_current_zero (R:realType) (h2:(1+1:R)!=0):
  @simplex_cube_source_current R h2 0%N=
    @dirac_current R h2 0%N (fun _=>True)
      (fun x (_:True)=>norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R 0%N)) x) 0.
Proof.
have hCube:@euclidean_open_unit_cube R 0%N=(fun _=>True).
  apply:funext=>x;apply:propext;split;first by [].
  move=>_ i;by case:i.
have hWhole:measure_measurable (@euclidean_lebesgue_measure R 0%N) (fun _=>True).
  have hOriginal:=@simplex_cube_source_measurable R 0%N.
  by rewrite hCube in hOriginal.
have hSets:=@open_euclidean_characteristic_set_equal R h2 0%N (fun _=>True)
  (fun x (_:True)=>norm_full_domain_interior
    (inner_norm (@euclidean_inner_productP R 0%N)) x)
  (@euclidean_open_unit_cube R 0%N) (fun _=>True)
  (@simplex_cube_source_measurable R 0%N) hWhole hCube.
rewrite !open_euclidean_characteristic_current_full in hSets.
rewrite /simplex_cube_source_current hSets euclidean_characteristic_current_whole.
exact:euclidean_fundamental_current_point.
Qed.

(** Source for [simplex_cube_current_one]: the original
    one-coordinate cube current is [0,1],
    the time segment in the point-join
    recursion of 4.1.11, p. 365,
    used in 4.1.27, p. 384. *)
Theorem simplex_cube_current_one (R:realType) (h2:(1+1:R)!=0):
  @simplex_cube_source_current R h2 1%N=@current_join_time_segment R h2.
Proof.
pose B:set (R_n R 1%N):=(@euclidean_one_project R) @^-1`
  (`]0,1[:set (real_line_metric R)).
have hCube:@euclidean_open_unit_cube R 1%N=B.
  apply:funext=>x;apply:propext;rewrite /B /preimage /= in_itv /=.
  exact:euclidean_open_unit_cube_one.
have hInterval:=@scalar_oriented_segment_interval_current R h2 0 1 ltr01.
have hDomain:@ScalarSegmentCoordinateValues.scalar_segment_full_domain R 0 1=
  @current_join_time_segment_domain R by exact:Prop_irrelevance.
rewrite hDomain in hInterval.
change (@current_join_time_segment R h2=
  @euclidean_characteristic_current R h2 1%N B
    (@scalar_segment_interval_measurable R 0 1)) in hInterval.
have hSets:=@open_euclidean_characteristic_set_equal R h2 1%N (fun _=>True)
  (fun x (_:True)=>norm_full_domain_interior
    (inner_norm (@euclidean_inner_productP R 1%N)) x)
  (@euclidean_open_unit_cube R 1%N) B (@simplex_cube_source_measurable R 1%N)
  (@scalar_segment_interval_measurable R 0 1) hCube.
rewrite !open_euclidean_characteristic_current_full in hSets.
exact:eq_trans hSets (esym hInterval).
Qed.

(** Federer (1969), 3.2.36, p. 273: the actual scalar coarea
    integral for the positive first-distance portion of a product tube. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanBlockCoordinates EuclideanCartesianMap CompactHausdorffMetric CompactSetDistanceProfile
  EuclideanProductPositiveStripCoarea EuclideanProductTubeFibreMass ScalarRestrictedFibreCoarea
  EuclideanLebesgueDimensions HausdorffMeasure LebesgueScalarMeasure MetricSetDistanceUP
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension MeasureIntegralGraphEquivalence
  MeasureSubsetIntegral SubsetIntegralTotalAgreement RealOpenIntervals ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_product_radial_coarea]: the first two
    equalities of Federer 3.2.36, p. 273, on the positive
    first-distance part of the actual product tube. Actual distance
    coarea, scalar transport and the proved full rectifiable-product
    fibre identity discharge every geometric and integration premise.
    No finite-mass, full-dimensionality or positive second dimension
    hypothesis is added. The zero first-distance slice is treated
    separately, as in the printed proof. *)
Theorem euclidean_product_radial_coarea (R:realType) k n
    (A:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R k.+1)))
    (B:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)))
    (d:inner_metric_space (@euclidean_inner_productP R (k.+1+n))->R) (r:R):
  is_inner_convex (val A) ->
  @is_metric_set_distance R (inner_metric_space (@euclidean_inner_productP R (k.+1+n)))
    (euclidean_cartesian_set (val A) (val B)) d ->
  let f:=fun z:inner_metric_space (@euclidean_inner_productP R (k.+1+n))=>
    compact_set_distance_profile A (euclidean_block_split z).1 in
  is_measure_subset_integral (@lebesgue_scalar_measure R) (real_open_interval 0 r)
    (partial_function_total (fun s:R=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R k.+1)) k
        [set x|compact_set_distance_profile A x=s]*
      @euclidean_lebesgue_measure R n
        [set y|(compact_set_distance_profile B y<Num.sqrt (r^+2-s^+2))%R]
        :extended_real_line R)%E))
    (@euclidean_lebesgue_measure R (k.+1+n) ([set z|0<f z<r] `&` [set z|d z<r])).
Proof.
move=>hConvex hD f.
have hI:=@euclidean_product_positive_strip_coarea R k.+1 n A (val B) d r
  (ltn0Sn k) hD.
have hDegree:(k.+1+n-1)%N=(k+n)%N by rewrite addSn subn1.
rewrite hDegree in hI.
have hScalar:=restricted_scalar_fibre_integral hI.
apply:(@subset_integral_total_agreement R R (@lebesgue_scalar_measure R)
  (real_open_interval 0 r)
  (fun s:R=>(@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (k.+1+n)))
    (k+n) [set z|f z=s /\d z<r]:extended_real_line R))
  (fun s:R=>(@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k.+1)) k
    [set x|compact_set_distance_profile A x=s]*
    @euclidean_lebesgue_measure R n
    [set y|(compact_set_distance_profile B y<Num.sqrt (r^+2-s^+2))%R]:extended_real_line R)%E)
  _ _).1 hScalar.
move=>s [hs hsr].
exact:(@euclidean_product_tube_fibre_mass R k n A B d s r hConvex hD hs hsr).
Qed.

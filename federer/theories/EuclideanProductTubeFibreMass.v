(** Federer (1969), 3.2.36, p. 273:
    actual product-tube fibre masses follow
    from the proved rectifiable product theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanBlockCoordinates EuclideanCartesianMap EuclideanProductTubeFibres EuclideanBoundedRectifiability
  CompactSetDistanceProfile CompactHausdorffMetric CompactMetricBounded ConvexDistanceLevelCauchy
  MetricSetDistanceUP MetricSetDistanceContinuity RealMetricBackground TopologicalBorel
  RectifiableSetUP RectifiableCartesianProduct RectifiableCartesianProductUP
  HausdorffMeasure EuclideanHausdorffLebesgue EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_product_tube_fibre_mass]: the
    actual fibre-mass identity in the second
    displayed equality of Federer 3.2.36,
    p. 273. The first distance level
    is genuinely k-rectifiable by 3.2.35;
    the actual second tube is Borel and
    genuinely n-rectifiable by its bounded
    identity parametrization. Thus every premise
    of 3.2.23 is discharged. Whole fibres,
    zero second dimension and k=0 counting
    fibres are retained. The degree k+n
    equals the printed (k+1+n)-1. *)
Theorem euclidean_product_tube_fibre_mass (R:realType) k n
    (A:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R k.+1)))
    (B:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)))
    (d:inner_metric_space (@euclidean_inner_productP R (k.+1+n))->R) (s r:R):
  is_inner_convex (val A) ->
  @is_metric_set_distance R (inner_metric_space (@euclidean_inner_productP R (k.+1+n)))
    (euclidean_cartesian_set (val A) (val B)) d ->0<s ->s<r ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (k.+1+n))) (k+n)
    [set z:inner_metric_space (@euclidean_inner_productP R (k.+1+n))|
      compact_set_distance_profile A (euclidean_block_split z).1=s /\d z<r]=
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k.+1)) k
      [set x|compact_set_distance_profile A x=s]*
      @euclidean_lebesgue_measure R n
      [set y|(compact_set_distance_profile B y<Num.sqrt (r^+2-s^+2))%R])%E.
Proof.
move=>hConvex hD hs hsr.
pose X:=inner_metric_space (@euclidean_inner_productP R k.+1).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose W:set X:=[set x|compact_set_distance_profile A x=s].
pose T:set Y:=[set y|(compact_set_distance_profile B y<Num.sqrt (r^+2-s^+2))%R].
have hWRect:=(@convex_distance_level_cauchy R k (val A) (compact_set_distance_profile A) s
  (set_valP A).2 hConvex (compact_metric_diameter_finite A)
  (compact_set_distance_profile_specification A) hs).1.
have hWClosed:closed W.
  change (closed ((compact_set_distance_profile A:X->real_line_metric R) @^-1` [set s])).
  apply:preimage_closed.
  - move=>x _; exact:(@metric_set_distance_continuous R X (val A) (compact_set_distance_profile A)
      (compact_set_distance_profile_specification A) x).
  - apply:accessible_closed_set1; apply:hausdorff_accessible; exact:metric_hausdorff.
have hWBorel:=closed_borel_set hWClosed.
have hr:0<r:=lt_trans hs hsr.
have hRoot:0<Num.sqrt (r^+2-s^+2).
  by rewrite sqrtr_gt0 subr_gt0 (ltr_sqr (ltW hs) (ltW hr)).
have [_ [hTBorel hTMeasureRect]]:=@compact_distance_tube_rectifiable R n B
  (Num.sqrt (r^+2-s^+2)) hRoot.
have [_ hIdentity]:=@federer_3_2_23 R k n k.+1 n W T hWRect hWBorel hTMeasureRect hTBorel.
have hMass:=@rectifiable_cartesian_total_mass_from_identity R k n k.+1 n W T hIdentity.
have hTVolume:=(@euclidean_hausdorff_spherical_lebesgue R n T).1.
rewrite (@euclidean_product_tube_first_distance_fibre R k.+1 n A B d s r hD (ltW hs) hsr).
by rewrite hMass hTVolume.
Qed.

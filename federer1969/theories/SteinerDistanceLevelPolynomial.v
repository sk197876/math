(** Federer (1969), 3.2.36, p. 273:
    every whole positive distance level has
    the printed polynomial Hausdorff mass. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  MetricSetDistanceUP SteinerTubePolynomial ConvexSteinerTubeFormula SteinerDistanceLevelAverage
  SteinerDistanceLevelCoefficient ConvexIntrinsicVolumeIntegrals IntegralGeometricGauge
  ProjectionBeta EuclideanBallVolume HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_distance_level_polynomial]:
    the whole level-mass substitution in
    Federer 3.2.36, p. 273.
    For every original nonempty bounded convex
    source and every positive distance value,
    its entire level has mass equal to
    the differentiated Steiner polynomial. The
    already proved actual Cauchy/projection formula
    gives pointwise equality at every positive
    radius; no a.e.-only differentiation inference
    or auxiliary derivative hypothesis is used.
    All positive ambient dimensions remain,
    including counting measure in the line. *)
Theorem convex_distance_level_polynomial (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))) d (t:R):
  S!=set0 ->is_inner_convex S ->metric_set_bounded S ->is_metric_set_distance S d ->(0<t)%R ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k.+1)) k [set x|d x=t]=
    \sum_(i:'I_k.+1) @integral_geometric_gauge R k.+1 i
      (leq_trans (steiner_dimension_guard i) (leqnSn k)) 1 S*
      ((k.+1-i)%:R*euclidean_unit_ball_volume R (k.+1-i)*t^+(k-i))%R%:E.
Proof.
move=>hNonempty hS hBound hD ht.
have hAverage:=@steiner_distance_level_average R k S d t
  (@convex_steiner_tube_formula R k) hNonempty hS hBound hD ht.
have hNonnegative (i:'I_k.+1):0<=
    (euclidean_unit_ball_volume R (k-i)*t^+(k-i))%R%:E*
      ((@projection_beta R k.+1 i (leq_trans (steiner_dimension_guard i) (leqnSn k)) 1 /
        @projection_beta R k i (steiner_dimension_guard i) 1)%R%:E*
      @integral_geometric_gauge R k.+1 i (leq_trans (steiner_dimension_guard i) (leqnSn k)) 1 S).
  apply:mule_ge0.
  - rewrite lee_fin; apply:mulr_ge0; first exact:ltW (euclidean_unit_ball_volumeE R (k-i)).2.
    apply:exprn_ge0; exact:ltW ht.
  - apply:mule_ge0.
    + rewrite lee_fin; apply:divr_ge0; apply:ltW.
      * exact:(@projection_beta_positive R k.+1 i (leq_trans (steiner_dimension_guard i) (leqnSn k)) 1 (lexx 1)).
      * exact:(@projection_beta_positive R k i (steiner_dimension_guard i) 1 (lexx 1)).
    + exact:(@convex_intrinsic_volume_nonnegative_finite R k.+1 i
        (leq_trans (steiner_dimension_guard i) (leqnSn k)) 1 S hNonempty hS hBound (lexx 1)).1.
rewrite hAverage ge0_sume_distrr; last by move=>i _; exact:hNonnegative.
apply:eq_bigr=>i _.
have hReorder (a b c v:R) (z: \bar R):
    a%:E*((b*v)%R%:E*(c%:E*z))=(a*b*c*v)%R%:E*z.
  rewrite !EFinM !muleA -!EFinM; congr (_%:E*z); ring.
rewrite hReorder (@steiner_distance_level_coefficient R k i (steiner_dimension_guard i)).
exact:muleC.
Qed.

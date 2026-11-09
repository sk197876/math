(** Federer (1969), 3.3.19, pp. 302–306:
    the original compact circular-disc example, using only
    the public laws of its opaque original objects. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces EuclideanInnerProduct InnerMetric
  CircularDiscTreeUP CircularDiscTreeSealed CircularDiscLimitUP CircularDiscLimitSealed
  CircularDiscTreeTopology CircularDiscExactMass CircularDiscPureUnrectifiability
  CircularDiscRadialMapSealed CircularDiscAngularTailDensity CircularDiscConicalUpperDensity
  CircularDiscGrossNull CircularDiscUpperDensityHalf CircularTrigonometrySealed
  PlanarUnitCircleGeometry PartialFunctionUP StructureCone MetricDensities MeasureRestriction
  MeasureAlmostUP RectifiableSetUP HausdorffMeasure IntegralGeometricMeasure ProjectionBeta
  ProjectionMeasure EuclideanProjectionSpace EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_3_19]: the principal conclusions
    of 3.3.19, pp. 302–306, for the ACTUAL
    original sealed disc intersection. All convex exponents,
    original projections, conical planes and apertures remain.
    The actual upper-density value is proved at every
    original point, strengthening the printed almost-everywhere
    assertion. The accompanying modules prove the original
    level-piece, restriction, angular and auxiliary assertions.
    Q denotes convex generators, as printed on p. 304. *)
Theorem federer_3_3_19 (R:realType):
  let E:=inner_metric_space (@euclidean_inner_productP R 2) in
  let A:=@CircularDiscLimit.value R in
  let H:=@hausdorff_measure R [the metricType R of E] 1 in
  let pi:=@CircularTrigonometry.half_period R in
  A!=set0 /\compact A /\H A=(2:R)%:E /\
  (forall t: \bar R,(1<=t)%E ->
    ((@projection_beta R 2 1 (leqnSn 1) t)%:E*
      @convex_integral_geometric_measure R 2 1 (leqnSn 1) t A=(2:R)%:E)%E) /\
  @convex_integral_geometric_measure R 2 1 (leqnSn 1) 1 A=pi%:E /\
  is_purely_measure_m_unrectifiable H 1 A /\
  measure_almost_everywhere_on H A [set a:E|forall (V:G (R_n R 2) 1) (s:R),
    0<s ->s<1 ->((1/(2*pi))%:E<=upper_metric_density 1
      (measure_restrict H (A `&` structure_cone V a +oo s)) a)%E] /\
  (forall p:euclidean_projection_space R 2 1,
    euclidean_lebesgue_measure 1 (euclidean_projection_linear p @` A)=0%E) /\
  @gross_measure R 2 1 A=0%E /\
  forall a:E,A a ->upper_metric_density 1 (measure_restrict H A) a=((1:R)/2)%:E.
Proof.
move=>E A H pi.
pose T:=@CircularDiscTree.centres R.
have hT:=@CircularDiscTree.laws R.
have hA:=@CircularDiscLimit.laws R.
pose eta:=@CircularDiscRadialMap.map R T hT.
have hEta j:=@CircularDiscRadialMap.laws R T hT j.
have [hNonempty hCompact]:=@circular_disc_limit_nonempty_compact R T hT A hA.
split;first exact:hNonempty.
split;first exact:hCompact.
split;first exact:(@circular_disc_hausdorff_mass R T hT A hA).
split;first exact:(@circular_disc_normalized_convex_mass R T hT A hA).
split;first exact:(@circular_disc_first_convex_mass R T hT A hA).
split;first exact:(@circular_disc_purely_unrectifiable R T A hT hA).
split;first exact:(@circular_disc_conical_upper_density_almost R T hT A hA eta hEta).
split;first exact:(@CircularDiscProjectionNull.circular_disc_every_projection_null R T hT A hA eta hEta).
split;first exact:(@circular_disc_gross_measure_zero R T hT A hA eta hEta).
exact:(@circular_disc_upper_density_half R T hT A hA).
Qed.

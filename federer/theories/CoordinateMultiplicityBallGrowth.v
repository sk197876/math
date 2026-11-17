(** Federer (1969), 3.4.8(13), p. 336:
    uniform bounds on the original coordinate multiplicities
    give a uniform Hausdorff bound on ball sections.
    Apply the already proved 3.2.27 on finite
    measurable pieces, then pass to the whole section
    by the proved increasing finite-mass exhaustion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric ExteriorIndices
  CoordinateProjection ProjectionMultiplicityNullRemainder RectifiableSetUP RectifiableCoordinateMassUP
  RectifiableCoordinateProjectionBounds CountablyMeasureRectifiableOperations
  CountablyMeasureRectifiableFinitePieceBound MappingMultiplicity MappingMultiplicityLaws CurveFiniteMultiplicity
  BoundedSupportIntegralComparison EuclideanLebesgueDimensions EuclideanClosedBallGrowth
  MetricClosedBalls HausdorffMeasure HausdorffClosedCoverAgreement MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureFiniteClosure BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_multiplicity_hausdorff_ball_growth]:
    the projection estimate in 3.4.8(13), p. 336,
    with a coordinate ball as measurable support.
    The set may initially have infinite Hausdorff mass;
    only countable measure rectifiability is required. *)
Theorem coordinate_multiplicity_hausdorff_ball_growth (R:realType) n m (hmn:(m<=n)%N)
    (S:set (R_n R n)) (c:Lambda n m->R)
    (x:inner_metric_space (@euclidean_inner_productP R n)) (r:R):
  (forall lambda,0<=c lambda) ->
  is_countably_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m S ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) S ->
  (forall lambda,measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    [set y|(@mapping_multiplicity R [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
      (R_n R m) (@coordinate_projection R n m lambda) S y<=(c lambda)%:E)%E]) ->
  0<r ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m
    (S `&` metric_closed_ball x r)<=
    ((\sum_lambda c lambda)*@euclidean_closed_unit_volume R m*r^+m)%:E)%E.
Proof.
move=>hC hRect hSMeas hCaps hr.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R m).
pose H:=@hausdorff_measure R X m.
pose beta:=@euclidean_lebesgue_measure R m.
have hH:=@hausdorff_measure_is_measure R X m.
have hBeta:=@euclidean_lebesgue_is_measure R m.
pose E:=S `&` metric_closed_ball x r.
have hES:E `<=` S by move=>z hz;exact:hz.1.
have hECount:=@countably_measure_rectifiable_subset R X H m S E hES hRect.
have hEMeas:measure_measurable H E.
  apply:(measure_measurable_intersection hH hSMeas).
  apply:(@borel_regular_borel_measurable R X H hH (@hausdorff_measure_borel_regular R X m)).
  exact:(@closed_borel_set X (metric_closed_ball x r) (@metric_closed_ball_closed R X x r)).
apply:(@countably_measure_rectifiable_finite_piece_bound R n m E _ hECount hEMeas).
move=>W hWE hWRect hWMeas.
have [a [hA [_ hUpper]]]:=@rectifiable_coordinate_integrals_exist R m n hmn W hWRect hWMeas.
have hCoordinate lambda:(a lambda<=c lambda*@euclidean_closed_unit_volume R m*r^+m)%R.
  pose p:=@coordinate_projection R n m lambda.
  pose B:=@metric_closed_ball R Y (p x) r.
  have hBMeas:measure_measurable beta B.
    apply:(@borel_regular_borel_measurable R Y beta hBeta (@euclidean_lebesgue_borel_regular R m)).
    exact:(@closed_borel_set Y B (@metric_closed_ball_closed R Y (p x) r)).
  have hWCap:measure_almost_everywhere beta
      [set y|(@mapping_multiplicity R (Choice.clone X _) Y p W y<=(c lambda)%:E)%E].
    apply:(measure_almost_everywhere_mono hBeta _ (hCaps lambda))=>y hy.
    apply:(le_trans _ hy).
    exact:(@mapping_multiplicity_subset_bound R (Choice.clone X _) Y p W S
      (fun z hz=>hES z (hWE z hz)) y).
  have hSupport y:~B y ->@mapping_multiplicity R (Choice.clone X _) Y p W y=0%E.
    move=>hNot;apply:(@mapping_multiplicity_zero_iff R (Choice.clone X _) Y p W y).2.
    move=>[z hz hpz];apply:hNot;rewrite -hpz.
    exact:(le_trans (@coordinate_projection_metric_contraction R n m lambda x z) (hWE z hz).2).
  have hCNonnegative:(0<=(c lambda)%:E)%E by rewrite lee_fin;exact:hC lambda.
  have hBound:=@bounded_support_integral_comparison R (Choice.clone Y _) beta B
    (fun y=>@mapping_multiplicity R (Choice.clone X _) Y p W y) (c lambda)%:E (a lambda)%:E
    hBeta hBMeas hCNonnegative (hA lambda) hSupport hWCap.
  rewrite /B /beta (euclidean_closed_ball_measure (p x:Y) hr) -EFinM lee_fin mulrA in hBound.
  exact:hBound.
apply:(le_trans hUpper).
rewrite lee_fin mulr_suml mulr_suml.
apply:ler_sum=>lambda _;exact:hCoordinate lambda.
Qed.

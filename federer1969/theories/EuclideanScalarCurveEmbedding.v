(** Federer (1969), 3.2.6, pp. 245–246: identify
    the scalar target with the one-coordinate Euclidean
    line before applying the first formula to the signed
    scalar substitution argument. All identities preserve
    actual derivative graphs and actual counting fibres. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  EuclideanOneCoordinate EuclideanOneNormDifferential RealMetricBackground ExtendedRealOrderTopology
  NormedCurveDerivativeUP NormedCurveDerivativeIntegrands RealCurveDerivativeUP RealCurveDerivativeIntegrands
  EuclideanCurveSpeedMeasure LocallyAbsolutelyContinuousCurve MetricCurveAbsoluteContinuityBasic
  PartialFunctionUP MappingMultiplicity CountingMeasure MeasurePushforward LebesgueScalarMeasure
  EuclideanHausdorffLebesgue EuclideanLebesgueDimensions EuclideanLebesgue HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_scalar_curve_derivative_iff]: the
    case n=1 of Federer 3.2.6, p. 245. The actual
    vector derivative under R=R^1 is equivalent to the
    actual scalar derivative at its sole coordinate. *)
Lemma euclidean_scalar_curve_derivative_iff (R:realType) (f:R->R) a (v:R_n R 1):
  has_normed_curve_derivative (inner_norm (@euclidean_inner_productP R 1))
    (fun t=>euclidean_one_embed (f t)) a v <->
  has_real_curve_derivative f a (euclidean_one_project v).
Proof.
have hNorm h:inner_norm (@euclidean_inner_productP R 1)
    (h^-1*:(euclidean_one_embed (f (a+h))-euclidean_one_embed (f a))-v)=
    `|(f (a+h)-f a)/h-euclidean_one_project v|.
  rewrite euclidean_one_norm_coordinate /euclidean_one_embed /euclidean_one_project !ffunE.
  by rewrite mulrC.
split=>hD e he; have [d [hd hb]]:=hD e he; exists d; split=>// h hh.
- have hv:=hb h hh; by rewrite hNorm in hv.
- by rewrite hNorm; exact (hb h hh).
Qed.

(** Source for [euclidean_scalar_curve_speed_graph]: the
    scalar |f'| in Federer 3.2.6, p. 245,
    agrees with the actual Euclidean speed, including
    equality of their partial domains. *)
Lemma euclidean_scalar_curve_speed_graph (R:realType) (f:R->R) a z:
  partial_function_graph (euclidean_curve_speed (fun t=>euclidean_one_embed (f t))) a z <->
  partial_function_graph (real_curve_absolute_derivative_integrand f) a z.
Proof.
split.
- move=>[v [hv hVal]]; exists (euclidean_one_project v); split.
  + exact ((euclidean_scalar_curve_derivative_iff f a v).1 hv).
  + by rewrite euclidean_one_norm_coordinate in hVal.
- move=>[v [hv hVal]]; exists (euclidean_one_embed v); split.
  + apply:(euclidean_scalar_curve_derivative_iff f a (euclidean_one_embed v)).2.
    by rewrite euclidean_one_embedK.
  + by rewrite euclidean_one_norm_coordinate /euclidean_one_embed ffunE.
Qed.

(** Source for [euclidean_one_scalar_isometry]: supporting
    scalar metric identification in Federer 3.2.6,
    p. 245; no change of norm or normalization occurs. *)
Lemma euclidean_one_scalar_isometry (R:realType) (x y:real_line_metric R):
  mdist (euclidean_one_embed x) (euclidean_one_embed y)=mdist x y.
Proof.
by rewrite inner_metric_distanceE euclidean_one_norm_coordinate
  /euclidean_one_embed !ffunE real_line_metric_distanceE.
Qed.

(** Source for [euclidean_scalar_curve_absolute_continuity]:
    the scalar target in Federer 3.2.6, p. 245,
    satisfies precisely the same finite-family absolute
    continuity laws under the isometric identification R=R^1. *)
Lemma euclidean_scalar_curve_absolute_continuity (R:realType) (f:R->R):
  is_locally_absolutely_continuous_curve (f:R->real_line_metric R) ->
  is_locally_absolutely_continuous_curve (fun t=>euclidean_one_embed (f t)).
Proof.
move=>hAC a b hab.
apply:(@metric_absolute_continuity_lipschitz_postcomposition R [the metricType R of real_line_metric R]
  [the metricType R of inner_metric_space (@euclidean_inner_productP R 1)] (@euclidean_one_embed R) f 1 a b ler01).
- by move=>x y; rewrite euclidean_one_scalar_isometry mul1r.
- exact (hAC a b hab).
Qed.

(** Source for [euclidean_scalar_curve_multiplicity]: the
    same actual scalar fibre count under R=R^1 in
    Federer 3.2.6, pp. 245–246, including infinite fibres. *)
Lemma euclidean_scalar_curve_multiplicity (R:realType) (f:R->R) (A:set (real_line_metric R)) y:
  @mapping_multiplicity R [the choiceType of real_line_metric R] (R_n R 1)
    (fun t=>euclidean_one_embed (f t)) A (euclidean_one_embed y)=
  @mapping_multiplicity R [the choiceType of real_line_metric R] R f A y.
Proof.
rewrite /mapping_multiplicity; congr (counting_measure _).
apply/seteqP; split=>x [hx he]; split=>//.
- exact (can_inj (@euclidean_one_embedK R) he).
- by rewrite he.
Qed.

(** Source for [euclidean_one_hausdorff_pushforward]: the
    scalar target measure in Federer 3.2.6, p. 245,
    is L^1 by 2.10.35, with the precise first-coordinate
    product convention of 2.6.5. *)
Lemma euclidean_one_hausdorff_pushforward (R:realType):
  @hausdorff_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R 1)] 1=
  measure_pushforward (@euclidean_one_embed R) (@lebesgue_scalar_measure R).
Proof.
apply:funext=>A; rewrite (euclidean_hausdorff_spherical_lebesgue A).1.
change (@positive_euclidean_lebesgue_measure R 0 A=
  measure_pushforward (@euclidean_one_embed R) (@lebesgue_scalar_measure R) A).
by rewrite positive_euclidean_lebesgue_first.
Qed.

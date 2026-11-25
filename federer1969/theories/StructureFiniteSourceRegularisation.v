(** Federer (1969), 3.3.15, p. 299: actual finite
    regularisation of the original outer measure restricted to W. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric StructureConeUP StructureEuclideanFiniteRadon
  MetricClosedBalls MetricDensities PositiveRadiusLimitCongruence
  MeasureUP MeasureBasic MeasureRestriction MeasureFiniteClosure
  MeasureDerivationContext BorelRegularisationUP BorelRegularisation BorelRegularisationBasic
  BorelRegularMeasureUP TopologicalBorel MeasurableBorelFamily RadonMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_finite_source_regularisation]: the actual
    Radon measure defined by the printed Borel-cover infimum in
    Federer 3.3.15, p. 299. Original W need not be measurable.
    The actual sealed regularisation retains Borel-set values,
    total original mass and domination on every original subset.
    Actual closed-ball values give EVERY-POINT equality of the
    original metric upper densities. Every auxiliary measure stays local. *)
Theorem structure_finite_source_regularisation (R:realType) n m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (W:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_structure_measure phi ->phi W< +oo ->
  exists psi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R,
    is_borel_regularisation (measure_restrict phi W) psi /\
    is_derivation_measure psi /\is_radon_measure psi /\psi setT=phi W /\
    (forall S,borel_set S ->psi S=phi (W `&` S)) /\
    (forall S,phi (W `&` S)<=psi S) /\
    (forall a,upper_metric_density m psi a=
      upper_metric_density m (measure_restrict phi W) a).
Proof.
move=>hStructure hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=measure_restrict phi W.
have hMu:is_measure mu:=measure_restrict_is_measure hStructure.1 W.
have hPhiBorel S:borel_set S ->measure_measurable phi S.
  apply:(@open_measurable_implies_borel_measurable R [the topologicalType of X] phi hStructure.1).
  move=>U hU.
  have hClosed:=hStructure.2 _ (open_closedC hU).
  have hOpen:=measure_measurable_complement hClosed; by rewrite setCK in hOpen.
have hMuBorel S:borel_set S ->measure_measurable mu S.
  move=>hS; exact:(@measure_restrict_measurable R [the choiceType of X] phi W S (hPhiBorel S hS)).
pose psi:=@borel_regularisation R [the topologicalType of X] mu.
have hReg:is_borel_regularisation mu psi:=borel_regularisation_laws mu.
have hPsi:is_measure psi:=borel_regularised_measure_is_measure hMu.
have hRegular:is_borel_regular_measure psi:=borel_regularised_measure_borel_regular hMu hMuBorel.
have hValue S:borel_set S ->psi S=phi (W `&` S).
  move=>hS; rewrite /psi; exact:(@borel_regularised_measure_borel_value R
    [the topologicalType of X] mu hMu S hS).
have hTotal:psi setT=phi W by rewrite (hValue setT (open_borel_set openT)) setIT.
have hTotalFinite:psi setT< +oo by rewrite hTotal.
have hClass:is_derivation_measure psi.
  constructor; [exact:hPsi|exact:hRegular|].
  move=>S _; exact:le_lt_trans (@measure_mono R _ psi hPsi S setT (subsetT S)) hTotalFinite.
have hRadon:=@structure_euclidean_finite_borel_radon R n psi hPsi hRegular hTotalFinite.
have hDomination S:phi (W `&` S)<=psi S.
  exact:(@borel_regularisation_dominates R [the topologicalType of X] mu psi hMu hReg S).
have hDensity a:upper_metric_density m psi a=upper_metric_density m mu a.
  rewrite /upper_metric_density.
  apply:(positive_radius_limits_congr _).1=>r hr.
  rewrite /metric_ball_density (hValue _ (closed_borel_set (@metric_closed_ball_closed R [the metricType R of X] a r))).
  by [].
exists psi; split; first exact:hReg.
split; first exact:hClass.
split; first exact:hRadon.
split; first exact:hTotal.
split; first exact:hValue.
split; first exact:hDomination.
exact:hDensity.
Qed.

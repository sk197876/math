(** Federer (1969), 4.1.25, p. 383: the bounded
    almost-everywhere convergence of smoothed differentials uses
    the Lebesgue-point theorem 2.9.9, pp. 156–157,
    and the centered-ball relation of 2.8.18, p. 152.
    The actual ambient Lebesgue measure is locally finite;
    its total mass need not be finite. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations
  FiniteCoordinates LinearBasis EuclideanInnerProduct InnerNorm
  HilbertFormCompactness InnerMetric InnerOwnNormTopology
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  EuclideanNormClosedBalls EuclideanNormCountableBase CountableBaseDenseSet
  NormDirectionalLimitation DirectionalLimitationUP MetricClosedBalls
  MetricBoundedUnion MeasureUP MeasureBasic BorelRegularMeasureUP
  MeasureDerivationContext CoveringFamilyUP CoveringRelationUP
  CenteredBallRelations CenteredBallVitali PartialFunctionUP PartialFunctionBasic
  PartialFunctionPostcomposition PartialZeroExtension ExtendedRealOrderTopology
  MeasureAlmostUP MeasurableFunctionUP MeasureSubsetIntegral
  MeasureIntegralGraphEquivalence MeasureLebesgueSet NormedLebesguePoints
  BoundedVectorNormSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LebesgueActionLebesguePoints.
Variable R : realType.
Variable m : nat.
Local Notation X := (R_n R m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation mu := (@euclidean_lebesgue_measure R m).
Local Notation hm := (euclidean_lebesgue_is_measure R m).

(** Source for [current_lipschitz_lebesgue_action_derivation_context]:
    the standing measure and centered-ball hypotheses of
    2.9.9, pp. 156–157, used in the first proof
    of 4.1.25, p. 383. This is the original
    norm presentation of Euclidean space, in every dimension. *)
Lemma current_lipschitz_lebesgue_action_derivation_context :
  @is_measure_derivation_context R [the metricType R of XT] mu
    (@centered_closed_ball_relation R [the metricType R of XT]).
Proof.
have hRegular : @is_borel_regular_measure R [the topologicalType of XT] mu.
  constructor.
  - exact: euclidean_distribution_measure_open.
  - move=>A.
    have [B [hAB [hB hMeasure]]] :=
      borel_regular_cover (euclidean_lebesgue_borel_regular R m) A.
    exists B; split=>//; split=>//.
    exact: (inner_own_norm_borel_iff (@euclidean_inner_productP R m) B).1 hB.
have hBounded A : @metric_set_bounded R [the metricType R of XT] A ->
    (mu A < +oo)%E.
  move=>hA.
  have [r [hr hInside]] := @metric_bounded_distance_bound R
    [the metricType R of XT] A 0 hA.
  have hCompact:=@euclidean_norm_closed_ball_compact R m (0:XT) r.
  apply:(le_lt_trans (@measure_mono R [the choiceType of XT] mu hm A
    (@metric_closed_ball R [the metricType R of XT] 0 r) hInside)).
  exact:(@euclidean_distribution_measure_compact_finite R m
    (@metric_closed_ball R [the metricType R of XT] 0 r) hCompact).
have hMeasure : @is_derivation_measure R [the metricType R of XT] mu.
  constructor.
  - exact:hm.
  - exact:hRegular.
  - exact:hBounded.
pose V := @centered_closed_ball_relation R [the metricType R of XT].
have hContext : is_covering_theory_context (covering_relation_image V setT) mu.
  constructor=>//.
  - exact: hm.
  - move=>B [x [_ [r [hR ->]]]]; exact:metric_closed_ball_closed.
  - move=>W hW; exact:euclidean_distribution_measure_open hW.
have [B hB] := @euclidean_norm_countable_open_base R m.
have hSeparable := @countable_open_base_dense_set XT 0 B hB.
have hThird : (0 < ((1:R)/3) <= 1/3)%R.
  apply/andP; split; last exact:lexx.
  by rewrite divr_gt0 // ltr0n.
have [zeta hDirectional] := @finite_norm_directional_limitation R X NX hNX
  m (@coordinate_basis R m) (@coordinate_basisP R m) (1/3) hThird.
pose C : set (set XT) := [set setT].
have hCover : (\bigcup_(A in C) A) = setT.
  apply/seteqP; split=>x _; first exact I.
  by exists setT.
have hLimited A : C A -> exists (xi : \bar R) (eta : R) (k : nat),
    is_directionally_limited_at A xi eta k.
  move=>hA; change (A=setT) in hA; rewrite hA.
  by exists +oo%E,(1/3),zeta.
constructor; first exact:hMeasure.
exact: (@federer_2_8_18 R [the metricType R of XT] mu C
  hContext hSeparable (countable1 setT) hCover hLimited).
Qed.

(** Source for [current_lipschitz_lebesgue_action_bounded_lebesgue_points]:
    2.9.9, pp. 156–157, applied to each bounded
    directional derivative in 4.1.25, p. 383.
    Only the given target's countable dense set is used.
    There is no finite-total-Lebesgue-mass assumption. *)
Theorem current_lipschitz_lebesgue_action_bounded_lebesgue_points
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (C:set (real_norm_metric_space hNY))
    (v:X->real_norm_metric_space hNY) (L:R) :
  countable C -> dense C ->
  is_measure_measurable_function mu (partial_function_total v) ->
  (forall x,NY (v x)<=L) ->
  measure_almost_everywhere mu
    (@measure_lebesgue_set R [the metricType R of XT]
      [the metricType R of real_norm_metric_space hNY] mu
      (@centered_closed_ball_relation R [the metricType R of XT])
      (partial_function_total v)).
Proof.
move=>hCc hCd hMeas hBound.
apply: (@federer_2_9_9 R [the metricType R of XT] Y NY hNY mu
  (@centered_closed_ball_relation R [the metricType R of XT])
  (partial_function_total v) C
  current_lipschitz_lebesgue_action_derivation_context hMeas hCc hCd).
move=>A hABounded hAMeas.
have hFinite := derivation_measure_bounded_finite
  (derivation_context_measure current_lipschitz_lebesgue_action_derivation_context)
  hABounded.
have hFin : mu A \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative hm A)).
have hMass : mu A=(fine (mu A))%:E by rewrite fineK.
have [J hJ] := @bounded_vector_norm_subset_integral R XT Y NY hNY C
  mu hm A (fine (mu A)) L v hCc hCd hAMeas hMass hMeas hBound.
exists J.
apply: (@measure_integral_graph_equivalent R XT mu _ _ J%:E _ hJ)=>x y.
rewrite !partial_function_zero_extension_graph; split.
- move=>[[hx he]|hx]; last by right.
  left; split=>//; exists (v x); split=>//.
  exact:(real_total_integrand_graph _ _ _).1 he.
- move=>[[hx [z [hz he]]]|hx]; last by right.
  left; split=>//; apply/real_total_integrand_graph.
  by rewrite (hz:v x=z).
Qed.
End LebesgueActionLebesguePoints.

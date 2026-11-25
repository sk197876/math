(** Federer (1969), 2.9.19, p. 165: bound the two continuous-part interval
    masses by total variation. The continuous parts annihilate Lebesgue-null
    endpoints, so a closed interval has the same continuous- part masses as
    its interior even when g jumps at an endpoint. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength StieltjesIntegral
  StieltjesImageMeasures StieltjesInducedPairLaws StieltjesDerivationClass StieltjesContinuityPoints
  MeasureUP MeasureBasic MeasureDerivationContext AbsoluteContinuousPart AbsoluteContinuousPartBasic
  LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [scalar_continuous_part_singleton_null]: supporting
    endpoint-nullity step in the integral estimate of Federer 2.9.19, p.
    165, using the continuous-part nullity law of 2.9.1, p. 152, and scalar
    singleton length from 2.5.17, p. 111. *)
Lemma scalar_continuous_part_singleton_null (R : realType)
    (psi : set (real_line_metric R) -> \bar R) (x : R) : is_measure psi ->
  measure_continuous_part psi (@lebesgue_scalar_measure R) [set x]=0.
Proof.
move=> hm.
exact (@continuous_part_null R [the topologicalType of real_line_metric R]
  (@lebesgue_scalar_measure R) psi _ hm
  (@measure_continuous_part_specification R [the topologicalType of real_line_metric R]
    psi (@lebesgue_scalar_measure R)) [set x] (lebesgue_scalar_singleton x)).
Qed.

(** Source for [stieltjes_continuous_part_segment_bound]: direct bound
    underlying the final integral estimate in Federer 2.9.19, p. 165 Remove
    the null endpoints for both continuous parts, dominate them by psi+,psi-
    on the open interval, and use the open-interval variation bound of
    2.5.17. This holds for every a<=b without endpoint-continuity
    assumptions on g. *)
Lemma stieltjes_continuous_part_segment_bound (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) (a b : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim -> (a<=b)%R ->
  @measure_continuous_part R [the topologicalType of real_line_metric R] psip (@lebesgue_scalar_measure R) `[a,b]+
    @measure_continuous_part R [the topologicalType of real_line_metric R] psim (@lebesgue_scalar_measure R) `[a,b]<=
    curve_variation (g : R -> real_line_metric R) a b.
Proof.
move=> hg hp hab.
have [hCP hCM] := @stieltjes_induced_pair_derivation_class R g psip psim hg hp.
have hmP := derivation_measure_law hCP; have hmM := derivation_measure_law hCM.
have hmL := lebesgue_scalar_is_measure R.
pose GP := @measure_continuous_part R [the topologicalType of real_line_metric R] psip (@lebesgue_scalar_measure R).
pose GM := @measure_continuous_part R [the topologicalType of real_line_metric R] psim (@lebesgue_scalar_measure R).
have hGP := @measure_continuous_part_is_measure R [the topologicalType of real_line_metric R]
  psip (@lebesgue_scalar_measure R) hmL hmP.
have hGM := @measure_continuous_part_is_measure R [the topologicalType of real_line_metric R]
  psim (@lebesgue_scalar_measure R) hmL hmM.
have hGPa := @scalar_continuous_part_singleton_null R psip a hmP.
have hGPb := @scalar_continuous_part_singleton_null R psip b hmP.
have hGMa := @scalar_continuous_part_singleton_null R psim a hmM.
have hGMb := @scalar_continuous_part_singleton_null R psim b hmM.
change (is_true (GP `[a,b]+GM `[a,b]<=
  curve_variation (g : R -> real_line_metric R) a b)).
rewrite (@measure_segment_open_interval R GP a b hGP hGPa hGPb)
  (@measure_segment_open_interval R GM a b hGM hGMa hGMb).
have hPdom := @measure_continuous_part_le R [the topologicalType of real_line_metric R]
  psip (@lebesgue_scalar_measure R) hmL (derivation_measure_borel_regular hCP) `]a,b[.
have hMdom := @measure_continuous_part_le R [the topologicalType of real_line_metric R]
  psim (@lebesgue_scalar_measure R) hmL (derivation_measure_borel_regular hCM) `]a,b[.
apply: le_trans (leeD hPdom hMdom) _.
have [_ [_ [_ [_ [_ [_ [_ [_ [_ [hOpen _]]]]]]]]]] :=
  @induced_measure_pair_laws R g hg psip psim hp.
have hb := hOpen a b hab.
have hVfin := @curve_variation_fin_num R [the metricType R of real_line_metric R] g hg a b hab.
by move: hb; rewrite /total_variation (fineK hVfin).
Qed.

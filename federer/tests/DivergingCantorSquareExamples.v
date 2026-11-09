(** Federer (1969), 3.3.21, p. 309: concrete original diverging-schedule regression examples. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric EuclideanRealPlane EuclideanCantorProduct MetricCartesianProductUP
  ScheduledPowerCantorSetSealed ScheduledPowerCantorSetUP DivergingCantorScheduleUP DivergingCantorSquareExample
  ScheduledCriticalOrdinaryDensity EqualCostFirstEndpoint RealMetricDensities RealHausdorffMeasure HausdorffMeasure
  MetricDensities MeasureRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ordinary_diverging_cantor_schedule]: the actual
    schedule n_j=j+2 is an explicit admissible original witness for
    the construction in 3.3.21, p. 309. *)
Definition ordinary_diverging_cantor_schedule (j:nat):nat:=(j+2)%N.

(** Source for [ordinary_diverging_cantor_schedule_laws]: the actual
    schedule has all n_j>= 2 and tends to infinity as required in
    3.3.21, p. 309. No faster growth is needed. *)
Lemma ordinary_diverging_cantor_schedule_laws:
  (forall j,(2<=ordinary_diverging_cantor_schedule j)%N) /\
  cantor_schedule_tends_infinity ordinary_diverging_cantor_schedule.
Proof.
split;first by move=>j;rewrite /ordinary_diverging_cantor_schedule leq_addl.
move=>N;exists N=>j hNj.
exact:(leq_trans hNj (leq_addr 2 j)).
Qed.

(** Source for [oscillating_diverging_cantor_schedule]: an actual
    nonmonotone original schedule is allowed by 3.3.21, p. 309.
    It is j+2 at odd j and 2j+4 at even j. *)
Definition oscillating_diverging_cantor_schedule (j:nat):nat:=
  if odd j then (j+2)%N else (2*j+4)%N.

(** Source for [oscillating_diverging_cantor_schedule_laws]: this
    actual original schedule tends to infinity and has n_0= 4>3=n_1,
    testing the absence of a monotonicity assumption in 3.3.21, p. 309. *)
Lemma oscillating_diverging_cantor_schedule_laws:
  (forall j,(2<=oscillating_diverging_cantor_schedule j)%N) /\
  cantor_schedule_tends_infinity oscillating_diverging_cantor_schedule /\
  (oscillating_diverging_cantor_schedule 1<oscillating_diverging_cantor_schedule 0)%N.
Proof.
have hLower j:(j+2<=oscillating_diverging_cantor_schedule j)%N.
  rewrite /oscillating_diverging_cantor_schedule;case:ifP=>_;first exact:leqnn.
  have hJ:(j<= 2*j)%N by rewrite mul2n -addnn;exact:leq_addr.
  apply:leq_add;[exact:hJ|by []].
split.
- move=>j;exact:leq_trans (leq_addl j 2) (hLower j).
split;last by [].
move=>N;exists N=>j hNj;exact:leq_trans (leq_trans hNj (leq_addr 2 j)) (hLower j).
Qed.

(** Source for [diverging_square_actual_critical_positive_mass_zero_density]:
    actual original n_j=j+2 at m= 1/2 has positive finite ordinary
    H1 and lower one-density zero at the original zero corner,
    3.3.21, p. 309. Actual corner membership is retained. *)
Example diverging_square_actual_critical_positive_mass_zero_density (R:realType)
    (hm:0<(1/2:R)) (hm1:(1/2:R)<1):
  let n:=ordinary_diverging_cantor_schedule in
  let hn:=ordinary_diverging_cantor_schedule_laws.1 in
  let A:=@ScheduledPowerCantor.value R (1/2:R) hm hm1 n hn in
  let E:=euclidean_cantor_product A A in
  let H1:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1 in
  E (@euclidean_real_plane_pair R 0 0) /\(0<H1 E< +oo)%E /\
    lower_metric_density 1 (measure_restrict H1 E) (@euclidean_real_plane_pair R 0 0)= 0%E.
Proof.
move=>n hn A E H1.
have [f hPair]:=@ScheduledPowerCantor.laws R (1/2:R) hm hm1 n hn.
have hEndpoint:=power_cantor_original_zero_endpoint hPair.
have [hMass hDensity]:=@scheduled_critical_square_ordinary_density_zero R 1 n A f ltr01 hn
  ordinary_diverging_cantor_schedule_laws.2 hPair.
split.
- split;rewrite ?(MetricCartesianProductUP.metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
    ?(MetricCartesianProductUP.metric_product_second_pair (@euclidean_real_plane_is_metric_product R));exact:hEndpoint.
- split;[exact:hMass|exact:hDensity _].
Qed.

(** Source for [diverging_square_actual_noninteger_oscillating_schedule]:
    actual m= 3/4 and the explicit nonmonotone original schedule
    give positive finite H^(3/2) and vanishing original lower
    real-degree density at every centre, 3.3.21, p. 309. *)
Example diverging_square_actual_noninteger_oscillating_schedule (R:realType)
    (hm:0<(3/4:R)) (hm1:(3/4:R)<1) (hp:0<= 2 * (3/4:R)):
  let n:=oscillating_diverging_cantor_schedule in
  let hn:=oscillating_diverging_cantor_schedule_laws.1 in
  let A:=@ScheduledPowerCantor.value R (3/4:R) hm hm1 n hn in
  let E:=euclidean_cantor_product A A in
  let mu:=@real_hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) (2 * (3/4:R)) hp in
  (0<mu E< +oo)%E /\forall a:inner_metric_space (@euclidean_inner_productP R 2),
    lower_real_metric_density hp (measure_restrict mu E) a= 0%E.
Proof.
move=>n hn A E mu.
have h:=@federer_3_3_21 R (3/4:R) hm hm1 hp n hn oscillating_diverging_cantor_schedule_laws.2.1.
split;[exact:h.2.1|exact:h.2.2.1].
Qed.

(** Source for [diverging_square_actual_subcritical_degree]: actual
    m= 1/3 also has positive finite H^(2/3) and vanishing lower
    density, showing that the full 0<m<1 range of 3.3.21,
    p. 309, is retained below the preceding example's threshold. *)
Example diverging_square_actual_subcritical_degree (R:realType)
    (hm:0<(1/3:R)) (hm1:(1/3:R)<1) (hp:0<= 2 * (1/3:R)):
  let n:=ordinary_diverging_cantor_schedule in
  let hn:=ordinary_diverging_cantor_schedule_laws.1 in
  let A:=@ScheduledPowerCantor.value R (1/3:R) hm hm1 n hn in
  let E:=euclidean_cantor_product A A in
  let mu:=@real_hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) (2 * (1/3:R)) hp in
  (0<mu E< +oo)%E /\forall a:inner_metric_space (@euclidean_inner_productP R 2),
    lower_real_metric_density hp (measure_restrict mu E) a= 0%E.
Proof.
move=>n hn A E mu.
have h:=@federer_3_3_21 R (1/3:R) hm hm1 hp n hn ordinary_diverging_cantor_schedule_laws.2.
split;[exact:h.2.1|exact:h.2.2.1].
Qed.

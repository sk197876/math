(** Federer (1969), 2.10.29, p. 194: use the product of the two real power
    measures restricted to the Cantor factors. Its total mass is c^2, and
    its interval rectangle bounds are those of the two factors. This file
    uses only the sealed power and product measures. It introduces no
    assumption about the desired mixed-product measure. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge MetricDiameter MetricDiameterReal
  RealPower MeasureUP MeasureBasic MeasureRestriction MeasurePushforward ProductMeasure
  MetricCartesianProductUP MetricCartesianRectangleBounds MetricRealPowerMeasure
  MetricRealPowerClosedCovers MetricRealPowerIntervalAgreement BorelRegularMeasureUP TopologicalBorel
  PowerCantorPairUP PowerCantorPair PowerCantorIntervalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [power_cantor_restricted_measure]: supporting
    restriction of the actual real power measure
    to a Cantor factor in 2.10.29, p. 194.
    The definition also makes sense for arbitrary sets. *)
Definition power_cantor_restricted_measure (R : realType) (c m : R) (A : set (real_line_metric R)) :=
  measure_restrict (@metric_real_power_measure R [the metricType R of real_line_metric R] c m) A.

(** Source for [power_cantor_restricted_is_measure]: supporting
    restriction measure law for 2.10.29, p. 194,
    using 2.1.2, p. 54. No measurability
    assumption is needed on the restricting set. *)
Lemma power_cantor_restricted_is_measure (R : realType) (c m : R) (A : set (real_line_metric R)) :
  (0<=c)%R -> is_measure (power_cantor_restricted_measure c m A).
Proof. move=> hc; exact: measure_restrict_is_measure (metric_real_power_measure_is_measure _ _ hc) A. Qed.

(** Source for [power_cantor_restricted_interval_measurable]: supporting
    measurable rectangles in 2.10.29, p. 194.
    Compact intervals are closed, hence measurable
    for the Borel regular power measure and
    each of its restrictions. *)
Lemma power_cantor_restricted_interval_measurable (R : realType) (c m : R)
    (A : set (real_line_metric R)) (T : compact_real_intervals R) :
  (0<=c)%R -> measure_measurable (power_cantor_restricted_measure c m A) (val T).
Proof.
move=> hc; apply: measure_restrict_measurable.
apply: (borel_regular_borel_measurable
  (@metric_real_power_measure_is_measure R [the metricType R of real_line_metric R] c m hc)
  (@metric_real_power_measure_borel_regular R [the metricType R of real_line_metric R] c m hc)).
apply: closed_borel_set; exact: compact_real_interval_closed (set_valP T).
Qed.

(** Source for [power_cantor_product_measure]: supporting
    competing product measure in 2.10.29, p. 194,
    with positive coefficient c explicit. Its
    two factor measures are actual restrictions. *)
Definition power_cantor_product_measure (R : realType) (P : metricType R)
    (pair : real_line_metric R -> real_line_metric R -> P) (c m : R) (hc : (0<=c)%R)
    (A B : set (real_line_metric R)) :=
  paired_product_measure pair (@power_cantor_restricted_is_measure R c m A hc)
    (@power_cantor_restricted_is_measure R c m B hc).

(** Source for [power_cantor_product_is_measure]: supporting
    measure law for the actual competing product
    in 2.10.29, p. 194. *)
Lemma power_cantor_product_is_measure (R : realType) (P : metricType R)
    (pair : real_line_metric R -> real_line_metric R -> P) (c m : R) (hc : (0<=c)%R) A B :
  is_measure (@power_cantor_product_measure R P pair c m hc A B).
Proof. exact: paired_product_is_measure. Qed.

(** Source for [power_cantor_product_rectangle_bound]: direct
    reduction to the two factor interval masses
    in 2.10.29, p. 194. The test set
    need not be measurable. *)
Lemma power_cantor_product_rectangle_bound (R : realType) (P : metricType R)
    (pair : real_line_metric R -> real_line_metric R -> P)
    (first second : P -> real_line_metric R)
    (hp : is_metric_cartesian_product pair first second)
    (c m : R) (hc : (0<=c)%R) A B (S : set P) (U V : compact_real_intervals R) :
  (forall p, S p -> val U (first p) /\ val V (second p)) ->
  @power_cantor_product_measure R P pair c m hc A B S<=
    @metric_real_power_measure R [the metricType R of real_line_metric R] c m (A `&` val U)*
    @metric_real_power_measure R [the metricType R of real_line_metric R] c m (B `&` val V).
Proof.
move=> hS; exact (@paired_product_rectangle_bound R P [the metricType R of real_line_metric R]
  [the metricType R of real_line_metric R] pair first second hp _ _
  (@power_cantor_restricted_is_measure R c m A hc) (@power_cantor_restricted_is_measure R c m B hc)
  S (val U) (val V) (@power_cantor_restricted_interval_measurable R c m A U hc)
  (@power_cantor_restricted_interval_measurable R c m B V hc) hS).
Qed.

(** Source for [power_cantor_product_total_mass]: direct
    positive product mass in 2.10.29, p. 194,
    for two actual Cantor pairs. Since this
    measure is already restricted in each factor,
    the total mass is c^2. *)
Lemma power_cantor_product_total_mass (R : realType) (P : metricType R)
    (pair : real_line_metric R -> real_line_metric R -> P)
    (c m : R) (hc : (0<=c)%R) n l A B f g :
  (0<c)%R -> (0<m)%R -> (m<1)%R ->
  is_power_cantor_pair c m n A f -> is_power_cantor_pair c m l B g ->
  @power_cantor_product_measure R P pair c m hc A B setT=(c*c)%R%:E.
Proof.
move=> hcp hm hm1 hA hB.
rewrite /power_cantor_product_measure paired_product_whole_value
  /power_cantor_restricted_measure /measure_restrict !setIT.
by rewrite (power_cantor_pair_real_power_mass hcp hm hm1 hA).1
  (power_cantor_pair_real_power_mass hcp hm hm1 hB).1 -EFinM.
Qed.

(** Source for [power_cantor_product_cantor_mass]: direct
    positive mass of the Cantor product itself
    in 2.10.29, p. 194. Compactness makes
    both factors measurable; restriction leaves
    their mass c unchanged. *)
Lemma power_cantor_product_cantor_mass (R : realType) (P : metricType R)
    (pair : real_line_metric R -> real_line_metric R -> P)
    (first second : P -> real_line_metric R)
    (hp : is_metric_cartesian_product pair first second)
    (c m : R) (hc : (0<=c)%R) n l A B f g :
  (0<c)%R -> (0<m)%R -> (m<1)%R ->
  is_power_cantor_pair c m n A f -> is_power_cantor_pair c m l B g ->
  @power_cantor_product_measure R P pair c m hc A B
    [set p | A (first p) /\ B (second p)]=(c*c)%R%:E.
Proof.
move=> hcp hm hm1 hA hB.
have hmeas C v hC : is_power_cantor_pair c m v C hC ->
    measure_measurable (power_cantor_restricted_measure c m C) C.
  move=> hpair; apply: measure_restrict_measurable.
  apply: (borel_regular_borel_measurable
    (@metric_real_power_measure_is_measure R [the metricType R of real_line_metric R] c m hc)
    (@metric_real_power_measure_borel_regular R [the metricType R of real_line_metric R] c m hc)).
  apply: closed_borel_set.
  exact: compact_closed (@metric_hausdorff R [the metricType R of real_line_metric R])
    (power_cantor_pair_properties hcp hm hm1 hpair).1.
rewrite /power_cantor_product_measure
  (@paired_product_coordinate_rectangle_value R P [the metricType R of real_line_metric R]
    [the metricType R of real_line_metric R] pair first second hp _ _
    (@power_cantor_restricted_is_measure R c m A hc) (@power_cantor_restricted_is_measure R c m B hc)
    A B (hmeas A n f hA) (hmeas B l g hB))
  /power_cantor_restricted_measure /measure_restrict !setIid.
by rewrite (power_cantor_pair_real_power_mass hcp hm hm1 hA).1
  (power_cantor_pair_real_power_mass hcp hm hm1 hB).1 -EFinM.
Qed.

(** Source for [power_cantor_product_zero_diameter]: supporting
    diameter-zero case of the local bound in
    2.10.29, p. 194. Both projections lie
    in degenerate intervals; the positive exponent
    makes their factor masses zero. *)
Lemma power_cantor_product_zero_diameter (R : realType) (P : metricType R)
    (pair : real_line_metric R -> real_line_metric R -> P)
    (first second : P -> real_line_metric R)
    (hp : is_metric_cartesian_product pair first second)
    (c m : R) (hc : (0<=c)%R) n l A B f g :
  (0<c)%R -> (0<m)%R -> (m<1)%R ->
  is_power_cantor_pair c m n A f -> is_power_cantor_pair c m l B g ->
  forall S : set P, extended_metric_diameter S=0 ->
    @power_cantor_product_measure R P pair c m hc A B S=0.
Proof.
move=> hcp hm hm1 hA hB S hdiam.
have hnu := @power_cantor_product_is_measure R P pair c m hc A B.
have [hS0|hS] := eqVneq S set0; first by rewrite hS0 (measure_empty hnu).
have hSne : S !=set0 by apply/set0P.
have hsize : extended_metric_diameter S<=0%R%:E by rewrite hdiam.
have [U [V [hU [hV hcover]]]] := @metric_cartesian_real_rectangle_hull R P pair first second hp S 0 hSne (lexx 0%R) hsize.
have hrect := @power_cantor_product_rectangle_bound R P pair first second hp c m hc A B S U V hcover.
have hleft := @power_cantor_pair_interval_bound R c m n A f hcp hm hm1 hA U.
have hright := @power_cantor_pair_interval_bound R c m l B g hcp hm hm1 hB V.
rewrite hU real_power_zero_base ?gt_eqF // mulr0 in hleft.
rewrite hV real_power_zero_base ?gt_eqF // mulr0 in hright.
have hleft0 : @metric_real_power_measure R [the metricType R of real_line_metric R] c m (A `&` val U)=0.
  apply/eqP; rewrite eq_le hleft; exact: measure_nonnegative (metric_real_power_measure_is_measure _ _ hc) _.
rewrite hleft0 mul0e in hrect; apply/eqP; rewrite eq_le hrect.
exact: measure_nonnegative hnu _.
Qed.

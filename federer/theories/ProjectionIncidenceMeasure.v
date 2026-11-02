(** Supporting incidence measure for Federer (1969), 2.10.5, pp. 172–173,
    and its Borel projection-null characterization. Compose the actual
    product outer measure L^m times theta-star with the incidence-set
    operation. Countable covers of source sets give countable covers of
    their incidences, so this is an outer measure on the source. For Suslin
    S, Fubini identifies its value with the actual integral of f_S, hence
    with beta_1 zeta_1(S). This auxiliary outer measure is a supporting
    proof object, not an additional named measure attributed to Federer. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionMetric
  EuclideanLebesgueDimensions OrthogonalProjectionProbability ProjectedVolumeIncidence
  ProjectedVolumeMeasurability MeasureUP MeasureBasic MeasureSplit MeasureIndexedCover
  ProductMeasure ProductSections ProductSetFubini PartialFunctionBasic MeasureIntegralUP
  CountablyMeasurableUP CountablyMeasurableBasic CountablyMeasurableProduct CountablyMeasurableSubsets
  SuslinSetUP BorelClosedProjection BorelCoverCostUP IntegralGeometricGauge IntegralGeometricMeasure
  ProjectionBeta NonnegativeExtendedExponentNormUP ExtendedPositivePower
  MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleWeightedBound CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projected_incidence_measure]: supporting
    actual product measure of {(y,p):y in p(S)}
    for Federer 2.10.5, pp. 172–173. The
    outer measure is defined on all source sets,
    without a measurability premise on S. *)
Definition projected_incidence_measure (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :=
  product_measure (euclidean_lebesgue_is_measure R m) (@theta_star_is_measure R n m hmn)
    (projection_incidence (m:=m) S).

(** Source for [projected_incidence_is_measure]: supporting
    outer-measure law for the incidence operation
    in Federer 2.10.5, pp. 172–173, used
    to pass the exponent-one generator bound
    to the Caratheodory measure on arbitrary targets. *)
Theorem projected_incidence_is_measure (R : realType) (n m : nat) (hmn : (m<=n)%N) :
  is_measure (@projected_incidence_measure R n m hmn).
Proof.
have hp := product_measure_is_measure (euclidean_lebesgue_is_measure R m) (@theta_star_is_measure R n m hmn).
constructor; first by move=> A; exact: measure_nonnegative hp _.
move=> A D hD hcover.
apply: (measure_indexed_cover hp hD)=> z [x [hx he]].
have [B hB hxB] := hcover x hx.
exists B=> //; exists x; by split.
Qed.

(** Source for [projected_volume_incidence_integral]:
    direct Fubini integral identity underlying the
    measurability argument in Federer 2.10.5,
    p. 172, from 2.6.2(3), pp. 115–117.
    Suslin S can be unbounded and the actual
    integral and incidence measure can be infinite. *)
Theorem projected_volume_incidence_integral (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_suslin_set R S -> is_measure_integral (@orthogonal_projection_probability R n m hmn)
    (partial_function_total (projected_volume_function (m:=m) S))
    (@projected_incidence_measure R n m hmn S).
Proof.
move=> hS.
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose P := orthogonal_projection_metric_space R n m.
pose theta := @orthogonal_projection_probability R n m hmn.
pose hm := euclidean_lebesgue_is_measure R m.
pose ht := @theta_star_is_measure R n m hmn.
have hwhole : measure_countably_measurable (product_measure hm ht) setT.
  apply: product_whole_countably_measurable; first exact: euclidean_lebesgue_countably_measurable.
  apply: finite_measurable_set_countably_measurable; first exact: measure_measurable_whole ht.
  by rewrite theta_star_total ltry.
have hinc := @projection_incidence_product_measurable R n m theta ht S
  (@theta_star_borel_regular R n m hmn) hS.
have hcount := @measurable_subset_countably_measurable R (Y*P)%type
  (product_measure hm ht) (product_measure_is_measure hm ht)
  (projection_incidence (m:=m) S) setT hinc (fun _ _ => I) hwhole.
have hi := (@product_set_fubini R Y P (@euclidean_lebesgue_measure R m)
  theta hm ht (projection_incidence (m:=m) S) hcount).2.2.2.
have he : (fun p => euclidean_lebesgue_measure m
    (product_horizontal_section (projection_incidence (m:=m) S) p)) = projected_volume_function S.
  apply: funext=> p; rewrite /product_horizontal_section projection_incidence_horizontal_section; by [].
by rewrite he in hi.
Qed.

(** Source for [integral_geometric_one_gauge_incidence]:
    supporting equality of beta_1 zeta_1(S)
    with the incidence measure for the zero-set
    assertion in Federer 2.10.5, p. 173.
    The norm at exponent one is the integral
    of the actual nonnegative extended f_S. *)
Lemma integral_geometric_one_gauge_incidence (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_suslin_set R S ->
  (@projection_beta R n m hmn 1)%:E * @integral_geometric_gauge R n m hmn 1 S =
    @projected_incidence_measure R n m hmn S.
Proof.
move=> hS.
pose theta := @orthogonal_projection_probability R n m hmn.
pose f := projected_volume_function (m:=m) S.
pose v := @projected_incidence_measure R n m hmn S.
have hi := @projected_volume_incidence_integral R n m hmn S hS.
have hv : 0<=v := measure_nonnegative (@projected_incidence_is_measure R n m hmn) S.
have hn := @integral_geometric_gauge_norm_specification R n m hmn 1 (lexx 1) S hS.
apply: (nonnegative_extended_exponent_norm_unique hn).
split; first exact: lexx.
exists v; split.
- have he : (fun p => extended_positive_power (f p) 1%R)=f.
    apply: funext=> p; exact: extended_positive_power_one (projected_volume_function_nonnegative S p).
  rewrite he; exact hi.
- by rewrite invr1 (@extended_positive_power_one R v hv).
Qed.

(** Source for [projected_incidence_integral_geometric_bound]:
    supporting bound of the incidence outer
    measure by beta_1 I_1 for Federer 2.10.5,
    p. 173. Compare the actual exponent-one
    costs at one positive cutoff, then use the
    Caratheodory supremum. The target is arbitrary. *)
Theorem projected_incidence_integral_geometric_bound (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @projected_incidence_measure R n m hmn A <=
    (@projection_beta R n m hmn 1)%:E * @integral_geometric_measure R n m hmn 1 A.
Proof.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose J := @borel_metric_sets R E.
pose S (j : J) := val j.
pose c (j : J) := @integral_geometric_gauge R n m hmn 1 (S j).
pose eta := metric_scale_envelope S c 1.
have heta := @metric_scale_envelope_specification R E J S c 1.
have hb := @projection_beta_positive R n m hmn 1 (lexx 1).
have hbound : @projected_incidence_measure R n m hmn A<=(@projection_beta R n m hmn 1)%:E*eta A.
  apply: (@measure_bounded_by_scaled_metric_envelope R E J S c 1 eta
    (@projected_incidence_measure R n m hmn) (@projection_beta R n m hmn 1)
    heta (@projected_incidence_is_measure R n m hmn) hb)=> j _.
  have hS := @metric_borel_suslin R E (S j) (set_valP j).
  by rewrite -(@integral_geometric_one_gauge_incidence R n m hmn (S j) hS).
apply: le_trans hbound _; apply: lee_wpmul2l; first by rewrite lee_fin; exact: ltW hb.
exact: (@caratheodory_limit_upper R E J S c (@integral_geometric_measure R n m hmn 1)
  (@integral_geometric_measure_specification R n m hmn 1) A 1 eta lte01 heta).
Qed.
